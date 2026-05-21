"""Convert ModSecurity (PCRE) regex patterns to ECMA2020.

ModSecurity rules use a PCRE dialect; the SMT-LIB2 ``re.from_ecma2020``
function expects ECMA2020 syntax.  This module performs a best-effort,
source-level translation of the constructs that commonly appear in OWASP CRS
and similar rule sets.

Conversions applied (in order):
  1. Inline flag groups ``(?flags)`` → expanded in-place:
       ``i`` (case-insensitive) — each letter is replaced by a two-element
           character class, e.g. ``a`` → ``[aA]``, ``[a-z]`` → ``[a-zA-Z]``.
       ``m`` / ``s`` — no syntactic change needed (ECMA2020 supports these as
           flags, but since ``re.from_ecma2020_flags`` is not available we
           leave them implicit; the solver sees the pattern without the flag,
           which may affect ``^``/``$`` and ``.`` semantics).
       ``x`` (verbose) — raises ``UnsupportedPatternError``.
  2. Named capture groups ``(?P<name>…)`` → ``(?<name>…)``.
  3. Wide hex escapes ``\\x{HHHH}`` → ``\\u{HHHH}``.
  4. POSIX bracket expressions ``[[:class:]]`` → equivalent ECMA2020 ranges.
  5. Atomic groups ``(?>…)`` → ``(?:…)`` (semantics approximated; warning).
  6. Possessive quantifiers ``*+``, ``++``, ``?+``, ``{n}+`` → greedy
     equivalents (semantics approximated; warning).
  7. ``\\Q…\\E`` literal-escape blocks → each character individually escaped.
  8. Inline comments ``(?#…)`` → removed.
  9. ``\\A`` → ``^``, ``\\Z`` / ``\\z`` → ``$``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field


# ---------------------------------------------------------------------------
# POSIX character-class table
# ---------------------------------------------------------------------------

_POSIX: dict[str, str] = {
    "alpha":  "a-zA-Z",
    "digit":  "0-9",
    "alnum":  "a-zA-Z0-9",
    "lower":  "a-z",
    "upper":  "A-Z",
    "space":  r" \t\r\n\f\v",
    "blank":  r" \t",
    "punct":  r"""!"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~""",
    "print":  r"\x20-\x7e",
    "graph":  r"\x21-\x7e",
    "cntrl":  r"\x00-\x1f\x7f",
    "xdigit": "0-9a-fA-F",
    "word":   r"a-zA-Z0-9_",
    "ascii":  r"\x00-\x7f",
}

_SUPPORTED_FLAGS = frozenset("ims")


# ---------------------------------------------------------------------------
# Public types
# ---------------------------------------------------------------------------

@dataclass
class ConversionResult:
    """Result of converting a PCRE pattern to ECMA2020."""
    pattern: str
    warnings: list[str] = field(default_factory=list)


class UnsupportedPatternError(Exception):
    """Raised for PCRE constructs that cannot be safely converted."""


# ---------------------------------------------------------------------------
# Case-insensitive expansion
# ---------------------------------------------------------------------------

def _escape_span(s: str, i: int) -> int:
    """Return the number of characters consumed by the escape sequence at *s[i]*.

    *i* must point to the leading backslash.  Handles ``\\xHH``, ``\\uHHHH``,
    ``\\u{…}``, ``\\UHHHHHHHH``; falls back to 2 for all other sequences.
    """
    if i + 1 >= len(s):
        return 1
    nc = s[i + 1]
    if nc in 'xX':
        return 4           # \xHH
    if nc == 'u':
        if i + 2 < len(s) and s[i + 2] == '{':
            j = i + 3
            while j < len(s) and s[j] != '}':
                j += 1
            return j - i + 1   # \u{…}
        return 6               # \uHHHH
    if nc == 'U':
        return 10              # \UHHHHHHHH
    return 2                   # \c — single escaped char


def _ci_expand_class(inner: str) -> str:
    """Add the opposite-case version of every letter/range inside a character
    class body (the text between ``[``/``[^`` and the closing ``]``).

    Examples::

        "a-z"  → "a-zA-Z"
        "abc"  → "abcABC"
        "0-9"  → "0-9"          (digits unchanged)
        "a-f"  → "a-fA-F"
        "\\\\x5c/"  → "\\\\x5c/"     (hex escape — not a letter, unchanged)
    """
    additions: list[str] = []
    i = 0
    n = len(inner)

    while i < n:
        c = inner[i]

        if c == '\\':
            # Skip the full escape sequence — never expand escape-encoded chars.
            i += _escape_span(inner, i)
            continue

        # Range x-y
        if (i + 2 < n
                and inner[i + 1] == '-'
                and inner[i + 2] not in (']', '')):
            d = inner[i + 2]
            if (c.isascii() and c.isalpha()
                    and d.isascii() and d.isalpha()
                    and c.islower() == d.islower()):
                c2, d2 = c.swapcase(), d.swapcase()
                swapped = f'{c2}-{d2}'
                if swapped not in inner and swapped not in ''.join(additions):
                    additions.append(swapped)
            i += 3
            continue

        if c.isascii() and c.isalpha():
            other = c.swapcase()
            if other not in inner and other not in ''.join(additions):
                additions.append(other)

        i += 1

    return inner + ''.join(additions)


def _make_case_insensitive(pattern: str) -> str:
    """Rewrite *pattern* so that every letter matches both cases.

    Operates character-by-character with a simple state machine that tracks
    whether the current position is inside a character class.  Escape
    sequences are passed through verbatim.

    * Outside a character class: ``a`` → ``[aA]``
    * Inside a character class:  ``[abc]`` → ``[abcABC]``,
                                  ``[a-z]`` → ``[a-zA-Z]``
    """
    out: list[str] = []
    i = 0
    n = len(pattern)

    while i < n:
        c = pattern[i]

        # ── Escape sequence ────────────────────────────────────────────────
        if c == '\\':
            span = _escape_span(pattern, i)
            out.append(pattern[i:i + span])
            i += span
            continue

        # ── Character class ────────────────────────────────────────────────
        if c == '[':
            # Collect the full character class span.
            j = i + 1
            class_prefix = '['          # '[' or '[^'

            if j < n and pattern[j] == '^':
                class_prefix = '[^'
                j += 1

            # A ']' immediately after '[' or '[^' is treated as a literal ']'.
            if j < n and pattern[j] == ']':
                j += 1

            # Advance to the closing ']'.
            while j < n:
                if pattern[j] == '\\':
                    j += 2
                    continue
                if pattern[j] == ']':
                    j += 1
                    break
                j += 1

            raw_class = pattern[i:j]
            # Extract inner content (between prefix and closing ']')
            inner = raw_class[len(class_prefix):-1]
            expanded_inner = _ci_expand_class(inner)
            out.append(class_prefix + expanded_inner + ']')
            i = j
            continue

        # ── Plain letter outside a class ───────────────────────────────────
        if c.isascii() and c.isalpha():
            other = c.swapcase()
            out.append(f'[{c}{other}]')
            i += 1
            continue

        out.append(c)
        i += 1

    return ''.join(out)


# ---------------------------------------------------------------------------
# Remaining conversion helpers
# ---------------------------------------------------------------------------

def _extract_inline_flags(pattern: str, warnings: list[str]) -> tuple[str, str]:
    """Remove standalone ``(?flags)`` groups and return ``(new_pattern, flags)``."""
    flags: set[str] = set()

    def _replace(m: re.Match) -> str:  # type: ignore[type-arg]
        flag_chars = m.group(1)
        if flag_chars.startswith("-"):
            warnings.append(
                f"flag removal '(?{flag_chars})' has no ECMA2020 equivalent — left as-is"
            )
            return m.group(0)
        unsupported = [ch for ch in flag_chars if ch not in _SUPPORTED_FLAGS]
        if unsupported:
            raise UnsupportedPatternError(
                f"PCRE inline flag(s) {''.join(unsupported)!r} have no ECMA2020 equivalent"
            )
        flags.update(flag_chars)
        return ""

    converted = re.sub(r"\(\?([a-zA-Z]+)\)", _replace, pattern)

    if re.search(r"\(\?[a-zA-Z]+:", converted):
        warnings.append(
            "scoped inline flags '(?flags:…)' are not supported in ECMA2020 — "
            "pattern left as-is; results may be incorrect"
        )

    return converted, "".join(sorted(flags))


def _convert_posix_classes(pattern: str, warnings: list[str]) -> str:
    def _replace_posix(m: re.Match) -> str:  # type: ignore[type-arg]
        name = m.group(1)
        replacement = _POSIX.get(name)
        if replacement is None:
            warnings.append(f"unknown POSIX class '[:{name}:]' — left as-is")
            return m.group(0)
        return replacement

    return re.sub(r"\[:([a-z]+):\]", _replace_posix, pattern)


def _convert_quoted_blocks(pattern: str) -> str:
    def _escape_literal(m: re.Match) -> str:  # type: ignore[type-arg]
        return re.escape(m.group(1))

    return re.sub(r"\\Q(.*?)\\E", _escape_literal, pattern, flags=re.DOTALL)


def _convert_atomic_groups(pattern: str, warnings: list[str]) -> str:
    if re.search(r"\(\?>", pattern):
        warnings.append(
            "atomic group '(?>…)' has no ECMA2020 equivalent — "
            "converted to '(?:…)'; possessive semantics are lost"
        )
        pattern = re.sub(r"\(\?>", "(?:", pattern)
    return pattern


def _convert_possessive_quantifiers(pattern: str, warnings: list[str]) -> str:
    if re.search(r"(?<=[*+?}])\+", pattern):
        warnings.append(
            "possessive quantifier (e.g. '*+') has no ECMA2020 equivalent — "
            "converted to greedy; backtracking semantics may differ"
        )
        pattern = re.sub(r"([*+?}])\+", r"\1", pattern)
    return pattern


def _convert_anchors(pattern: str) -> str:
    pattern = re.sub(r"\\A", "^", pattern)
    pattern = re.sub(r"\\[Zz]", "$", pattern)
    return pattern


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def pcre_to_ecma2020(pattern: str) -> ConversionResult:
    """Convert a ModSecurity (PCRE) regex *pattern* to an ECMA2020 pattern.

    Returns a :class:`ConversionResult` with:

    * ``pattern``  – converted pattern string for ``re.from_ecma2020``.
    * ``warnings`` – list of human-readable conversion notes.

    Raises :class:`UnsupportedPatternError` for PCRE constructs that cannot
    be safely approximated (e.g. ``(?x)`` verbose mode).
    """
    warnings: list[str] = []

    # 1. Extract inline flags; expand (?i) in-place.
    pattern, flags = _extract_inline_flags(pattern, warnings)

    if 'i' in flags:
        pattern = _make_case_insensitive(pattern)

    if set(flags) - {'i'}:
        remaining = "".join(sorted(set(flags) - {'i'}))
        warnings.append(
            f"flag(s) '{remaining}' extracted but re.from_ecma2020_flags is unavailable — "
            "flag effect is not encoded; results may differ for multiline/dotAll patterns"
        )

    # 2. Named capture groups (?P<name>…) → (?<name>…)
    pattern = re.sub(r"\(\?P<([^>]+)>", r"(?<\1>", pattern)

    # 3. Wide hex escapes \x{HHHH} → \u{HHHH}
    pattern = re.sub(r"\\x\{([0-9a-fA-F]+)\}", r"\\u{\1}", pattern)

    # 4. POSIX bracket expressions
    pattern = _convert_posix_classes(pattern, warnings)

    # 5. Atomic groups
    pattern = _convert_atomic_groups(pattern, warnings)

    # 6. Possessive quantifiers
    pattern = _convert_possessive_quantifiers(pattern, warnings)

    # 7. \Q…\E literal blocks
    pattern = _convert_quoted_blocks(pattern)

    # 8. Inline comments (?#…)
    pattern = re.sub(r"\(\?#[^)]*\)", "", pattern)

    # 9. PCRE-only anchors
    pattern = _convert_anchors(pattern)

    return ConversionResult(pattern=pattern, warnings=warnings)
