"""Extract the set of Unicode codepoints relevant to a regex.

Parses a Python-flavoured regex with the internal :mod:`re._parser` module and
walks the resulting AST, collecting every codepoint the pattern can match:

* every literal character (``LITERAL``);
* every codepoint covered by a character-class ``RANGE`` (e.g. ``[a-c]``
  contributes ``97, 98, 99``);
* a handful of representative boundary codepoints for predefined classes
  such as ``\\d``, ``\\w``, ``\\s`` (used both standalone and inside a class),
  since these denote effectively unbounded/huge Unicode categories that
  cannot be enumerated exactly;
* for a *negated* class (``[^...]`` / ``NOT_LITERAL``), the full complement
  of its explicit contents over the whole Unicode range ``0x0-0x10FFFF`` —
  i.e. every codepoint that is *not* listed, since that is exactly what the
  negated class matches;
* under the ``IGNORECASE`` flag (``(?i)``, global or scoped via
  ``(?i:...)``), every literal/range codepoint also contributes its
  opposite-case counterpart, since that is what actually matches at runtime;
* ``.`` (``ANY``) contributes every Unicode codepoint except ``\\n`` (0x0A),
  or literally every codepoint (including ``\\n``) under the ``DOTALL`` flag
  (``(?s)``, global or scoped via ``(?s:...)``) — matching what ``.``
  actually matches at runtime;
* both branches of a conditional group (``(?(id)yes|no)`` / ``GROUPREF_EXISTS``)
  are walked, since either can execute depending on runtime match state.

Because predefined classes are only approximated by a handful of boundary
codepoints, :func:`extract_relevant_codepoints` is *not* safe for callers
that need a complete/exact set (e.g. to decide that some codepoint can never
matter and its handling may be dropped). Such callers should use
:func:`extract_relevant_codepoints_precise` instead, which returns ``None``
whenever the pattern uses a predefined class anywhere.
"""

from __future__ import annotations

try:
    import re._constants as _sre
    import re._parser as _sre_parse
except ImportError:  # Python < 3.11: internals live in top-level modules.
    import sre_constants as _sre
    import sre_parse as _sre_parse

__all__ = ["extract_relevant_codepoints", "extract_relevant_codepoints_precise"]

_UNICODE_MAX = 0x10FFFF  # highest valid Unicode codepoint (inclusive)

# Representative codepoints for predefined character classes. Each entry maps
# to a handful of boundary codepoints (endpoints of the underlying ranges)
# rather than a full enumeration, keeping the resulting alphabet finite.
_CATEGORY_CODEPOINTS: dict[int, tuple[int, ...]] = {
    _sre.CATEGORY_DIGIT: (0x30, 0x39),
    _sre.CATEGORY_NOT_DIGIT: (0x30, 0x39),
    _sre.CATEGORY_UNI_DIGIT: (0x30, 0x39),
    _sre.CATEGORY_UNI_NOT_DIGIT: (0x30, 0x39),
    _sre.CATEGORY_SPACE: (0x09, 0x0A, 0x0D, 0x20),
    _sre.CATEGORY_NOT_SPACE: (0x09, 0x0A, 0x0D, 0x20),
    _sre.CATEGORY_UNI_SPACE: (0x09, 0x0A, 0x0D, 0x20),
    _sre.CATEGORY_UNI_NOT_SPACE: (0x09, 0x0A, 0x0D, 0x20),
    _sre.CATEGORY_WORD: (0x30, 0x39, 0x41, 0x5A, 0x5F, 0x61, 0x7A),
    _sre.CATEGORY_NOT_WORD: (0x30, 0x39, 0x41, 0x5A, 0x5F, 0x61, 0x7A),
    _sre.CATEGORY_UNI_WORD: (0x30, 0x39, 0x41, 0x5A, 0x5F, 0x61, 0x7A),
    _sre.CATEGORY_UNI_NOT_WORD: (0x30, 0x39, 0x41, 0x5A, 0x5F, 0x61, 0x7A),
}

# Opcodes that carry a nested SubPattern (or list of SubPatterns) to recurse into.
_SUBPATTERN_OPS = {_sre.ASSERT, _sre.ASSERT_NOT, _sre.MAX_REPEAT, _sre.MIN_REPEAT}

# The full Unicode codepoint space, built lazily (only once a negated class is
# actually encountered) since it is ~1.1M entries.
_full_unicode_cache: set[int] | None = None


def _full_unicode() -> set[int]:
    global _full_unicode_cache
    if _full_unicode_cache is None:
        _full_unicode_cache = set(range(0, _UNICODE_MAX + 1))
    return _full_unicode_cache


def _case_variants(cp: int) -> set[int]:
    """Return *cp* plus its opposite-case codepoint(s), if any."""
    ch = chr(cp)
    variants = {cp}
    lower = ch.lower()
    upper = ch.upper()
    if len(lower) == 1:
        variants.add(ord(lower))
    if len(upper) == 1:
        variants.add(ord(upper))
    return variants


def extract_relevant_codepoints(pattern: str, flags: int = 0) -> set[int]:
    """Return the set of Unicode codepoints (as ints) relevant to *pattern*.

    See module docstring for exactly what is collected. Constructs with no
    fixed codepoint (anchors, backreferences) are ignored.
    """
    codepoints, _approximate = _extract(pattern, flags)
    return codepoints


def extract_relevant_codepoints_precise(
    pattern: str, flags: int = 0
) -> "set[int] | None":
    """Like :func:`extract_relevant_codepoints`, but ``None`` if imprecise.

    Predefined classes (``\\d``, ``\\w``, ``\\s`` and their negations, standalone
    or inside a character class) are only approximated by a handful of
    boundary codepoints — a real but out-of-set codepoint (e.g. ``'b'`` for
    ``\\w``) can still match the pattern. Callers that need a *complete* set
    (e.g. to conclude some codepoint can never affect the match) must treat
    that case as "unknown" rather than use the approximation, hence ``None``.
    """
    codepoints, approximate = _extract(pattern, flags)
    return None if approximate else codepoints


def _extract(pattern: str, flags: int) -> "tuple[set[int], bool]":
    codepoints: set[int] = set()
    approximate = [False]
    parsed = _sre_parse.parse(pattern, flags)
    ignorecase = bool(parsed.state.flags & _sre.SRE_FLAG_IGNORECASE)
    dotall = bool(parsed.state.flags & _sre.SRE_FLAG_DOTALL)
    _walk_subpattern(parsed, codepoints, ignorecase, dotall, approximate)
    return codepoints, approximate[0]


def _walk_subpattern(
    subpattern, codepoints: set[int], ignorecase: bool, dotall: bool, approximate: list
) -> None:
    for op, av in subpattern.data:
        _walk_node(op, av, codepoints, ignorecase, dotall, approximate)


def _walk_node(
    op, av, codepoints: set[int], ignorecase: bool, dotall: bool, approximate: list
) -> None:
    if op == _sre.LITERAL:
        codepoints.update(_case_variants(av) if ignorecase else {av})

    elif op == _sre.NOT_LITERAL:
        # `[^x]` compiled to the single-char shorthand: matches everything
        # except `x` (and, under IGNORECASE, `x`'s opposite case too).
        excluded = _case_variants(av) if ignorecase else {av}
        codepoints.update(_full_unicode() - excluded)

    elif op == _sre.CATEGORY:
        approximate[0] = True
        codepoints.update(_CATEGORY_CODEPOINTS.get(av, ()))

    elif op == _sre.ANY:
        # `.` — everything except newline, or literally everything under DOTALL.
        codepoints.update(
            _full_unicode() if dotall else _full_unicode() - {0x0A}
        )

    elif op == _sre.IN:
        explicit, negated = _expand_class_items(av, ignorecase, approximate)
        if negated:
            codepoints.update(_full_unicode() - explicit)
        else:
            codepoints.update(explicit)

    elif op == _sre.BRANCH:
        _, alternatives = av
        for alt in alternatives:
            _walk_subpattern(alt, codepoints, ignorecase, dotall, approximate)

    elif op == _sre.SUBPATTERN:
        # (group, add_flags, del_flags, subpattern) — add_flags/del_flags
        # encode scoped inline flags, e.g. the IGNORECASE/DOTALL bits set by
        # `(?i:…)` / `(?s:…)`.
        _, add_flags, del_flags, subpattern = av
        scoped_ignorecase = (
            (ignorecase or bool(add_flags & _sre.SRE_FLAG_IGNORECASE))
            and not bool(del_flags & _sre.SRE_FLAG_IGNORECASE)
        )
        scoped_dotall = (
            (dotall or bool(add_flags & _sre.SRE_FLAG_DOTALL))
            and not bool(del_flags & _sre.SRE_FLAG_DOTALL)
        )
        _walk_subpattern(
            subpattern, codepoints, scoped_ignorecase, scoped_dotall, approximate
        )

    elif op in _SUBPATTERN_OPS:
        # ASSERT/ASSERT_NOT: (direction, subpattern)
        # MAX_REPEAT/MIN_REPEAT: (min, max, subpattern)
        subpattern = av[-1]
        _walk_subpattern(subpattern, codepoints, ignorecase, dotall, approximate)

    elif op == _sre.GROUPREF_EXISTS:
        # (group, yes_subpattern, no_subpattern) — `(?(id)yes|no)`. Either
        # branch can execute depending on runtime match state, so both
        # contribute; `no_subpattern` is None when there is no "no" branch.
        _, yes_subpattern, no_subpattern = av
        _walk_subpattern(yes_subpattern, codepoints, ignorecase, dotall, approximate)
        if no_subpattern is not None:
            _walk_subpattern(no_subpattern, codepoints, ignorecase, dotall, approximate)

    # AT, GROUPREF and similar opcodes carry no fixed codepoint information
    # and are intentionally ignored.


def _expand_class_items(
    items, ignorecase: bool, approximate: list
) -> "tuple[set[int], bool]":
    """Expand the item list of an ``IN`` node (a character class body).

    Returns ``(explicit_codepoints, negated)`` where *explicit_codepoints* is
    every codepoint directly listed by the class (individual literals, full
    range expansions, and category boundary points — plus opposite-case
    counterparts under IGNORECASE) and *negated* is True if the class started
    with ``[^``.
    """
    explicit: set[int] = set()
    negated = False
    for item_op, item_av in items:
        if item_op == _sre.NEGATE:
            negated = True
        elif item_op == _sre.LITERAL:
            explicit.update(_case_variants(item_av) if ignorecase else {item_av})
        elif item_op == _sre.RANGE:
            lo, hi = item_av
            if ignorecase:
                for cp in range(lo, hi + 1):
                    explicit.update(_case_variants(cp))
            else:
                explicit.update(range(lo, hi + 1))
        elif item_op == _sre.CATEGORY:
            approximate[0] = True
            explicit.update(_CATEGORY_CODEPOINTS.get(item_av, ()))
    return explicit, negated
