"""t:urlDecodeUni — str.replace_all / str.replace_re_all chain.

urlDecodeUni is a strict superset of urlDecode. In addition to standard
application/x-www-form-urlencoded decoding it handles:

  1. '+' → space (ASCII 0x20)                           — same as urlDecode
  2. '%XX'    → byte 0xXX (0x00–0xFF, case-insensitive) — same as urlDecode
  3. '%uXXXX' → Unicode code point U+XXXX (0000-FFFF)    — IIS Unicode encoding
  4. Full-width ASCII U+FF01–U+FF5E → U+0021–U+007E     — best-fit mapping

For (3) the approach is the same as for (2): one str.replace_re_all call per
code point, where the regex covers both 'u'/'U' and all upper/lower-case
combinations of the four hex digits, and the fixed replacement is the SMT-LIB2
Unicode escape '\\u{XXXX}'.  This works naturally because SMT-LIB2 string
literals already use '\\u{XXXX}' to denote Unicode code points.

Pass ordering
  The same invariants as urlDecode apply (see url_decode.py), extended to the
  %uXXXX group:

  Pass 1   : '+' → space
  Passes 2–N: '%XX' ≠ '%25' — standard percent decoding
  Pass N+1  : '%25' → '%'   — last among '%XX', prevents '%25XX' double-decode
  Passes N+2–M: '%uXXXX' ≠ '%u0025' — IIS Unicode decoding
  Pass M+1  : '%u0025' → '%' — last among '%uXXXX'
  Passes M+2+: full-width ASCII character substitutions

  Running '%uXXXX' after '%XX' ensures '%u002541' → '%41', not 'A': once
  '%u0025' decodes to '%' the '%41' suffix is never re-decoded because the
  '%XX' passes have already completed.

  Known limitation: '%25u0025' → '%u0025' → '%'. ModSecurity's single-pass
  would give '%u0025' (after decoding '%25' to '%', the characters 'u0025'
  are emitted as-is without re-scanning). This edge case is structurally
  identical to the '&amp;lt;' → '<;' limitation in htmlEntityDecode and is
  accepted as an unavoidable consequence of the multi-pass model.
"""

from __future__ import annotations

from .url_decode import _smt_char_literal, _nibble_re, _percent_re


_U_RE = '(re.union (str.to_re "u") (str.to_re "U"))'

_FULLWIDTH_FIRST = 0xFF01
_FULLWIDTH_LAST  = 0xFF5E
_ASCII_FIRST     = 0x0021


def _smt_char_unicode(codepoint: int) -> str:
    return f"\\u{{{codepoint:04x}}}"


def _percent_u_re(codepoint: int) -> str:
    """SMT-LIB2 regex matching all case variants of '%uXXXX' for *codepoint*."""
    n1 = _nibble_re((codepoint >> 12) & 0xF)
    n2 = _nibble_re((codepoint >> 8)  & 0xF)
    n3 = _nibble_re((codepoint >> 4)  & 0xF)
    n4 = _nibble_re( codepoint        & 0xF)
    return f'(re.++ (str.to_re "%") {_U_RE} {n1} {n2} {n3} {n4})'


def url_decode_uni_fun_decl() -> str:
    """Return the (define-fun t_urlDecodeUni ...) SMT-LIB2 declaration."""
    body = "s"

    # --- Group 1: standard urlDecode passes ---

    # Pass 1: '+' → space
    body = f'(str.replace_all {body} "+" "{_smt_char_literal(0x20)}")'

    # Passes 2..N-1: '%XX' → byte for all bytes except 0x25
    for byte in range(256):
        if byte == 0x25:
            continue
        body = (f'(str.replace_re_all {body} {_percent_re(byte)}'
                f' "{_smt_char_literal(byte)}")')

    # Pass N: '%25' → '%' (last among '%XX')
    body = (f'(str.replace_re_all {body} {_percent_re(0x25)}'
            f' "{_smt_char_literal(0x25)}")')

    # --- Group 2: IIS '%uXXXX' Unicode decoding ---
    # Runs after '%XX' so that '%u002541' → '%41' (not 'A'): '%u0025' decodes
    # to '%' after all '%XX' passes have completed, leaving the trailing hex
    # chars undecoded.

    # Passes: '%uXXXX' for all BMP code points except U+0025 ('%')
    for cp in range(0x10000):
        if cp == 0x0025:
            continue
        body = (f'(str.replace_re_all {body} {_percent_u_re(cp)}'
                f' "{_smt_char_unicode(cp)}")')

    # Last '%uXXXX' pass: U+0025 → '%'
    body = (f'(str.replace_re_all {body} {_percent_u_re(0x0025)}'
            f' "{_smt_char_unicode(0x0025)}")')

    # --- Group 3: full-width ASCII best-fit mapping ---
    # U+FF01–U+FF5E → U+0021–U+007E (94 characters)
    for i in range(_FULLWIDTH_LAST - _FULLWIDTH_FIRST + 1):
        fw    = _FULLWIDTH_FIRST + i
        ascii = _ASCII_FIRST + i
        body = (f'(str.replace_all {body} "{_smt_char_unicode(fw)}"'
                f' "{_smt_char_unicode(ascii)}")')

    return f"(define-fun t_urlDecodeUni ((s String)) String {body})"


# NOTE: Not computed at import time — calling url_decode_uni_fun_decl() takes
# ~15 s and produces a ~13 MB declaration with 65 887 passes.  The resulting
# SMT formula is too large for practical solver use; urlDecodeUni is therefore
# kept as an uninterpreted function with axioms in smt.py.  This module exists
# to demonstrate that the exact define-fun model is achievable in principle.
def _build_url_decode_uni_fun_decl() -> str:
    """Build on demand — expensive (~15 s, ~13 MB)."""
    return url_decode_uni_fun_decl()
