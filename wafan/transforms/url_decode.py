"""t:urlDecode — modelled as str.replace_all / str.replace_re_all passes.

ModSecurity's urlDecode decodes application/x-www-form-urlencoded input
in a single left-to-right scan:
  1. '+' → space (ASCII 0x20)
  2. '%XX' (case-insensitive hex) → the corresponding byte value (0x00–0xFF)
  3. Invalid or incomplete '%' sequences pass through unchanged

The transform is modelled as 257 passes:
  Pass 1:   str.replace_all '+' → space (first so '%2B' → '+' is not
            re-decoded to space)
  Pass 2..N-1: str.replace_re_all with regex covering all case variants
            of '%XX', one pass per byte value (except 0x25)
  Pass N:   str.replace_re_all for '%25' → '%' (last to prevent the
            multi-pass chain from double-decoding '%25XX' → '%XX' → char,
            which would diverge from ModSecurity's single-pass scan)

Using str.replace_re_all instead of enumerating each case variant with
str.replace_all reduces the pass count from ~485 to 257: each nibble that is
a hex letter (a-f / A-F) is covered by a (re.union …) term, so one regex
per byte value handles all upper/lower-case combinations.

Pass-ordering correctness argument
  - Pass 1 must precede passes 2-N so that a literal '+' in the input becomes
    a space, while '%2B' (percent-encoded '+') later becomes '+' (not space).
  - No replacement in passes 2..N-1 can produce a '%' character because 0x25
    is excluded from those passes. Therefore no pass-2 result can interact
    with adjacent characters to synthesise a new '%XX' pattern that a later
    pass would then decode—each '%XX' in the original input is decoded at
    most once.
  - Placing '%25' last ensures: if the input contains '%25XX', passes 2..N-1
    leave '%25XX' intact (there is no matching '%XX' pattern at that position
    for XX ≠ 25), then pass N decodes '%25' → '%', yielding '%XX' that the
    earlier passes have already consumed. ModSecurity's single-pass result is
    identical ('%XX' passes through as literal suffix after '%25').

Known limitation (shared with htmlEntityDecode): the multi-pass chain is not
an exact model of ModSecurity's single left-to-right scan. The pass ordering
above handles the known '%25XX' corner case correctly.
"""

from __future__ import annotations


def _smt_char_literal(byte: int) -> str:
    return f"\\u{{{byte:02x}}}"


def _nibble_re(nibble: int) -> str:
    """Return an SMT-LIB2 regex term matching both case variants of a hex nibble.

    For decimal digits (0–9) there is only one variant; for letters (a–f /
    A–F) both lower- and upper-case forms are covered by a re.union term.
    """
    if nibble < 10:
        return f'(str.to_re "{nibble}")'
    lo = chr(ord("a") + nibble - 10)
    hi = lo.upper()
    return f'(re.union (str.to_re "{lo}") (str.to_re "{hi}"))'


def _percent_re(byte: int) -> str:
    """Return an SMT-LIB2 regex matching all case variants of '%XX' for *byte*."""
    hi, lo = byte >> 4, byte & 0x0F
    return f'(re.++ (str.to_re "%") {_nibble_re(hi)} {_nibble_re(lo)})'


def _url_decode_body(inner: str) -> str:
    """Build the urlDecode pass chain applied to *inner*, returning an SMT expression."""
    body = inner
    body = f'(str.replace_all {body} "+" "{_smt_char_literal(0x20)}")'
    for byte in range(256):
        if byte == 0x25:
            continue
        body = (
            f'(str.replace_re_all {body} {_percent_re(byte)}'
            f' "{_smt_char_literal(byte)}")'
        )
    body = (
        f'(str.replace_re_all {body} {_percent_re(0x25)}'
        f' "{_smt_char_literal(0x25)}")'
    )
    return body


def url_decode_fun_decl() -> str:
    """Return the (define-fun t_urlDecode ...) SMT-LIB2 declaration."""
    return f"(define-fun t_urlDecode ((s String)) String {_url_decode_body('s')})"


URL_DECODE_FUN_DECL = url_decode_fun_decl()
