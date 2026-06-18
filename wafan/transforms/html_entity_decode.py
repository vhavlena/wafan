"""t:htmlEntityDecode — modelled as str.replace_all / str.replace_re_all passes.

ModSecurity's htmlEntityDecode (apache2/msc_util.c / html_entity_decode.cc)
decodes a fixed 6-entry named-entity table plus decimal/hex numeric character
references, always emitting a single byte (values >= 256 are truncated to
their low byte).

Pass structure (1036 passes total vs ~5132 in the literal-only version):

  Group 1 — forms WITH trailing ';' (processed before no-semicolon forms):
    a. str.replace_all  × 6   Named entities (&lt; … &amp; last)
    b. str.replace_re_all × 256  Decimal: &#0?DEC;  — no prefix-overlap
                                  possible because ';' terminates the match
    c. str.replace_re_all × 256  Hex:     &#[xX]0?HH; — x/X and letter-case
                                  variants folded into re.union terms

  Group 2 — forms WITHOUT trailing ';':
    d. str.replace_re_all × 256  Hex:     &#[xX]0?HH  — no ordering needed;
                                  all patterns have a constant-length suffix
    e. str.replace_re_all × 256  Decimal: &#0?DEC  — MUST be processed in
                                  descending decimal-digit-count order so that
                                  e.g. '&#10' is consumed as LF before the
                                  '&#1' pass can eat its '&#1' prefix;
                                  amp (38, 2-digit) is last within its group
    f. str.replace_all  × 6   Named entities (&lt … &amp last)

Pass-ordering rules that make the chain behave like ModSecurity's single scan:
  1. Forms WITH ';' before forms WITHOUT — prevents '&lt;' being decoded as
     '&lt' + ';'.
  2. Within the no-semicolon decimal group, longer decimal representations
     first — prevents a shorter prefix (e.g. '&#1') stealing part of a
     longer match (e.g. '&#10').
  3. Entities decoding to '&' (&amp; / &#38; / &#x26;) are processed last
     within their group — so their '&' output cannot be picked up by an
     earlier pass and trigger a second decoding step (htmlEntityDecode is
     documented as single-pass: '&amp;lt;' -> '&lt;', not '<').

Known limitations (documented, not modelled):
  - numeric references >= 256 / >= 0x100 (low-byte truncation of multi-digit
    values beyond the enumerated 0-255 forms below) are left as-is.
  - the canonical '&amp;lt;' -> '&lt;' (single-pass, NOT '<') example is not
    reproduced exactly: once '&amp;' is decoded to '&' by the named-with-';'
    pass it forms a new '&lt;', which the later named-without-';' pass then
    decodes to '<', yielding '<;' instead of '&lt;'. A fully faithful
    single-pass scan requires a non-recursive string theory this z3 build
    does not provide.
"""

from __future__ import annotations

_HTML_NAMED_ENTITIES: tuple[tuple[str, int], ...] = (
    ("lt",   0x3C),
    ("gt",   0x3E),
    ("quot", 0x22),
    ("nbsp", 0xA0),
    ("apos", 0x27),
    ("amp",  0x26),  # produces '&' — must stay last in each group
)


def _smt_char_literal(byte: int) -> str:
    return f"\\u{{{byte:02x}}}"


def _nibble_re(nibble: int) -> str:
    """SMT-LIB2 regex term matching both case variants of a hex nibble."""
    if nibble < 10:
        return f'(str.to_re "{nibble}")'
    lo = chr(ord("a") + nibble - 10)
    hi = lo.upper()
    return f'(re.union (str.to_re "{lo}") (str.to_re "{hi}"))'


_X_RE = '(re.union (str.to_re "x") (str.to_re "X"))'


def _hex_entity_re(byte: int, semi: bool) -> str:
    """SMT-LIB2 regex matching all case variants of '&#xXX[;]' for *byte*."""
    hi, lo = byte >> 4, byte & 0x0F
    parts = [
        '(str.to_re "&#")',
        _X_RE,
        '(re.opt (str.to_re "0"))',
        _nibble_re(hi),
        _nibble_re(lo),
    ]
    if semi:
        parts.append('(str.to_re ";")')
    return f'(re.++ {" ".join(parts)})'


def _dec_entity_re(value: int, semi: bool) -> str:
    """SMT-LIB2 regex matching '&#[0]DEC[;]' for *value*."""
    parts = [
        '(str.to_re "&#")',
        '(re.opt (str.to_re "0"))',
        f'(str.to_re "{value}")',
    ]
    if semi:
        parts.append('(str.to_re ";")')
    return f'(re.++ {" ".join(parts)})'


def _bytes_amp_last() -> list[int]:
    """Return 0-255 with 0x26 ('&') at the end."""
    return [v for v in range(256) if v != 0x26] + [0x26]


def html_entity_decode_fun_decl() -> str:
    """Return the (define-fun t_htmlEntityDecode ...) SMT-LIB2 declaration."""
    body = "s"

    # --- Group 1: forms WITH trailing ';' ---

    # (a) Named entities WITH ';' — amp is last in _HTML_NAMED_ENTITIES
    for name, val in _HTML_NAMED_ENTITIES:
        body = f'(str.replace_all {body} "&{name};" "{_smt_char_literal(val)}")'

    # (b) Decimal numeric WITH ';': &#0?DEC;
    # The ';' terminator prevents prefix-overlap, so any order is correct.
    for v in _bytes_amp_last():
        body = (f'(str.replace_re_all {body} {_dec_entity_re(v, semi=True)}'
                f' "{_smt_char_literal(v)}")')

    # (c) Hex numeric WITH ';': &#[xX]0?HH; — covers x/X and letter-case variants
    for v in _bytes_amp_last():
        body = (f'(str.replace_re_all {body} {_hex_entity_re(v, semi=True)}'
                f' "{_smt_char_literal(v)}")')

    # --- Group 2: forms WITHOUT trailing ';' ---

    # (d) Hex numeric WITHOUT ';': &#[xX]0?HH
    # All patterns have the same constant-length suffix structure, so no
    # ordering is needed among them.
    for v in _bytes_amp_last():
        body = (f'(str.replace_re_all {body} {_hex_entity_re(v, semi=False)}'
                f' "{_smt_char_literal(v)}")')

    # (e) Decimal numeric WITHOUT ';': &#0?DEC — MUST process longer decimal
    # representations first. E.g. value 10 (regex &#0?10) must run before
    # value 1 (&#0?1) so that '&#10' is not partially consumed as '&#1' + '0'.
    # Sort key: descending decimal digit count, amp (38, 2-digit) last in its
    # digit-count group.
    def _dec_nosemi_key(v: int) -> tuple:
        return (-len(str(v)), v == 0x26)

    for v in sorted(range(256), key=_dec_nosemi_key):
        body = (f'(str.replace_re_all {body} {_dec_entity_re(v, semi=False)}'
                f' "{_smt_char_literal(v)}")')

    # (f) Named entities WITHOUT ';' — amp is last in _HTML_NAMED_ENTITIES
    for name, val in _HTML_NAMED_ENTITIES:
        body = f'(str.replace_all {body} "&{name}" "{_smt_char_literal(val)}")'

    return f"(define-fun t_htmlEntityDecode ((s String)) String {body})"


HTML_ENTITY_DECODE_FUN_DECL = html_entity_decode_fun_decl()
