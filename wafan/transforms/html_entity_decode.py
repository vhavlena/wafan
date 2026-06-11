"""t:htmlEntityDecode — modelled as a chain of literal str.replace_all passes.

ModSecurity's htmlEntityDecode (apache2/msc_util.c / html_entity_decode.cc)
decodes a fixed 6-entry named-entity table plus decimal/hex numeric
character references, always emitting a single byte (values >= 256 are
truncated to their low byte). Each decoded entity is a fixed-length literal
string, so the whole transform can be expressed precisely as a sequence of
(str.replace_all s "&...;" "<byte>") passes.

Pass ordering rules that make the literal-replace chain behave like
ModSecurity's single left-to-right scan:
  1. Forms WITH a trailing ';' are processed before forms WITHOUT one,
     so e.g. "&lt;" is decoded as "<" rather than "&lt" -> "<" + ";".
  2. Within the "no trailing ';'" group, longer literals are processed
     first (e.g. "&#012" before "&#01" before "&#1"), so a longer
     reference is never partially matched by a shorter one's prefix.
  3. Entities that decode to '&' (&amp; / &#38; / &#x26;) are processed
     last within their group, so their output '&' cannot be picked up by
     an earlier pass and trigger a second decoding step (htmlEntityDecode
     is documented as single-pass: "&amp;lt;" -> "&lt;", not "<").

Known limitations (documented, not modelled):
  - numeric references >= 256 / >= 0x100 (low-byte truncation of multi-
    digit values beyond the enumerated 0-255 forms below) are left as-is.
  - unknown named entities and HTML5 named entities correctly pass through
    unchanged (they are simply absent from the replacement table).
  - the canonical "&amp;lt;" -> "&lt;" (single-pass, NOT "<") example from
    the spec is not reproduced exactly: once "&amp;" is decoded to '&' it
    forms a new "&lt;", and the no-semicolon pass 4 ("&lt" -> "<") then
    matches its "&lt" prefix, yielding "<;" instead of "&lt;". A fully
    faithful single-pass scan would require a non-recursive string theory
    this z3 build does not provide.
"""

from __future__ import annotations

_HTML_NAMED_ENTITIES: tuple[tuple[str, int], ...] = (
    ("lt", 0x3C),
    ("gt", 0x3E),
    ("quot", 0x22),
    ("nbsp", 0xA0),
    ("apos", 0x27),
    ("amp", 0x26),  # produces '&' — must stay last in each group
)


def _smt_char_literal(byte: int) -> str:
    return f"\\u{{{byte:02x}}}"


def _html_entity_decode_pairs() -> list[tuple[str, str]]:
    """Ordered (literal_pattern, literal_replacement) pairs for htmlEntityDecode."""
    pairs: list[tuple[str, str]] = []

    # 1) named entities, with trailing ';' (amp last, see module docstring)
    for name, val in _HTML_NAMED_ENTITIES:
        pairs.append((f"&{name};", _smt_char_literal(val)))

    # 2) numeric entities (decimal + hex), 0-255, with trailing ';'.
    #    A single optional leading zero is supported for both bases
    #    (covers e.g. "&#060;" / "&#x03C;"). '&'-producing value 0x26 last.
    numeric_semi: list[tuple[str, str]] = []
    amp_numeric_semi: list[tuple[str, str]] = []
    for v in range(256):
        ch = _smt_char_literal(v)
        dec = str(v)
        hx = f"{v:02x}"
        forms = {f"&#{dec};", f"&#0{dec};"}
        for h in {hx, hx.upper()}:
            forms |= {f"&#x{h};", f"&#X{h};", f"&#x0{h};", f"&#X0{h};"}
        target = amp_numeric_semi if v == 0x26 else numeric_semi
        target.extend((f, ch) for f in forms)
    pairs.extend(numeric_semi)
    pairs.extend(amp_numeric_semi)

    # 3) numeric entities without trailing ';', longest pattern first so a
    #    shorter reference's literal can't match as a prefix of a longer one.
    nosemi: list[tuple[str, str, bool]] = []
    for v in range(256):
        ch = _smt_char_literal(v)
        dec = str(v)
        hx = f"{v:02x}"
        forms = {f"&#{dec}", f"&#0{dec}"}
        for h in {hx, hx.upper()}:
            forms |= {f"&#x{h}", f"&#X{h}", f"&#x0{h}", f"&#X0{h}"}
        nosemi.extend((f, ch, v == 0x26) for f in forms)
    nosemi.sort(key=lambda t: -len(t[0]))
    pairs.extend((p, c) for p, c, is_amp in nosemi if not is_amp)
    pairs.extend((p, c) for p, c, is_amp in nosemi if is_amp)

    # 4) named entities without trailing ';' (amp last)
    for name, val in _HTML_NAMED_ENTITIES:
        pairs.append((f"&{name}", _smt_char_literal(val)))

    return pairs


_HTML_ENTITY_DECODE_PAIRS = _html_entity_decode_pairs()


def html_entity_decode_fun_decl() -> str:
    """Return the (define-fun t_htmlEntityDecode ...) declaration."""
    body = "s"
    for pattern, replacement in _HTML_ENTITY_DECODE_PAIRS:
        body = f'(str.replace_all {body} "{pattern}" "{replacement}")'
    return f"(define-fun t_htmlEntityDecode ((s String)) String {body})"


HTML_ENTITY_DECODE_FUN_DECL = html_entity_decode_fun_decl()
