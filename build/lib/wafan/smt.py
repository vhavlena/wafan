"""Convert SecRule conditions to SMT-LIB2 format.

Only @rx (ECMA regex matching) is supported, via the `re.from_ecma2020`
SMT-LIB function, targeting the z3-noodler backend.

SecRule ``t:`` transformations are handled in two ways:

Direct SMT-LIB counterparts (applied inline):
  none            – resets the transform chain (identity)
  lowercase       – str.to_lower
  uppercase       – str.to_upper

Modelled precisely as a define-fun chaining literal str.replace_all passes:
  htmlEntityDecode– t_htmlEntityDecode, see _html_entity_decode_fun_decl for
                    the full table and pass-ordering rules.

Uninterpreted functions (declared per-formula with constraining axioms):
  urlDecode       – t_urlDecode       : length-non-increasing, idempotent
  urlDecodeUni    – t_urlDecodeUni    : same axioms as urlDecode
  removeWhitespace– t_removeWhitespace: idempotent, result contains no
                                        space / tab / CR / LF
  compressWhitespace–t_compressWhitespace: idempotent, no consecutive spaces
  removeNulls     – t_removeNulls     : idempotent, length-non-increasing
  trim            – t_trim            : idempotent, length-non-increasing
  trimLeft        – t_trimLeft        : idempotent, length-non-increasing
  trimRight       – t_trimRight       : idempotent, length-non-increasing
  normalizePath   – t_normalizePath   : idempotent, result free of /../ / /./
  normalizePathWin– t_normalizePathWin: same axioms as normalizePath

Transforms not listed above raise UnsupportedTransformError.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

from .parser import SecRule, SecRuleAction, SecRuleVariable
from .regex_conv import UnsupportedPatternError, pcre_to_ecma2020


SMT_LOGIC = "QF_SLIA"


# ---------------------------------------------------------------------------
# Transform table
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _TransformDef:
    """Definition of one SecRule transform in SMT-LIB2 terms."""
    smt_fn: str           # SMT function name, e.g. "str.lower"; empty = direct inline
    fun_decl: str = ""    # (declare-fun …) line; empty for built-in SMT functions
    axioms: tuple[str, ...] = ()

    def apply(self, expr: str) -> str:
        return f"({self.smt_fn} {expr})"


def _uninterpreted(name: str, *axioms: str) -> _TransformDef:
    """Build a _TransformDef for an uninterpreted (String) → String function."""
    decl = f"(declare-fun {name} (String) String)"
    return _TransformDef(smt_fn=name, fun_decl=decl, axioms=tuple(axioms))


def _forall(body: str) -> str:
    return f"(assert (forall ((s String)) {body}))"


def _idempotent(fn: str) -> str:
    return _forall(f"(= ({fn} ({fn} s)) ({fn} s))")


def _len_le(fn: str) -> str:
    return _forall(f"(<= (str.len ({fn} s)) (str.len s))")


def _empty_fixed(fn: str) -> str:
    return f'(assert (= ({fn} "") ""))'


def _no_substring(fn: str, sub: str) -> str:
    escaped = sub.replace("\\", "\\\\")
    return _forall(f'(not (str.contains ({fn} s) "{escaped}"))')


def _no_double(fn: str, sub: str) -> str:
    escaped = sub.replace("\\", "\\\\")
    return _forall(f'(not (str.contains ({fn} s) "{escaped}{escaped}"))')


_URL_DECODE_AXIOMS = (
    _len_le("t_urlDecode"),
    _idempotent("t_urlDecode"),
    _empty_fixed("t_urlDecode"),
)

_REMOVE_WS_AXIOMS = (
    _len_le("t_removeWhitespace"),
    _idempotent("t_removeWhitespace"),
    _empty_fixed("t_removeWhitespace"),
    _no_substring("t_removeWhitespace", " "),
    _no_substring("t_removeWhitespace", "\t"),
    _no_substring("t_removeWhitespace", "\n"),
    _no_substring("t_removeWhitespace", "\r"),
)

_COMPRESS_WS_AXIOMS = (
    _len_le("t_compressWhitespace"),
    _idempotent("t_compressWhitespace"),
    _empty_fixed("t_compressWhitespace"),
    _no_double("t_compressWhitespace", " "),
)

_REMOVE_NULLS_AXIOMS = (
    _len_le("t_removeNulls"),
    _idempotent("t_removeNulls"),
    _empty_fixed("t_removeNulls"),
)

_TRIM_AXIOMS = (
    _len_le("t_trim"),
    _idempotent("t_trim"),
    _empty_fixed("t_trim"),
)

_TRIM_LEFT_AXIOMS = (
    _len_le("t_trimLeft"),
    _idempotent("t_trimLeft"),
    _empty_fixed("t_trimLeft"),
)

_TRIM_RIGHT_AXIOMS = (
    _len_le("t_trimRight"),
    _idempotent("t_trimRight"),
    _empty_fixed("t_trimRight"),
)

_NORM_PATH_AXIOMS = (
    _idempotent("t_normalizePath"),
    _empty_fixed("t_normalizePath"),
    _no_substring("t_normalizePath", "/../"),
    _no_substring("t_normalizePath", "/./"),
)

_NORM_PATH_WIN_AXIOMS = (
    _idempotent("t_normalizePathWin"),
    _empty_fixed("t_normalizePathWin"),
    _no_substring("t_normalizePathWin", "\\..\\"),
    _no_substring("t_normalizePathWin", "\\.\\"),
)

# ---------------------------------------------------------------------------
# t:htmlEntityDecode — modelled as a chain of literal str.replace_all passes
# ---------------------------------------------------------------------------
#
# ModSecurity's htmlEntityDecode (apache2/msc_util.c / html_entity_decode.cc)
# decodes a fixed 6-entry named-entity table plus decimal/hex numeric
# character references, always emitting a single byte (values >= 256 are
# truncated to their low byte). Each decoded entity is a fixed-length literal
# string, so the whole transform can be expressed precisely as a sequence of
# (str.replace_all s "&...;" "<byte>") passes (re.from_ecma2020-based
# str.replace_re_all is not usable here: this z3-noodler build does not
# support it).
#
# Pass ordering rules that make the literal-replace chain behave like
# ModSecurity's single left-to-right scan:
#   1. Forms WITH a trailing ';' are processed before forms WITHOUT one,
#      so e.g. "&lt;" is decoded as "<" rather than "&lt" -> "<" + ";".
#   2. Within the "no trailing ';'" group, longer literals are processed
#      first (e.g. "&#012" before "&#01" before "&#1"), so a longer
#      reference is never partially matched by a shorter one's prefix.
#   3. Entities that decode to '&' (&amp; / &#38; / &#x26;) are processed
#      last within their group, so their output '&' cannot be picked up by
#      an earlier pass and trigger a second decoding step (htmlEntityDecode
#      is documented as single-pass: "&amp;lt;" -> "&lt;", not "<").
#
# Known limitations (documented, not modelled):
#   - numeric references >= 256 / >= 0x100 (low-byte truncation of multi-
#     digit values beyond the enumerated 0-255 forms below) are left as-is.
#   - unknown named entities and HTML5 named entities correctly pass through
#     unchanged (they are simply absent from the replacement table).
#   - the canonical "&amp;lt;" -> "&lt;" (single-pass, NOT "<") example from
#     the spec is not reproduced exactly: once "&amp;" is decoded to '&' it
#     forms a new "&lt;", and the no-semicolon pass 4 ("&lt" -> "<") then
#     matches its "&lt" prefix, yielding "<;" instead of "&lt;". A fully
#     faithful single-pass scan would require a non-recursive string theory
#     this z3 build does not provide.

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


def _html_entity_decode_fun_decl() -> str:
    body = "s"
    for pattern, replacement in _HTML_ENTITY_DECODE_PAIRS:
        body = f'(str.replace_all {body} "{pattern}" "{replacement}")'
    return f"(define-fun t_htmlEntityDecode ((s String)) String {body})"


_HTML_ENTITY_DECODE_FUN_DECL = _html_entity_decode_fun_decl()


# Keys are normalised (lower-cased) transform names.
# "none" is excluded — it is handled specially by extract_transforms.
_TRANSFORMS: dict[str, _TransformDef] = {
    # --- direct SMT-LIB built-ins ---
    "lowercase":  _TransformDef(smt_fn="str.to_lower"),
    "uppercase":  _TransformDef(smt_fn="str.to_upper"),
    # --- uninterpreted functions ---
    "urldecode":         _uninterpreted("t_urlDecode",          *_URL_DECODE_AXIOMS),
    "urldecodeuni":      _uninterpreted("t_urlDecodeUni",
                             _len_le("t_urlDecodeUni"),
                             _idempotent("t_urlDecodeUni"),
                             _empty_fixed("t_urlDecodeUni"),
                         ),
    "htmlentitydecode":  _TransformDef(smt_fn="t_htmlEntityDecode",
                                        fun_decl=_HTML_ENTITY_DECODE_FUN_DECL),
    "removewhitespace":  _uninterpreted("t_removeWhitespace",   *_REMOVE_WS_AXIOMS),
    "compresswhitespace":_uninterpreted("t_compressWhitespace", *_COMPRESS_WS_AXIOMS),
    "removenulls":       _uninterpreted("t_removeNulls",        *_REMOVE_NULLS_AXIOMS),
    "trim":              _uninterpreted("t_trim",               *_TRIM_AXIOMS),
    "trimleft":          _uninterpreted("t_trimLeft",           *_TRIM_LEFT_AXIOMS),
    "trimright":         _uninterpreted("t_trimRight",          *_TRIM_RIGHT_AXIOMS),
    "normalizepath":     _uninterpreted("t_normalizePath",      *_NORM_PATH_AXIOMS),
    "normalizepathwin":  _uninterpreted("t_normalizePathWin",   *_NORM_PATH_WIN_AXIOMS),
}


class UnsupportedTransformError(Exception):
    """Raised when a SecRule transformation is unknown to this module."""


# ---------------------------------------------------------------------------
# SmtFormula
# ---------------------------------------------------------------------------

@dataclass
class SmtFormula:
    """SMT-LIB2 representation of a single SecRule condition."""

    rule_id: str
    declarations: list[str]      # (declare-const VAR String)
    assertion: str
    fun_declarations: list[str] = field(default_factory=list)   # (declare-fun …)
    axioms: list[str] = field(default_factory=list)             # axiom asserts

    def to_smt2(self) -> str:
        """Render a self-contained, check-sat-ready SMT-LIB2 string."""
        lines = [
            f"(set-logic {SMT_LOGIC})",
            f"; rule id:{self.rule_id}",
            *self.fun_declarations,
            *self.axioms,
            *self.declarations,
            f"(assert {self.assertion})",
            "(check-sat)",
        ]
        return "\n".join(lines)

    def declared_var_names(self) -> list[str]:
        """Return variable names from declaration lines, preserving order."""
        names: list[str] = []
        for decl in self.declarations:
            parts = decl.split()
            # (declare-const NAME String)
            if len(parts) >= 3 and parts[0] == "(declare-const":
                names.append(parts[1])
        return names

    def to_smt2_with_model(self) -> str:
        """Like to_smt2(), but adds (get-value ...) to extract a concrete model.

        Requires the solver to be launched with model generation enabled
        (e.g. z3 model=true -in).  Only meaningful when check-sat returns sat.
        """
        var_names = self.declared_var_names()
        get_value = "(get-value (" + " ".join(var_names) + "))"
        lines = [
            f"(set-logic {SMT_LOGIC})",
            f"; rule id:{self.rule_id}",
            *self.fun_declarations,
            *self.axioms,
            *self.declarations,
            f"(assert {self.assertion})",
            "(check-sat)",
            get_value,
        ]
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Transformation helpers
# ---------------------------------------------------------------------------

def extract_transforms(actions: Sequence[SecRuleAction]) -> list[str]:
    """Return the effective ordered list of transformation names from actions.

    ``t:none`` resets any previously accumulated transforms (ModSecurity
    semantics: "removes all transformations configured for the current rule").
    """
    transforms: list[str] = []
    for action in actions:
        if action.name == "t":
            if action.arg.lower() == "none":
                transforms = []
            else:
                transforms.append(action.arg)
    return transforms


def apply_transforms_smt(var_expr: str, transforms: Sequence[str]) -> str:
    """Wrap *var_expr* with SMT-LIB transformation functions.

    Transforms are applied left-to-right (innermost = first applied), e.g.
    ``[lowercase, uppercase]`` produces ``(str.to_upper (str.to_lower var))``.

    Raises UnsupportedTransformError for any transform not in _TRANSFORMS.
    """
    expr = var_expr
    for t in transforms:
        defn = _TRANSFORMS.get(t.lower())
        if defn is None:
            raise UnsupportedTransformError(
                f"Transform '{t}' is not supported"
            )
        expr = defn.apply(expr)
    return expr


def transform_preamble(transforms: Sequence[str]) -> tuple[list[str], list[str]]:
    """Return ``(fun_declarations, axioms)`` required by *transforms*.

    Only uninterpreted transforms contribute entries; direct SMT-LIB functions
    (e.g. ``str.to_lower``) need no declaration.  Duplicates are eliminated while
    preserving first-seen order.
    """
    seen: set[str] = set()
    fun_decls: list[str] = []
    axioms: list[str] = []

    for t in transforms:
        key = t.lower()
        defn = _TRANSFORMS.get(key)
        if defn is None:
            raise UnsupportedTransformError(f"Transform '{t}' is not supported")
        if defn.fun_decl and key not in seen:
            seen.add(key)
            fun_decls.append(defn.fun_decl)
            axioms.extend(defn.axioms)

    return fun_decls, axioms


# ---------------------------------------------------------------------------
# Variable / pattern helpers
# ---------------------------------------------------------------------------

def _smt_var_name(variable: SecRuleVariable) -> str:
    """Produce a sanitised SMT identifier for a ModSecurity variable."""
    name = variable.name
    if variable.part:
        name = f"{name}__{variable.part}"
    return name.replace("-", "_").replace(".", "_").replace(":", "_")


def _escape_smt_string(pattern: str) -> str:
    """Escape a regex pattern for embedding in an SMT-LIB2 string literal."""
    return pattern.replace("\\", "\\\\").replace('"', '\\"')


def _rx_assertion(var_expr: str, pattern: str, negated: bool) -> str:
    escaped = _escape_smt_string(pattern)
    inner = f'(str.in_re {var_expr} (re.from_ecma2020 "{escaped}"))'
    return f"(not {inner})" if negated else inner


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def rx_rule_to_smt(rule: SecRule) -> SmtFormula:
    """Convert a single @rx SecRule to an SmtFormula.

    Transformation actions (t:) are extracted and applied as SMT-LIB wrappers
    around each variable expression.  Uninterpreted transforms are declared and
    axiomatised in the formula preamble.

    Each ModSecurity variable becomes a free String constant.  Multiple
    variables produce a disjunctive assertion.

    Raises:
        ValueError: if the operator is not @rx / !@rx.
        UnsupportedTransformError: if a t: action is unknown.
    """
    if rule.operator not in ("@rx", "!@rx"):
        raise ValueError(
            f"Rule {rule.rule_id}: operator '{rule.operator}' is not @rx"
        )

    negated = rule.negated or rule.operator == "!@rx"
    conv = pcre_to_ecma2020(rule.operator_argument)
    pattern = conv.pattern
    transforms = extract_transforms(rule.actions)
    fun_decls, axioms = transform_preamble(transforms)

    declarations: list[str] = []
    assertions: list[str] = []
    seen: set[str] = set()

    for variable in rule.variables:
        v = _smt_var_name(variable)
        if v not in seen:
            declarations.append(f"(declare-const {v} String)")
            seen.add(v)
        var_expr = apply_transforms_smt(v, transforms)
        assertions.append(_rx_assertion(var_expr, pattern, negated))

    assertion = assertions[0] if len(assertions) == 1 else "(or " + " ".join(assertions) + ")"

    return SmtFormula(
        rule_id=rule.rule_id,
        fun_declarations=fun_decls,
        axioms=axioms,
        declarations=declarations,
        assertion=assertion,
    )


def rules_to_smt(rules: Sequence[SecRule]) -> list[SmtFormula]:
    """Convert a sequence of @rx SecRules to SmtFormulas, skipping others."""
    result = []
    for rule in rules:
        if rule.operator in ("@rx", "!@rx"):
            result.append(rx_rule_to_smt(rule))
    return result
