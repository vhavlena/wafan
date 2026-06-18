"""Convert SecRule conditions to SMT-LIB2 format.

Supported operators (see _OPERATORS / is_supported_operator):
  @rx          – ECMA regex matching, via the `re.from_ecma2020` SMT-LIB
                 function, targeting the z3-noodler backend.
  @streq       – string equality (str.=)
  @contains    – substring match (str.contains)
  @beginsWith  – prefix match (str.prefixof)
  @endsWith    – suffix match (str.suffixof)
  @within      – input is a substring of one of a space-separated list of values
  @pm          – any of a space-separated list of phrases is a substring of the input
  @eq/@ge/@gt/@le/@lt – numeric comparison of (str.to_int input) against an
                 integer argument; the argument must be a literal integer
                 (macro expansions and floats are not supported and raise
                 UnsupportedOperatorError), and the input is additionally
                 required to be a non-empty digit string, since
                 (str.to_int input) is -1 for any non-digit string

All operators support ``!`` negation (e.g. ``!@rx``) and the rule-level
``negated`` flag.

SecRule ``t:`` transformations are handled in two ways:

Direct SMT-LIB counterparts (applied inline):
  none            – resets the transform chain (identity)
  lowercase       – str.to_lower
  uppercase       – str.to_upper

Modelled precisely as a define-fun chaining literal str.replace_all passes:
  htmlEntityDecode– t_htmlEntityDecode, see
                    wafan.transforms.html_entity_decode for the full table
                    and pass-ordering rules.

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
from typing import Callable, Sequence

from .parser import SecRule, SecRuleAction, SecRuleVariable
from .regex_conv import UnsupportedPatternError, pcre_to_ecma2020
from .transforms.html_entity_decode import HTML_ENTITY_DECODE_FUN_DECL
from .transforms.url_decode import URL_DECODE_FUN_DECL


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

# Keys are normalised (lower-cased) transform names.
# "none" is excluded — it is handled specially by extract_transforms.
_TRANSFORMS: dict[str, _TransformDef] = {
    # --- direct SMT-LIB built-ins ---
    "lowercase":  _TransformDef(smt_fn="str.to_lower"),
    "uppercase":  _TransformDef(smt_fn="str.to_upper"),
    # --- uninterpreted functions ---
    "urldecode":         _TransformDef(smt_fn="t_urlDecode",
                                       fun_decl=URL_DECODE_FUN_DECL),
    "urldecodeuni":      _uninterpreted("t_urlDecodeUni",
                             _len_le("t_urlDecodeUni"),
                             _idempotent("t_urlDecodeUni"),
                             _empty_fixed("t_urlDecodeUni"),
                         ),
    "htmlentitydecode":  _TransformDef(smt_fn="t_htmlEntityDecode",
                                        fun_decl=HTML_ENTITY_DECODE_FUN_DECL),
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


def effective_transforms(rule: SecRule) -> list[str]:
    """Return the effective ordered list of transformation names for *rule*.

    ModSecurity inherits transformations from the closest preceding
    ``SecDefaultAction`` in the same phase, but only when the rule itself
    does not define any ``t:`` action (including ``t:none``); a rule that
    defines its own transformations entirely replaces the inherited ones.
    """
    if any(action.name == "t" for action in rule.actions):
        return extract_transforms(rule.actions)
    return extract_transforms(rule.inherited_actions)


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


def _wrap_negated(atom: str, negated: bool) -> str:
    return f"(not {atom})" if negated else atom


# ---------------------------------------------------------------------------
# Operator table
# ---------------------------------------------------------------------------

class UnsupportedOperatorError(Exception):
    """Raised when a SecRule operator cannot be converted to SMT."""


def _op_rx(var_expr: str, argument: str, negated: bool) -> str:
    conv = pcre_to_ecma2020(argument)
    return _rx_assertion(var_expr, conv.pattern, negated)


def _op_streq(var_expr: str, argument: str, negated: bool) -> str:
    atom = f'(= {var_expr} "{_escape_smt_string(argument)}")'
    return _wrap_negated(atom, negated)


def _op_contains(var_expr: str, argument: str, negated: bool) -> str:
    atom = f'(str.contains {var_expr} "{_escape_smt_string(argument)}")'
    return _wrap_negated(atom, negated)


def _op_beginswith(var_expr: str, argument: str, negated: bool) -> str:
    atom = f'(str.prefixof "{_escape_smt_string(argument)}" {var_expr})'
    return _wrap_negated(atom, negated)


def _op_endswith(var_expr: str, argument: str, negated: bool) -> str:
    atom = f'(str.suffixof "{_escape_smt_string(argument)}" {var_expr})'
    return _wrap_negated(atom, negated)


def _disjunction(atoms: list[str]) -> str:
    if not atoms:
        return "false"
    if len(atoms) == 1:
        return atoms[0]
    return "(or " + " ".join(atoms) + ")"


def _op_within(var_expr: str, argument: str, negated: bool) -> str:
    # @within: matches if var_expr is a substring of one of the
    # space-separated values in argument.
    atoms = [
        f'(str.contains "{_escape_smt_string(v)}" {var_expr})'
        for v in argument.split()
    ]
    return _wrap_negated(_disjunction(atoms), negated)


def _op_pm(var_expr: str, argument: str, negated: bool) -> str:
    # @pm: matches if any of the space-separated phrases is a substring of
    # var_expr.
    atoms = [
        f'(str.contains {var_expr} "{_escape_smt_string(v)}")'
        for v in argument.split()
    ]
    return _wrap_negated(_disjunction(atoms), negated)


_NUMERIC_OPS = {"eq": "=", "ge": ">=", "gt": ">", "le": "<=", "lt": "<"}


def _make_numeric_op(smt_op: str):
    def _op(var_expr: str, argument: str, negated: bool) -> str:
        try:
            value = int(argument.strip())
        except ValueError as exc:
            raise UnsupportedOperatorError(
                f"Operator argument '{argument}' is not an integer"
            ) from exc
        # (str.to_int var_expr) is -1 for any non-digit string, which would
        # otherwise satisfy e.g. "@lt 5" for arbitrary non-numeric input.
        # Require var_expr to be a digit string for the comparison to hold.
        is_digits = f'(str.in_re {var_expr} (re.+ (re.range "0" "9")))'
        atom = f"(and {is_digits} ({smt_op} (str.to_int {var_expr}) {value}))"
        return _wrap_negated(atom, negated)

    return _op


_OPERATORS: dict[str, Callable[[str, str, bool], str]] = {
    "rx": _op_rx,
    "streq": _op_streq,
    "contains": _op_contains,
    "beginswith": _op_beginswith,
    "endswith": _op_endswith,
    "within": _op_within,
    "pm": _op_pm,
    **{name: _make_numeric_op(smt_op) for name, smt_op in _NUMERIC_OPS.items()},
}


def _normalize_operator(operator: str) -> tuple[str, bool]:
    """Split *operator* into (normalised name, bang-negated).

    e.g. ``"!@rx"`` -> ``("rx", True)``, ``"@beginsWith"`` -> ``("beginswith", False)``.
    """
    op = operator
    negated = op.startswith("!")
    if negated:
        op = op[1:]
    if op.startswith("@"):
        op = op[1:]
    return op.lower(), negated


def is_supported_operator(operator: str) -> bool:
    """True if *operator* (with optional leading ``!``/``@``) can be converted to SMT."""
    name, _ = _normalize_operator(operator)
    return name in _OPERATORS


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def rule_to_smt(rule: SecRule) -> SmtFormula:
    """Convert a single SecRule to an SmtFormula.

    Transformation actions (t:) are extracted and applied as SMT-LIB wrappers
    around each variable expression.  Uninterpreted transforms are declared and
    axiomatised in the formula preamble.

    Each ModSecurity variable becomes a free String constant.  Multiple
    variables produce a disjunctive assertion.

    Supported operators: @rx, @streq, @contains, @beginsWith, @endsWith,
    @within, @pm, @eq, @ge, @gt, @le, @lt (each with optional ``!`` negation).

    Raises:
        UnsupportedOperatorError: if the operator is not supported, or (for
            numeric operators) its argument is not an integer.
        UnsupportedTransformError: if a t: action is unknown.
    """
    op_name, op_negated = _normalize_operator(rule.operator)
    builder = _OPERATORS.get(op_name)
    if builder is None:
        raise UnsupportedOperatorError(
            f"Rule {rule.rule_id}: operator '{rule.operator}' is not supported"
        )

    negated = rule.negated or op_negated
    transforms = effective_transforms(rule)
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
        assertions.append(builder(var_expr, rule.operator_argument, negated))

    assertion = assertions[0] if len(assertions) == 1 else "(or " + " ".join(assertions) + ")"

    return SmtFormula(
        rule_id=rule.rule_id,
        fun_declarations=fun_decls,
        axioms=axioms,
        declarations=declarations,
        assertion=assertion,
    )


def chain_to_smt(chain: Sequence[SecRule]) -> SmtFormula:
    """Convert a chained sequence of @rx SecRules to a single SmtFormula.

    Each link's match condition is computed independently via
    rule_to_smt(); the chain as a whole matches only if every link
    matches (logical AND), mirroring ModSecurity's chained-rule semantics
    where a chained rule "fires" only if all of its links match the same
    request. Declarations, function declarations and axioms are merged
    across links, deduplicating identical entries (e.g. when multiple links
    reference the same ModSecurity variable or transform).

    Raises:
        UnsupportedOperatorError: if any link's operator is not supported.
        UnsupportedTransformError: if any link uses an unknown transform.
    """
    formulas = [rule_to_smt(rule) for rule in chain]

    declarations = _merge_unique([], [])
    fun_declarations: list[str] = []
    axioms: list[str] = []
    for f in formulas:
        declarations = _merge_unique(declarations, f.declarations)
        fun_declarations = _merge_unique(fun_declarations, f.fun_declarations)
        axioms = _merge_unique(axioms, f.axioms)

    if len(formulas) == 1:
        assertion = formulas[0].assertion
    else:
        assertion = "(and " + " ".join(f.assertion for f in formulas) + ")"

    return SmtFormula(
        rule_id=chain[0].rule_id,
        declarations=declarations,
        assertion=assertion,
        fun_declarations=fun_declarations,
        axioms=axioms,
    )


def _merge_unique(a: list[str], b: list[str]) -> list[str]:
    """Concatenate two lists, dropping duplicates from b that already appear in a."""
    seen = set(a)
    return a + [x for x in b if x not in seen]


def rules_to_smt(rules: Sequence[SecRule]) -> list[SmtFormula]:
    """Convert a sequence of SecRules to SmtFormulas, skipping unsupported operators."""
    result = []
    for rule in rules:
        if is_supported_operator(rule.operator):
            result.append(rule_to_smt(rule))
    return result
