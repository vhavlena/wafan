"""Convert SecRule conditions to SMT-LIB2 format.

Currently only @rx (ECMA regex matching) is supported via the
`re.from_ecma2020` SMT-LIB function, targeting the z3-noodler backend.

Supported SecRule transformations (t: actions) that have direct SMT-LIB
counterparts are applied inline as wrappers around the variable expression:
  none            – resets the transform chain (identity)
  lowercase       – str.lower
  uppercase       – str.upper

Transforms without SMT-LIB counterparts raise UnsupportedTransformError.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

from .parser import SecRule, SecRuleAction, SecRuleVariable


SMT_LOGIC = "QF_SLIA"

# Maps normalised transform name → function that wraps an SMT expression.
# "none" is handled separately (it resets the chain) and is not in this map.
_TRANSFORM_SMT: dict[str, Callable[[str], str]] = {
    "lowercase": lambda e: f"(str.lower {e})",
    "uppercase": lambda e: f"(str.upper {e})",
}


class UnsupportedTransformError(Exception):
    """Raised when a SecRule transformation has no SMT-LIB counterpart."""


@dataclass
class SmtFormula:
    """SMT-LIB2 representation of a single SecRule condition."""

    rule_id: str
    declarations: list[str]
    assertion: str

    def to_smt2(self) -> str:
        """Render a self-contained, check-sat-ready SMT-LIB2 string."""
        lines = [
            f"(set-logic {SMT_LOGIC})",
            f"; rule id:{self.rule_id}",
            *self.declarations,
            f"(assert {self.assertion})",
            "(check-sat)",
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
    ``[lowercase, uppercase]`` produces ``(str.upper (str.lower var))``.

    Raises UnsupportedTransformError for any transform not in _TRANSFORM_SMT.
    """
    expr = var_expr
    for t in transforms:
        key = t.lower()
        fn = _TRANSFORM_SMT.get(key)
        if fn is None:
            raise UnsupportedTransformError(
                f"Transform '{t}' has no SMT-LIB counterpart"
            )
        expr = fn(expr)
    return expr


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
    around each variable expression before the regex assertion is built.

    Each ModSecurity variable targeted by the rule becomes a free String
    constant.  When a rule targets multiple variables the assertion is a
    disjunction (any variable matching triggers the rule).

    Raises:
        ValueError: if the operator is not @rx / !@rx.
        UnsupportedTransformError: if a t: action has no SMT-LIB counterpart.
    """
    if rule.operator not in ("@rx", "!@rx"):
        raise ValueError(
            f"Rule {rule.rule_id}: operator '{rule.operator}' is not @rx"
        )

    negated = rule.negated or rule.operator == "!@rx"
    pattern = rule.operator_argument
    transforms = extract_transforms(rule.actions)

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

    if len(assertions) == 1:
        assertion = assertions[0]
    else:
        assertion = "(or " + " ".join(assertions) + ")"

    return SmtFormula(
        rule_id=rule.rule_id,
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
