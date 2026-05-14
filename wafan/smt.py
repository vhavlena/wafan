"""Convert SecRule conditions to SMT-LIB2 format.

Currently only @rx (ECMA regex matching) is supported via the
`re.from_ecma2020` SMT-LIB function, targeting the z3-noodler backend.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .parser import SecRule, SecRuleVariable


SMT_LOGIC = "QF_SLIA"


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


def _smt_var_name(variable: SecRuleVariable) -> str:
    """Produce a sanitised SMT identifier for a ModSecurity variable."""
    name = variable.name
    if variable.part:
        name = f"{name}__{variable.part}"
    return name.replace("-", "_").replace(".", "_").replace(":", "_")


def _escape_smt_string(pattern: str) -> str:
    """Escape a regex pattern for embedding in an SMT-LIB2 string literal."""
    return pattern.replace("\\", "\\\\").replace('"', '\\"')


def _rx_assertion(var_name: str, pattern: str, negated: bool) -> str:
    escaped = _escape_smt_string(pattern)
    inner = f'(str.in_re {var_name} (re.from_ecma2020 "{escaped}"))'
    return f"(not {inner})" if negated else inner


def rx_rule_to_smt(rule: SecRule) -> SmtFormula:
    """Convert a single @rx SecRule to an SmtFormula.

    Each ModSecurity variable targeted by the rule becomes a free String
    constant.  When a rule targets multiple variables the assertion is a
    disjunction (any variable matching triggers the rule).

    Raises ValueError for rules whose operator is not @rx / !@rx.
    """
    if rule.operator not in ("@rx", "!@rx"):
        raise ValueError(
            f"Rule {rule.rule_id}: operator '{rule.operator}' is not @rx"
        )

    negated = rule.negated or rule.operator == "!@rx"
    pattern = rule.operator_argument

    declarations: list[str] = []
    var_names: list[str] = []
    seen: set[str] = set()

    for variable in rule.variables:
        v = _smt_var_name(variable)
        if v not in seen:
            declarations.append(f"(declare-const {v} String)")
            seen.add(v)
        var_names.append(v)

    if len(var_names) == 1:
        assertion = _rx_assertion(var_names[0], pattern, negated)
    else:
        parts = [_rx_assertion(v, pattern, negated) for v in var_names]
        inner = "(or " + " ".join(parts) + ")"
        assertion = inner

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
