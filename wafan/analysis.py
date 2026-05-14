"""SMT-based analysis of ModSecurity SecRule rulesets.

Currently implemented analysis:
  SubsumptionChecker – detects pairs of @rx rules where one rule's match
  condition is a subset of another's (rule1 subsumed by rule2 means every
  input triggering rule1 also triggers rule2).

The module is solver-agnostic: any object implementing SolverBackend can be
supplied.  SubprocessSolver calls an external binary (default: z3-noodler)
via stdin/stdout using the SMT-LIB2 format produced by wafan.smt.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from enum import Enum
from typing import Protocol, Sequence

from .parser import SecRule, SecRuleVariable
from .smt import (
    SMT_LOGIC,
    UnsupportedTransformError,
    _escape_smt_string,
    apply_transforms_smt,
    extract_transforms,
)


# ---------------------------------------------------------------------------
# Solver abstraction
# ---------------------------------------------------------------------------

class SolverResult(Enum):
    SAT = "sat"        # counterexample found → not subsumed
    UNSAT = "unsat"    # no counterexample   → subsumed
    UNKNOWN = "unknown"


class SolverBackend(Protocol):
    """Minimal interface for an SMT solver backend."""

    def solve(self, smt2: str) -> SolverResult: ...


class SubprocessSolver:
    """Call an external SMT solver (e.g. z3-noodler) via stdin/stdout."""

    def __init__(self, argv: list[str] | None = None, timeout: int = 30) -> None:
        self.argv = argv or ["z3", "-in"]
        self.timeout = timeout

    def solve(self, smt2: str) -> SolverResult:
        try:
            proc = subprocess.run(
                self.argv,
                input=smt2,
                capture_output=True,
                text=True,
                timeout=self.timeout,
            )
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return SolverResult.UNKNOWN

        first = proc.stdout.strip().splitlines()[0] if proc.stdout.strip() else ""
        try:
            return SolverResult(first)
        except ValueError:
            return SolverResult.UNKNOWN


# ---------------------------------------------------------------------------
# Subsumption query generation
# ---------------------------------------------------------------------------

def _match_assertion(var_expr: str, pattern: str, negated: bool) -> str:
    escaped = _escape_smt_string(pattern)
    atom = f'(str.in_re {var_expr} (re.from_ecma2020 "{escaped}"))'
    return f"(not {atom})" if negated else atom


def subsumption_smt2(rule1: SecRule, rule2: SecRule) -> str:
    """Return an SMT-LIB2 string that is UNSAT iff rule1 is subsumed by rule2.

    The query asks: does there exist an input x that triggers rule1 but NOT
    rule2?  If UNSAT, no such x exists, so rule1 ⊆ rule2.

    Both rules' transformation chains are applied to the same free variable x,
    so transforms are correctly reflected in the subsumption condition.

    Raises UnsupportedTransformError if either rule uses a transform without
    an SMT-LIB counterpart.
    """
    transforms1 = extract_transforms(rule1.actions)
    transforms2 = extract_transforms(rule2.actions)

    negated1 = rule1.negated or rule1.operator == "!@rx"
    negated2 = rule2.negated or rule2.operator == "!@rx"

    var_expr1 = apply_transforms_smt("x", transforms1)
    var_expr2 = apply_transforms_smt("x", transforms2)

    # rule1 triggers for x
    assert1 = _match_assertion(var_expr1, rule1.operator_argument, negated1)
    # rule2 does NOT trigger for x  (counterexample condition)
    assert2_triggers = _match_assertion(var_expr2, rule2.operator_argument, negated2)
    assert2 = f"(not {assert2_triggers})"

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; subsumption check: rule {rule1.rule_id} subsumed by rule {rule2.rule_id}?",
        "; UNSAT => subsumed  |  SAT => not subsumed (witness exists)",
        "(declare-const x String)",
        f"(assert {assert1})",
        f"(assert {assert2})",
        "(check-sat)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Variable compatibility
# ---------------------------------------------------------------------------

def _variable_names(rule: SecRule) -> frozenset[str]:
    return frozenset(v.name for v in rule.variables)


def rules_share_variable(rule1: SecRule, rule2: SecRule) -> bool:
    """True if both rules target at least one common ModSecurity variable."""
    return bool(_variable_names(rule1) & _variable_names(rule2))


# ---------------------------------------------------------------------------
# Subsumption checker
# ---------------------------------------------------------------------------

@dataclass
class SubsumptionResult:
    """Outcome of checking whether rule1 is subsumed by rule2."""

    rule1: SecRule
    rule2: SecRule
    result: SolverResult

    @property
    def is_subsumed(self) -> bool:
        return self.result == SolverResult.UNSAT


class SubsumptionChecker:
    """Check subsumption between pairs of @rx SecRules using an SMT solver."""

    def __init__(self, solver: SolverBackend) -> None:
        self._solver = solver

    def check_pair(self, rule1: SecRule, rule2: SecRule) -> SubsumptionResult:
        """Check if rule1 is subsumed by rule2.

        Returns UNKNOWN if either rule uses an unsupported transform or if the
        rules target disjoint sets of variables.
        """
        if not rules_share_variable(rule1, rule2):
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN)

        try:
            smt2 = subsumption_smt2(rule1, rule2)
        except UnsupportedTransformError:
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN)

        result = self._solver.solve(smt2)
        return SubsumptionResult(rule1, rule2, result)

    def find_subsumed(self, rules: Sequence[SecRule]) -> list[SubsumptionResult]:
        """Return all ordered pairs (R1, R2) where R1 is subsumed by R2.

        Only @rx / !@rx rules are considered.  All ordered pairs with distinct
        rule ids are checked; pairs where the solver returns UNKNOWN are
        excluded from the result.
        """
        rx_rules = [r for r in rules if r.operator in ("@rx", "!@rx")]
        results: list[SubsumptionResult] = []

        for i, r1 in enumerate(rx_rules):
            for j, r2 in enumerate(rx_rules):
                if i == j:
                    continue
                res = self.check_pair(r1, r2)
                if res.result != SolverResult.UNKNOWN:
                    results.append(res)

        return results
