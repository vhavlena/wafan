"""Intersection analysis.

IntersectionChecker detects pairs of rules (or chains) with a non-empty
intersection, i.e. there exists at least one input that triggers both
simultaneously.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ..parser import SecRule, group_chains
from ..smt import (
    SMT_LOGIC,
    SmtFormula,
    UnsupportedOperatorError,
    UnsupportedTransformError,
    _merge_unique,
    apply_transforms_smt,
    chain_to_smt,
    effective_transforms,
    is_supported_operator,
    transform_preamble,
)
from .common import (
    _all_supported,
    _chain_label,
    _operator_assertion,
    _print_smt_block,
    _rule_label,
    chains_share_variable,
    rules_share_variable,
)
from .solver import SolverBackend, SolverResult


# ---------------------------------------------------------------------------
# Intersection query generation
# ---------------------------------------------------------------------------

def intersection_smt2(rule1: SecRule, rule2: SecRule) -> str:
    """Return an SMT-LIB2 string that is SAT iff rule1 and rule2 have a
    non-empty intersection (some input triggers both rules simultaneously).

    Both rules' transformation chains are applied to the same free variable x.
    Uninterpreted transforms are declared and axiomatised in the preamble.

    Raises:
        UnsupportedTransformError: if either rule uses an unknown transform.
        UnsupportedOperatorError: if either rule's operator is not supported.
    """
    transforms1 = effective_transforms(rule1)
    transforms2 = effective_transforms(rule2)

    fd1, ax1 = transform_preamble(transforms1)
    fd2, ax2 = transform_preamble(transforms2)
    fun_decls = _merge_unique(fd1, fd2)
    axioms    = _merge_unique(ax1, ax2)

    var_expr1 = apply_transforms_smt("x", transforms1)
    var_expr2 = apply_transforms_smt("x", transforms2)

    assert1 = _operator_assertion(rule1, var_expr1)
    assert2 = _operator_assertion(rule2, var_expr2)

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; intersection check: rule {rule1.rule_id} ∩ rule {rule2.rule_id} ≠ ∅?",
        "; SAT => non-empty intersection  |  UNSAT => disjoint",
        *fun_decls,
        *axioms,
        "(declare-const x String)",
        f"(assert {assert1})",
        f"(assert {assert2})",
        "(check-sat)",
    ]
    return "\n".join(lines)


def chain_intersection_smt2(
    chain1: Sequence[SecRule],
    chain2: Sequence[SecRule],
    f1: SmtFormula | None = None,
    f2: SmtFormula | None = None,
) -> str:
    """Return an SMT-LIB2 string that is SAT iff chain1 and chain2 have a
    non-empty intersection (some input triggers both chains simultaneously).

    Each chain matches only if all of its links match (logical AND, see
    chain_to_smt). Declarations for ModSecurity variables shared by name
    between the two chains are merged, so both chains' conditions are
    evaluated against the same request.

    *f1*/*f2* may be precomputed chain_to_smt() results (e.g. shared across
    multiple pairwise comparisons); if omitted, they are computed here.

    Raises UnsupportedTransformError if any link uses an unknown transform.
    """
    f1 = f1 if f1 is not None else chain_to_smt(chain1)
    f2 = f2 if f2 is not None else chain_to_smt(chain2)

    declarations = _merge_unique(f1.declarations, f2.declarations)
    fun_decls = _merge_unique(f1.fun_declarations, f2.fun_declarations)
    axioms = _merge_unique(f1.axioms, f2.axioms)

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; chain intersection check: chain {chain1[0].rule_id} ∩ chain {chain2[0].rule_id} ≠ ∅?",
        "; SAT => non-empty intersection  |  UNSAT => disjoint",
        *fun_decls,
        *axioms,
        *declarations,
        f"(assert {f1.assertion})",
        f"(assert {f2.assertion})",
        "(check-sat)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Intersection checker
# ---------------------------------------------------------------------------

@dataclass
class IntersectionResult:
    """Outcome of checking whether rule1 and rule2 have a non-empty intersection."""

    rule1: SecRule
    rule2: SecRule
    result: SolverResult
    skipped: bool = False

    @property
    def has_intersection(self) -> bool:
        return self.result == SolverResult.SAT


@dataclass
class ChainIntersectionResult:
    """Outcome of checking whether chain1 and chain2 have a non-empty intersection."""

    chain1: list[SecRule]
    chain2: list[SecRule]
    result: SolverResult
    skipped: bool = False

    @property
    def has_intersection(self) -> bool:
        return self.result == SolverResult.SAT


class IntersectionChecker:
    """Check whether pairs of @rx SecRules share a non-empty intersection."""

    def __init__(self, solver: SolverBackend, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check_pair(self, rule1: SecRule, rule2: SecRule) -> IntersectionResult:
        """Check if there is an input that triggers both rule1 and rule2.

        Returns UNKNOWN if either rule uses an unsupported transform or if the
        rules target disjoint sets of variables.
        """
        lhs = _rule_label(rule1)
        rhs = _rule_label(rule2)
        prefix = f"  {lhs}  ∩  {rhs}"

        if not rules_share_variable(rule1, rule2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return IntersectionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True)

        try:
            smt2 = intersection_smt2(rule1, rule2)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return IntersectionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "INTERSECTING",
                SolverResult.UNSAT: "disjoint",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return IntersectionResult(rule1, rule2, result)

    def find_intersecting(self, rules: Sequence[SecRule]) -> list[IntersectionResult]:
        """Return all unordered pairs (R1, R2) whose intersection is non-empty.

        Only @rx / !@rx rules are considered.  Each unordered pair is checked
        once; pairs skipped due to disjoint variables or unsupported
        transforms are excluded, but pairs where the solver itself returns
        UNKNOWN (e.g. timeout) are kept with that result.
        """
        rx_rules = [r for r in rules if is_supported_operator(r.operator)]
        n = len(rx_rules)
        if self._verbosity >= 1:
            print(f"Intersection analysis: {n} rules, {n * (n - 1) // 2} unordered pairs\n")
        results: list[IntersectionResult] = []

        for i, r1 in enumerate(rx_rules):
            for r2 in rx_rules[i + 1:]:
                res = self.check_pair(r1, r2)
                if not res.skipped:
                    results.append(res)

        return results

    def check_chain_pair(
        self,
        chain1: Sequence[SecRule],
        chain2: Sequence[SecRule],
        f1: SmtFormula | None = None,
        f2: SmtFormula | None = None,
    ) -> ChainIntersectionResult:
        """Check if there is an input that triggers both chain1 and chain2.

        Returns UNKNOWN if either chain contains a non-@rx link, uses an
        unsupported transform, or the chains target disjoint sets of
        variables.

        *f1*/*f2* may be precomputed chain_to_smt() results for chain1/chain2
        (see find_intersecting_chains), avoiding recomputation across pairs.
        """
        chain1, chain2 = list(chain1), list(chain2)
        lhs = _chain_label(chain1)
        rhs = _chain_label(chain2)
        prefix = f"  {lhs}  ∩  {rhs}"

        if not _all_supported(chain1) or not _all_supported(chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported operator)")
            return ChainIntersectionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True)

        if not chains_share_variable(chain1, chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return ChainIntersectionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True)

        try:
            smt2 = chain_intersection_smt2(chain1, chain2, f1, f2)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return ChainIntersectionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "INTERSECTING",
                SolverResult.UNSAT: "disjoint",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return ChainIntersectionResult(chain1, chain2, result)

    def find_intersecting_chains(self, rules: Sequence[SecRule]) -> list[ChainIntersectionResult]:
        """Return all unordered pairs of chains whose intersection is non-empty.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own); only chains whose every link is @rx /
        !@rx are considered. Each unordered pair is checked once; pairs
        skipped due to disjoint variables or unsupported transforms are
        excluded, but pairs where the solver itself returns UNKNOWN (e.g.
        timeout) are kept with that result.
        """
        chains = group_chains(list(rules))
        n = len(chains)
        if self._verbosity >= 1:
            print(f"Chain intersection analysis: {n} chains, {n * (n - 1) // 2} unordered pairs\n")
        results: list[ChainIntersectionResult] = []

        formulas: list[SmtFormula | None] = []
        for chain in chains:
            try:
                formulas.append(chain_to_smt(chain) if _all_supported(chain) else None)
            except (UnsupportedTransformError, UnsupportedOperatorError):
                formulas.append(None)

        for i, c1 in enumerate(chains):
            for j, c2 in enumerate(chains[i + 1:], start=i + 1):
                res = self.check_chain_pair(c1, c2, formulas[i], formulas[j])
                if not res.skipped:
                    results.append(res)

        return results
