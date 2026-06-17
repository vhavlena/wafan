"""Subsumption analysis.

SubsumptionChecker detects pairs where one rule's (or chain's) match
condition is a subset of another's (rule1 subsumed by rule2 means every
input triggering rule1 also triggers rule2).
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
# Subsumption query generation
# ---------------------------------------------------------------------------

def subsumption_smt2(rule1: SecRule, rule2: SecRule) -> str:
    """Return an SMT-LIB2 string that is UNSAT iff rule1 is subsumed by rule2.

    The query asks: does there exist an input x that triggers rule1 but NOT
    rule2?  If UNSAT, no such x exists, so rule1 ⊆ rule2.

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
    assert2 = f"(not {_operator_assertion(rule2, var_expr2)})"

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; subsumption check: rule {rule1.rule_id} subsumed by rule {rule2.rule_id}?",
        "; UNSAT => subsumed  |  SAT => not subsumed (witness exists)",
        *fun_decls,
        *axioms,
        "(declare-const x String)",
        f"(assert {assert1})",
        f"(assert {assert2})",
        "(check-sat)",
    ]
    return "\n".join(lines)


def chain_subsumption_smt2(
    chain1: Sequence[SecRule],
    chain2: Sequence[SecRule],
    f1: SmtFormula | None = None,
    f2: SmtFormula | None = None,
) -> str:
    """Return an SMT-LIB2 string that is UNSAT iff chain1 is subsumed by chain2.

    Each chain matches only if all of its links match (logical AND, see
    chain_to_smt). The query asks: does there exist an input that satisfies
    chain1's conjunction but not chain2's?  If UNSAT, chain1 ⊆ chain2.

    Declarations for ModSecurity variables shared by name between the two
    chains are merged, so both chains' conditions are evaluated against the
    same request.

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
        f"; chain subsumption check: chain {chain1[0].rule_id} subsumed by chain {chain2[0].rule_id}?",
        "; UNSAT => subsumed  |  SAT => not subsumed (witness exists)",
        *fun_decls,
        *axioms,
        *declarations,
        f"(assert {f1.assertion})",
        f"(assert (not {f2.assertion}))",
        "(check-sat)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Subsumption checker
# ---------------------------------------------------------------------------

@dataclass
class SubsumptionResult:
    """Outcome of checking whether rule1 is subsumed by rule2."""

    rule1: SecRule
    rule2: SecRule
    result: SolverResult
    skipped: bool = False

    @property
    def is_subsumed(self) -> bool:
        return self.result == SolverResult.UNSAT


@dataclass
class ChainSubsumptionResult:
    """Outcome of checking whether chain1 is subsumed by chain2."""

    chain1: list[SecRule]
    chain2: list[SecRule]
    result: SolverResult
    skipped: bool = False

    @property
    def is_subsumed(self) -> bool:
        return self.result == SolverResult.UNSAT


class SubsumptionChecker:
    """Check subsumption between pairs of @rx SecRules using an SMT solver."""

    def __init__(self, solver: SolverBackend, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check_pair(self, rule1: SecRule, rule2: SecRule) -> SubsumptionResult:
        """Check if rule1 is subsumed by rule2.

        Returns UNKNOWN if either rule uses an unsupported transform or if the
        rules target disjoint sets of variables.
        """
        lhs = _rule_label(rule1)
        rhs = _rule_label(rule2)
        prefix = f"  {lhs}  ⊆  {rhs}"

        if not rules_share_variable(rule1, rule2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True)

        try:
            smt2 = subsumption_smt2(rule1, rule2)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.UNSAT: "SUBSUMED",
                SolverResult.SAT: "not subsumed",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return SubsumptionResult(rule1, rule2, result)

    def find_subsumed(self, rules: Sequence[SecRule]) -> list[SubsumptionResult]:
        """Return all ordered pairs (R1, R2) where R1 is subsumed by R2.

        Only @rx / !@rx rules are considered.  All ordered pairs with distinct
        rule ids are checked; pairs skipped due to disjoint variables or
        unsupported transforms are excluded, but pairs where the solver
        itself returns UNKNOWN (e.g. timeout) are kept with that result.
        """
        rx_rules = [r for r in rules if is_supported_operator(r.operator)]
        n = len(rx_rules)
        if self._verbosity >= 1:
            print(f"Subsumption analysis: {n} rules, {n * (n - 1)} ordered pairs\n")
        results: list[SubsumptionResult] = []

        for i, r1 in enumerate(rx_rules):
            for j, r2 in enumerate(rx_rules):
                if i == j:
                    continue
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
    ) -> ChainSubsumptionResult:
        """Check if chain1 is subsumed by chain2.

        Returns UNKNOWN if either chain contains a non-@rx link, uses an
        unsupported transform, or the chains target disjoint sets of
        variables.

        *f1*/*f2* may be precomputed chain_to_smt() results for chain1/chain2
        (see find_subsumed_chains), avoiding recomputation across pairs.
        """
        chain1, chain2 = list(chain1), list(chain2)
        lhs = _chain_label(chain1)
        rhs = _chain_label(chain2)
        prefix = f"  {lhs}  ⊆  {rhs}"

        if not _all_supported(chain1) or not _all_supported(chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported operator)")
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True)

        if not chains_share_variable(chain1, chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True)

        try:
            smt2 = chain_subsumption_smt2(chain1, chain2, f1, f2)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.UNSAT: "SUBSUMED",
                SolverResult.SAT: "not subsumed",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return ChainSubsumptionResult(chain1, chain2, result)

    def find_subsumed_chains(self, rules: Sequence[SecRule]) -> list[ChainSubsumptionResult]:
        """Return all ordered pairs of chains where chain1 is subsumed by chain2.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own); only chains whose every link is @rx /
        !@rx are considered. All ordered pairs of distinct chains are
        checked; pairs skipped due to disjoint variables or unsupported
        transforms are excluded, but pairs where the solver itself returns
        UNKNOWN (e.g. timeout) are kept with that result.
        """
        chains = group_chains(list(rules))
        n = len(chains)
        if self._verbosity >= 1:
            print(f"Chain subsumption analysis: {n} chains, {n * (n - 1)} ordered pairs\n")
        results: list[ChainSubsumptionResult] = []

        formulas: list[SmtFormula | None] = []
        for chain in chains:
            try:
                formulas.append(chain_to_smt(chain) if _all_supported(chain) else None)
            except (UnsupportedTransformError, UnsupportedOperatorError):
                formulas.append(None)

        for i, c1 in enumerate(chains):
            for j, c2 in enumerate(chains):
                if i == j:
                    continue
                res = self.check_chain_pair(c1, c2, formulas[i], formulas[j])
                if not res.skipped:
                    results.append(res)

        return results
