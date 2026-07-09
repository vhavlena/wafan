"""Contradiction analysis.

ContradictionChecker builds on IntersectionChecker: it detects pairs of rules
(or chains) that not only share a non-empty intersection (some input triggers
both simultaneously), but also disagree on the disruptive action taken for
that input — one rule accepts it (``allow``/``pass``) while the other denies
it (``deny``/``drop``/``block``). Such a pair is a genuine contradiction: the
same request is both let through and blocked, depending on which rule "wins".
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

from ..parser import SecRule, group_chains
from ..smt import (
    SmtFormula,
    UnsupportedOperatorError,
    UnsupportedTransformError,
    chain_to_smt,
    is_supported_operator,
)
from .common import (
    _all_supported,
    _chain_label,
    _print_smt_block,
    _rule_label,
    chain_disposition,
    chains_share_variable,
    rule_disposition,
    rules_share_variable,
)
from .intersection import chain_intersection_smt2, intersection_smt2
from .solver import SolverBackend, SolverResult

# ---------------------------------------------------------------------------
# Contradiction query generation (identical to intersection: the accept/deny
# disagreement is a property of the rules' actions, not of the SMT query)
# ---------------------------------------------------------------------------

def contradiction_smt2(rule1: SecRule, rule2: SecRule) -> str:
    """Return an SMT-LIB2 string that is SAT iff rule1 and rule2 have a
    non-empty intersection (some input triggers both rules simultaneously).

    Identical to intersection_smt2(): whether that shared input constitutes a
    contradiction (one rule accepts it, the other denies it) is determined
    separately from each rule's actions, see ContradictionChecker.
    """
    return intersection_smt2(rule1, rule2)


def chain_contradiction_smt2(
    chain1: Sequence[SecRule],
    chain2: Sequence[SecRule],
    f1: SmtFormula | None = None,
    f2: SmtFormula | None = None,
) -> str:
    """Chain analogue of contradiction_smt2(); identical to chain_intersection_smt2()."""
    return chain_intersection_smt2(chain1, chain2, f1, f2)


# ---------------------------------------------------------------------------
# Contradiction checker
# ---------------------------------------------------------------------------

@dataclass
class ContradictionResult:
    """Outcome of checking whether rule1 and rule2 intersect and contradict."""

    rule1: SecRule
    rule2: SecRule
    result: SolverResult
    skipped: bool = False
    skip_reason: str = ""
    elapsed_sec: float = 0.0
    error: str = ""

    @property
    def has_intersection(self) -> bool:
        return self.result == SolverResult.SAT

    @property
    def is_contradiction(self) -> bool:
        return self.has_intersection and {rule_disposition(self.rule1), rule_disposition(self.rule2)} == {"allow", "deny"}


@dataclass
class ChainContradictionResult:
    """Outcome of checking whether chain1 and chain2 intersect and contradict."""

    chain1: list[SecRule]
    chain2: list[SecRule]
    result: SolverResult
    skipped: bool = False
    skip_reason: str = ""
    elapsed_sec: float = 0.0
    error: str = ""

    @property
    def has_intersection(self) -> bool:
        return self.result == SolverResult.SAT

    @property
    def is_contradiction(self) -> bool:
        return self.has_intersection and {chain_disposition(self.chain1), chain_disposition(self.chain2)} == {"allow", "deny"}


class ContradictionChecker:
    """Check whether pairs of @rx SecRules intersect and disagree on accept/deny."""

    def __init__(self, solver: SolverBackend, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check_pair(self, rule1: SecRule, rule2: SecRule) -> ContradictionResult:
        """Check if there is an input that triggers both rule1 and rule2 while
        the two rules disagree on whether to accept or deny it.

        Returns UNKNOWN if either rule uses an unsupported transform or if the
        rules target disjoint sets of variables.
        """
        lhs = _rule_label(rule1)
        rhs = _rule_label(rule2)
        prefix = f"  {lhs}  ⨯  {rhs}"

        if not rules_share_variable(rule1, rule2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<13}]  (no shared variable)")
            return ContradictionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True, skip_reason="no shared variable")

        try:
            smt2 = contradiction_smt2(rule1, rule2)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<13}]  (unsupported transform: {exc})")
            return ContradictionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True, skip_reason=str(exc))

        result = self._solver.solve(smt2)
        res = ContradictionResult(
            rule1, rule2, result,
            elapsed_sec=getattr(self._solver, "last_elapsed_sec", 0.0),
            error=getattr(self._solver, "last_error_text", "") if result == SolverResult.UNKNOWN else "",
        )
        if self._verbosity >= 1:
            outcome = "CONTRADICTION" if res.is_contradiction else {
                SolverResult.SAT: "intersecting",
                SolverResult.UNSAT: "disjoint",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<13}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return res

    def find_contradicting(self, rules: Sequence[SecRule]) -> list[ContradictionResult]:
        """Return all unordered pairs (R1, R2) that intersect and contradict.

        Only @rx / !@rx rules are considered.  Each unordered pair is checked
        once; pairs skipped due to disjoint variables or unsupported
        transforms are excluded, but pairs where the solver itself returns
        UNKNOWN (e.g. timeout) are kept with that result.
        """
        rx_rules = [r for r in rules if is_supported_operator(r.operator)]
        n = len(rx_rules)
        if self._verbosity >= 1:
            print(f"Contradiction analysis: {n} rules, {n * (n - 1) // 2} unordered pairs\n")
        results: list[ContradictionResult] = []

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
    ) -> ChainContradictionResult:
        """Check if there is an input that triggers both chain1 and chain2 while
        the two chains disagree on whether to accept or deny it.

        Returns UNKNOWN if either chain contains a non-@rx link, uses an
        unsupported transform, or the chains target disjoint sets of
        variables.

        *f1*/*f2* may be precomputed chain_to_smt() results for chain1/chain2
        (see find_contradicting_chains), avoiding recomputation across pairs.
        """
        chain1, chain2 = list(chain1), list(chain2)
        lhs = _chain_label(chain1)
        rhs = _chain_label(chain2)
        prefix = f"  {lhs}  ⨯  {rhs}"

        if not _all_supported(chain1) or not _all_supported(chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<13}]  (unsupported operator)")
            return ChainContradictionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True, skip_reason="unsupported operator")

        if not chains_share_variable(chain1, chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<13}]  (no shared variable)")
            return ChainContradictionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True, skip_reason="no shared variable")

        try:
            smt2 = chain_contradiction_smt2(chain1, chain2, f1, f2)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<13}]  (unsupported transform: {exc})")
            return ChainContradictionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True, skip_reason=str(exc))

        result = self._solver.solve(smt2)
        res = ChainContradictionResult(
            chain1, chain2, result,
            elapsed_sec=getattr(self._solver, "last_elapsed_sec", 0.0),
            error=getattr(self._solver, "last_error_text", "") if result == SolverResult.UNKNOWN else "",
        )
        if self._verbosity >= 1:
            outcome = "CONTRADICTION" if res.is_contradiction else {
                SolverResult.SAT: "intersecting",
                SolverResult.UNSAT: "disjoint",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<13}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return res

    def find_contradicting_chains(
        self,
        rules: Sequence[SecRule],
        include_skipped: bool = False,
        on_result: "Callable[[ChainContradictionResult], None] | None" = None,
    ) -> list[ChainContradictionResult]:
        """Return all unordered pairs of chains that intersect and contradict.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own); only chains whose every link is @rx /
        !@rx are considered. Each unordered pair is checked once; by
        default, pairs skipped due to disjoint variables or unsupported
        transforms are excluded, but pairs where the solver itself returns
        UNKNOWN (e.g. timeout) are kept with that result. Pass
        ``include_skipped=True`` to get every checked pair back, including
        skipped ones (with ``skipped=True`` and ``skip_reason`` set).

        *on_result*, if given, is called with each ChainContradictionResult
        (including skipped ones) as soon as it is computed, before the
        method returns — so a caller can stream/persist partial progress.
        """
        chains = group_chains(list(rules))
        n = len(chains)
        if self._verbosity >= 1:
            print(f"Chain contradiction analysis: {n} chains, {n * (n - 1) // 2} unordered pairs\n")
        results: list[ChainContradictionResult] = []

        formulas: list[SmtFormula | None] = []
        for chain in chains:
            try:
                formulas.append(chain_to_smt(chain) if _all_supported(chain) else None)
            except (UnsupportedTransformError, UnsupportedOperatorError):
                formulas.append(None)

        for i, c1 in enumerate(chains):
            for j, c2 in enumerate(chains[i + 1:], start=i + 1):
                res = self.check_chain_pair(c1, c2, formulas[i], formulas[j])
                if on_result is not None:
                    on_result(res)
                if include_skipped or not res.skipped:
                    results.append(res)

        return results
