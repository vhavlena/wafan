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
from ..smt import SmtFormula, UnsupportedOperatorError, UnsupportedTransformError, chain_to_smt, is_supported_operator
from .common import _all_supported, _chain_label, _print_smt_block, _rule_label, chain_disposition, intersection_outcome_label, rule_disposition
from .intersection import (
    ChainIntersectionResult,
    IntersectionChecker,
    IntersectionResult,
    chain_intersection_smt2,
    intersection_smt2,
)
from .solver import SolverBackend

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
    """Outcome of checking whether rule1 and rule2 intersect and contradict.

    Wraps the IntersectionResult of the identical SAT/UNSAT query
    IntersectionChecker performs (rule1/rule2/result/skipped/skip_reason/
    elapsed_sec/error/has_intersection all delegate to it via __getattr__)
    and adds only the accept/deny disposition check.
    """

    base: IntersectionResult

    def __getattr__(self, name: str):
        return getattr(self.base, name)

    @property
    def is_contradiction(self) -> bool:
        return self.base.has_intersection and {rule_disposition(self.base.rule1), rule_disposition(self.base.rule2)} == {"allow", "deny"}


@dataclass
class ChainContradictionResult:
    """Outcome of checking whether chain1 and chain2 intersect and contradict.

    Wraps the ChainIntersectionResult of the identical SAT/UNSAT query
    IntersectionChecker performs (chain1/chain2/result/skipped/skip_reason/
    elapsed_sec/error/has_intersection all delegate to it via __getattr__)
    and adds only the accept/deny disposition check.
    """

    base: ChainIntersectionResult

    def __getattr__(self, name: str):
        return getattr(self.base, name)

    @property
    def is_contradiction(self) -> bool:
        return self.base.has_intersection and {chain_disposition(self.base.chain1), chain_disposition(self.base.chain2)} == {"allow", "deny"}


class ContradictionChecker:
    """Check whether pairs of @rx SecRules intersect and disagree on accept/deny."""

    def __init__(self, solver: SolverBackend, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity
        self._intersection = IntersectionChecker(solver, verbosity=0)

    def _print_outcome(self, prefix: str, res: "ContradictionResult | ChainContradictionResult") -> None:
        if self._verbosity < 1:
            return
        if res.skipped:
            print(f"{prefix}  [{'skipped':<13}]  ({res.skip_reason})")
        else:
            outcome = "CONTRADICTION" if res.is_contradiction else intersection_outcome_label(res.result)
            print(f"{prefix}  [{outcome:<13}]")

    def check_pair(self, rule1: SecRule, rule2: SecRule) -> ContradictionResult:
        """Check if there is an input that triggers both rule1 and rule2 while
        the two rules disagree on whether to accept or deny it.

        Returns UNKNOWN if either rule uses an unsupported transform or if the
        rules target disjoint sets of variables.
        """
        prefix = f"  {_rule_label(rule1)}  ⨯  {_rule_label(rule2)}"
        res = ContradictionResult(self._intersection.check_pair(rule1, rule2))
        self._print_outcome(prefix, res)
        if self._verbosity >= 2 and not res.skipped:
            _print_smt_block(contradiction_smt2(rule1, rule2))
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
        supported1: bool | None = None,
        supported2: bool | None = None,
    ) -> ChainContradictionResult:
        """Check if there is an input that triggers both chain1 and chain2 while
        the two chains disagree on whether to accept or deny it.

        Returns UNKNOWN if either chain contains a non-@rx link, uses an
        unsupported transform, or the chains target disjoint sets of
        variables.

        *f1*/*f2* may be precomputed chain_to_smt() results, and
        *supported1*/*supported2* precomputed _all_supported() results, for
        chain1/chain2 (see find_contradicting_chains), avoiding recomputation
        across pairs.
        """
        chain1, chain2 = list(chain1), list(chain2)
        prefix = f"  {_chain_label(chain1)}  ⨯  {_chain_label(chain2)}"
        res = ChainContradictionResult(
            self._intersection.check_chain_pair(chain1, chain2, f1, f2, supported1, supported2)
        )
        self._print_outcome(prefix, res)
        if self._verbosity >= 2 and not res.skipped:
            _print_smt_block(chain_contradiction_smt2(chain1, chain2, f1, f2))
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

        supported: list[bool] = [_all_supported(chain) for chain in chains]
        formulas: list[SmtFormula | None] = []
        for chain, chain_supported in zip(chains, supported):
            try:
                formulas.append(chain_to_smt(chain) if chain_supported else None)
            except (UnsupportedTransformError, UnsupportedOperatorError):
                formulas.append(None)

        for i, c1 in enumerate(chains):
            for j, c2 in enumerate(chains[i + 1:], start=i + 1):
                res = self.check_chain_pair(c1, c2, formulas[i], formulas[j], supported[i], supported[j])
                if on_result is not None:
                    on_result(res)
                if include_skipped or not res.skipped:
                    results.append(res)

        return results
