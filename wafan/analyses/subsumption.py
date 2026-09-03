"""Subsumption analysis.

SubsumptionChecker detects pairs where one rule's (or chain's) match
condition is a subset of another's (rule1 subsumed by rule2 means every
input triggering rule1 also triggers rule2).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

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
)
from .common import (
    _all_supported,
    _chain_label,
    _joint_transform_preamble,
    _operator_assertion,
    _print_smt_block,
    _rule_label,
    chain_escaping_witness,
    chains_share_target,
    rules_share_variable,
    solve_any,
    solver_timed_out,
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

    fun_decls, axioms = _joint_transform_preamble([rule1], [rule2])

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


def subsumption_alternatives(
    chain1: Sequence[SecRule],
    chain2: Sequence[SecRule],
    f1: SmtFormula,
    f2: SmtFormula,
) -> list[str]:
    """The ways ``chain1 subsumed by chain2`` can fail, as a disjunction.

    Either chain2 does not fire where chain1 does, or it does not match a
    member chain1 matched. A single escaping term equal to ``chain1 and not
    chain2`` is dropped: with one shared address that is what the first
    disjunct already says under chain1's asserted condition.
    """
    refused = f"(not {f2.assertion})"
    escaping = chain_escaping_witness(chain1, chain2)
    if len(escaping) == 1 and escaping[0] == f"(and {f1.assertion} {refused})":
        return [refused]
    return [refused, *escaping]


def chain_subsumption_smt2(
    chain1: Sequence[SecRule],
    chain2: Sequence[SecRule],
    f1: SmtFormula | None = None,
    f2: SmtFormula | None = None,
    alternatives: Sequence[str] | None = None,
) -> str:
    """Return an SMT-LIB2 string that is UNSAT iff chain1 is subsumed by chain2.

    Subsumption is containment of witnesses: chain2 matches every member
    chain1 matches, which is what makes chain1 redundant. So the refutation
    asks for either of the two ways it can fail --- an input satisfying
    chain1's conjunction but not chain2's, or an address at which chain1
    matches and chain2 does not (see
    :func:`~wafan.analyses.common.chain_escaping_witness`). Each chain matches
    only if all of its links match (logical AND, see chain_to_smt), and both
    conditions are evaluated against one request, the two sides sharing the
    address symbols of every collection they both read.

    Containment is asked at the targets both chains read: a collection chain2
    never looks at is no evidence that it misses anything, and counting it
    would leave a chain guarded on ``TX:flag`` un-subsumable by the plain rule
    whose pattern it repeats. Whether the pair shares a target at all is
    settled before the query is built --- with none, containment is vacuous
    and what is left is chain1's own satisfiability.

    *f1*/*f2* may be precomputed chain_to_smt() results (e.g. shared across
    multiple pairwise comparisons); if omitted, they are computed here. Their
    ``fun_declarations``/``axioms`` are not reused directly (each chain may
    have restricted a shared transform to its own, different codepoint set),
    only their ``declarations``/``assertion``, which don't depend on that
    restriction; the function preamble is always recomputed jointly for the
    pair (see ``_joint_transform_preamble``) so that a transform shared by
    both chains gets exactly one, consistent declaration.

    *alternatives* restricts the refutation to the given disjuncts, which is
    how a caller asks about one of them at a time when the solver cannot
    decide the whole disjunction --- and a refined refutation usually needs
    that, a negated regex membership under a disjunction being where
    z3-noodler gives up (see :func:`~wafan.analyses.common.solve_any`). By
    default it is chain2 failing to fire, plus one escaping term per target
    both chains read.

    Raises UnsupportedTransformError if any link uses an unknown transform.
    """
    f1 = f1 if f1 is not None else chain_to_smt(chain1)
    f2 = f2 if f2 is not None else chain_to_smt(chain2)
    if alternatives is None:
        alternatives = subsumption_alternatives(chain1, chain2, f1, f2)

    declarations = _merge_unique(f1.declarations, f2.declarations)
    fun_decls, axioms = _joint_transform_preamble(chain1, chain2)

    refutation = (
        alternatives[0] if len(alternatives) == 1
        else "(or " + " ".join(alternatives) + ")"
    )

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; chain subsumption check: chain {chain1[0].rule_id} subsumed by chain {chain2[0].rule_id}?",
        "; UNSAT => subsumed  |  SAT => not subsumed (witness exists)",
        *fun_decls,
        *axioms,
        *declarations,
        f"(assert {f1.assertion})",
        f"(assert {refutation})",
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
    skip_reason: str = ""
    elapsed_sec: float = 0.0
    error: str = ""

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
    skip_reason: str = ""
    elapsed_sec: float = 0.0
    error: str = ""

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
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True, skip_reason="no shared variable")

        try:
            smt2 = subsumption_smt2(rule1, rule2)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN, skipped=True, skip_reason=str(exc))

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
        return SubsumptionResult(
            rule1, rule2, result,
            elapsed_sec=getattr(self._solver, "last_elapsed_sec", 0.0),
            error=getattr(self._solver, "last_error_text", "") if result == SolverResult.UNKNOWN else "",
        )

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
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True, skip_reason="unsupported operator")

        if not chains_share_target(chain1, chain2):
            # With no target in common there is nothing to contain: the
            # query would degenerate into chain1's own satisfiability (with
            # disjoint symbols, `F1 => F2` is valid iff F1 is unsatisfiable
            # or F2 valid), so what is left is a dead-code question about one
            # rule and not a relation between the pair. Reported as skipped
            # rather than as a subsumption, so a dead chain doesn't come out
            # "redundant" given every unrelated rule.
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no common target)")
            return ChainSubsumptionResult(
                chain1, chain2, SolverResult.UNKNOWN,
                skipped=True,
                skip_reason="no common target: subsumption could only hold degenerately",
            )

        try:
            f1 = f1 if f1 is not None else chain_to_smt(chain1)
            f2 = f2 if f2 is not None else chain_to_smt(chain2)
            alternatives = subsumption_alternatives(chain1, chain2, f1, f2)
            smt2 = chain_subsumption_smt2(chain1, chain2, f1, f2, alternatives)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN, skipped=True, skip_reason=str(exc))

        timeouts = getattr(self._solver, "timeout_count", 0)
        result = self._solver.solve(smt2)
        if (result == SolverResult.UNKNOWN and len(alternatives) > 1
                and not solver_timed_out(self._solver, timeouts)):
            # One way of failing at a time. The refutation is a disjunction
            # carrying negated regex memberships, which the solver answers
            # `unknown` to while deciding each branch of it.
            result = solve_any(self._solver, [
                chain_subsumption_smt2(chain1, chain2, f1, f2, [alt])
                for alt in alternatives
            ])
        if self._verbosity >= 1:
            outcome = {
                SolverResult.UNSAT: "SUBSUMED",
                SolverResult.SAT: "not subsumed",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return ChainSubsumptionResult(
            chain1, chain2, result,
            elapsed_sec=getattr(self._solver, "last_elapsed_sec", 0.0),
            error=getattr(self._solver, "last_error_text", "") if result == SolverResult.UNKNOWN else "",
        )

    def find_subsumed_chains(
        self,
        rules: Sequence[SecRule],
        include_skipped: bool = False,
        on_result: "Callable[[ChainSubsumptionResult], None] | None" = None,
    ) -> list[ChainSubsumptionResult]:
        """Return all ordered pairs of chains where chain1 is subsumed by chain2.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own); only chains whose every link is @rx /
        !@rx are considered. All ordered pairs of distinct chains are
        checked; by default, pairs skipped due to disjoint variables or
        unsupported transforms are excluded, but pairs where the solver
        itself returns UNKNOWN (e.g. timeout) are kept with that result. Pass
        ``include_skipped=True`` to get every checked pair back, including
        skipped ones (with ``skipped=True`` and ``skip_reason`` set) — e.g.
        for a detailed machine-readable report.

        *on_result*, if given, is called with each ChainSubsumptionResult
        (including skipped ones) as soon as it is computed, before the
        method returns — so a caller can stream/persist partial progress
        (e.g. to survive being killed partway through a large ruleset).
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
                if on_result is not None:
                    on_result(res)
                if include_skipped or not res.skipped:
                    results.append(res)

        return results
