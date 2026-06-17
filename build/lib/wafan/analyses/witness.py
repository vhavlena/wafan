"""Witness analysis.

WitnessChecker finds concrete inputs (models) that trigger @rx SecRules or
chains of @rx SecRules.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ..parser import SecRule, group_chains
from ..smt import (
    SmtFormula,
    UnsupportedOperatorError,
    UnsupportedTransformError,
    chain_to_smt,
    is_supported_operator,
    rule_to_smt,
)
from .common import _all_supported, _chain_label, _print_smt_block, _rule_label
from .solver import SolverResult, SubprocessSolver


# ---------------------------------------------------------------------------
# Witness (concrete model) query generation
# ---------------------------------------------------------------------------

def witness_smt2(rule: SecRule) -> str:
    """Return an SMT-LIB2 string that, when SAT, yields a concrete input
    triggering *rule*.

    The formula asserts the rule's match condition for each of its variables.
    A (get-value ...) command is appended so the solver can return concrete
    string values.  The solver must be invoked with model generation enabled
    (e.g. z3 model=true -in).

    Raises:
        UnsupportedOperatorError: if the operator is not supported.
        UnsupportedTransformError: if a t: action is unknown.
    """
    formula: SmtFormula = rule_to_smt(rule)
    return formula.to_smt2_with_model()


def chain_witness_smt2(chain: Sequence[SecRule]) -> str:
    """Return an SMT-LIB2 string that, when SAT, yields a concrete input
    triggering every link of *chain* simultaneously.

    The formula asserts the conjunction of each link's match condition (see
    chain_to_smt). A (get-value ...) command is appended so the solver can
    return concrete string values. The solver must be invoked with model
    generation enabled (e.g. z3 model=true -in).

    Raises:
        UnsupportedOperatorError: if any link's operator is not supported.
        UnsupportedTransformError: if any link uses an unknown transform.
    """
    formula: SmtFormula = chain_to_smt(chain)
    return formula.to_smt2_with_model()


# ---------------------------------------------------------------------------
# Witness checker
# ---------------------------------------------------------------------------

@dataclass
class WitnessResult:
    """Outcome of finding a concrete input that triggers *rule*.

    If *result* is SAT, *model* maps each ModSecurity variable name (as used
    in the SMT formula) to a concrete string value that satisfies the rule.
    For unsupported rules the result is UNKNOWN and model is None.
    """

    rule: SecRule
    result: SolverResult
    model: dict[str, str] | None = None

    @property
    def has_witness(self) -> bool:
        return self.result == SolverResult.SAT

    def format_model(self) -> str:
        """Return a human-readable representation of the model."""
        if not self.model:
            return "    (no model)"
        return "\n".join(f"    {k} = {v!r}" for k, v in self.model.items())


@dataclass
class ChainWitnessResult:
    """Outcome of finding a concrete input that triggers every link of *chain*.

    If *result* is SAT, *model* maps each ModSecurity variable name (as used
    in the SMT formula) to a concrete string value that satisfies all links
    of the chain simultaneously. For unsupported chains the result is
    UNKNOWN and model is None.
    """

    chain: list[SecRule]
    result: SolverResult
    model: dict[str, str] | None = None

    @property
    def has_witness(self) -> bool:
        return self.result == SolverResult.SAT

    def format_model(self) -> str:
        """Return a human-readable representation of the model."""
        if not self.model:
            return "    (no model)"
        return "\n".join(f"    {k} = {v!r}" for k, v in self.model.items())


class WitnessChecker:
    """Find concrete inputs (witnesses/models) that trigger @rx SecRules.

    Requires a SubprocessSolver (or any object with a solve_with_model
    method) so that the SMT model can be extracted from the solver output.
    """

    def __init__(self, solver: SubprocessSolver, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check_rule(self, rule: SecRule) -> WitnessResult:
        """Find a concrete input that triggers *rule*, if one exists.

        Returns UNKNOWN if the rule uses an unsupported transform or a
        non-@rx operator.
        """
        label = _rule_label(rule)

        if not is_supported_operator(rule.operator):
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (unsupported operator)")
            return WitnessResult(rule, SolverResult.UNKNOWN)

        try:
            smt2 = witness_smt2(rule)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (unsupported transform: {exc})")
            return WitnessResult(rule, SolverResult.UNKNOWN)

        result, model = self._solver.solve_with_model(smt2)

        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "SAT",
                SolverResult.UNSAT: "never matches",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"  {label}  [{outcome:<13}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)

        return WitnessResult(rule, result, model)

    def find_witnesses(self, rules: Sequence[SecRule]) -> list[WitnessResult]:
        """Return WitnessResults for all @rx / !@rx rules.

        Rules where the solver returns UNKNOWN are included so callers can
        distinguish unsatisfiable rules from solver failures.
        """
        rx_rules = [r for r in rules if is_supported_operator(r.operator)]
        if self._verbosity >= 1:
            print(f"Witness analysis: {len(rx_rules)} rules\n")
        return [self.check_rule(r) for r in rx_rules]

    def check_chain(self, chain: Sequence[SecRule]) -> ChainWitnessResult:
        """Find a concrete input that triggers every link of *chain*, if one exists.

        Returns UNKNOWN if any link uses an unsupported transform or a
        non-@rx operator.
        """
        chain = list(chain)
        label = _chain_label(chain)

        if not _all_supported(chain):
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (unsupported operator)")
            return ChainWitnessResult(chain, SolverResult.UNKNOWN)

        try:
            smt2 = chain_witness_smt2(chain)
        except (UnsupportedTransformError, UnsupportedOperatorError) as exc:
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (unsupported transform: {exc})")
            return ChainWitnessResult(chain, SolverResult.UNKNOWN)

        result, model = self._solver.solve_with_model(smt2)

        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "SAT",
                SolverResult.UNSAT: "never matches",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"  {label}  [{outcome:<13}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)

        return ChainWitnessResult(chain, result, model)

    def find_chain_witnesses(self, rules: Sequence[SecRule]) -> list[ChainWitnessResult]:
        """Return ChainWitnessResults for all chains of @rx / !@rx rules.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own). Chains where the solver returns UNKNOWN
        are included so callers can distinguish unsatisfiable chains from
        solver failures.
        """
        chains = group_chains(list(rules))
        if self._verbosity >= 1:
            print(f"Chain witness analysis: {len(chains)} chains\n")
        return [self.check_chain(c) for c in chains]
