"""Reachability analysis: which rules can never fire?

This is the analysis the stateful encoding in :mod:`wafan.state` exists to
make possible. The pairwise analyses ask whether two rules' *match
conditions* overlap; this one asks a question about the ruleset as a program:

    is there any request for which this rule both executes and matches?

If not, the rule is dead code. Three distinct causes show up in real rule
sets, and the checker separates them because the fix differs:

``unreachable``
    Control flow never gets there — an earlier ``skipAfter`` always jumps
    over it, a ``ctl:ruleRemoveById`` always disables it, or a preceding
    disruptive rule always ends the transaction first.

``impossible_match``
    Execution reaches the rule, but its condition cannot hold. The common
    case is a guard on ``TX`` state no rule ever produces: CRS's
    ``&TX:crs_exclusions_wordpress "@eq 0"`` pattern is vacuous when nothing
    sets that variable, and its ``!@eq 0`` counterpart is dead.

``ok``
    A concrete request exists that fires the rule.

Only ``UNSAT`` verdicts are meaningful as *findings*: the stateful encoding
over-approximates ``fire`` for any directive it cannot model faithfully (see
:mod:`wafan.state`), so a rule reported dead is genuinely dead, while a rule
reported live may merely be beyond the model's precision.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional

from ..ruleset import Directive, Ruleset
from ..state import StateEncoding, StatefulEncoder
from .solver import SolverBackend, SolverResult

# Verdicts, in reporting order of severity.
OK = "ok"
UNREACHABLE = "unreachable"
IMPOSSIBLE_MATCH = "impossible_match"
UNKNOWN = "unknown"


@dataclass
class ReachabilityResult:
    """Outcome of asking whether one directive can ever fire."""

    directive: Directive
    position: int
    verdict: str                 # OK | UNREACHABLE | IMPOSSIBLE_MATCH | UNKNOWN
    result: SolverResult
    abstracted: bool = False     # this directive's match was over-approximated
    abstract_reason: str = ""
    elapsed_sec: float = 0.0
    error: str = ""

    @property
    def is_dead(self) -> bool:
        return self.verdict in (UNREACHABLE, IMPOSSIBLE_MATCH)

    @property
    def rule_id(self) -> str:
        return self.directive.rule_id


class ReachabilityChecker:
    """Decide, per directive, whether any request can make it fire."""

    def __init__(self, solver: SolverBackend, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check(self, encoding: StateEncoding, position: int) -> ReachabilityResult:
        """Check one position of *encoding*'s execution sequence.

        Asserts ``fire_p`` over the ruleset sliced at *p* — everything ordered
        after *p* is irrelevant, since state only flows forward. On UNSAT a
        second query asserting ``reach_p`` alone separates "never executed"
        from "executed but can't match".
        """
        directive = encoding.order[position]
        fire = encoding.fire[position]
        abstract_reason = encoding.abstracted.get(position, "")

        smt2 = encoding.script([fire], upto=position)
        result = self._solver.solve(smt2)
        elapsed = getattr(self._solver, "last_elapsed_sec", 0.0)

        verdict = UNKNOWN
        if result == SolverResult.SAT:
            verdict = OK
        elif result == SolverResult.UNSAT:
            reach = encoding.reach.get(position, "true")
            if reach == "true":
                verdict = IMPOSSIBLE_MATCH
            else:
                reach_result = self._solver.solve(
                    encoding.script([reach], upto=position)
                )
                elapsed += getattr(self._solver, "last_elapsed_sec", 0.0)
                verdict = (
                    IMPOSSIBLE_MATCH if reach_result == SolverResult.SAT else UNREACHABLE
                )

        res = ReachabilityResult(
            directive=directive,
            position=position,
            verdict=verdict,
            result=result,
            abstracted=bool(abstract_reason),
            abstract_reason=abstract_reason,
            elapsed_sec=elapsed,
            error=(
                getattr(self._solver, "last_error_text", "")
                if result == SolverResult.UNKNOWN
                else ""
            ),
        )
        if self._verbosity >= 1:
            print(f"  {directive.label():<62} [{verdict}]", flush=True)
        return res

    def find_dead(
        self,
        encoding: StateEncoding,
        on_result: Optional[Callable[[ReachabilityResult], None]] = None,
        include_actions: bool = False,
    ) -> list[ReachabilityResult]:
        """Check every rule directive in *encoding*, in execution order.

        ``SecAction`` directives are skipped by default: they are
        unconditional, so their reachability is a property of the control flow
        around them rather than a rule-quality finding. Pass
        ``include_actions=True`` to check them too (an unreachable
        ``SecAction`` means its ``setvar`` initialisers never run, which is
        worth knowing when auditing a configuration).
        """
        results: list[ReachabilityResult] = []
        for position, directive in enumerate(encoding.order):
            if directive.kind == "marker":
                continue
            if directive.kind == "action" and not include_actions:
                continue
            res = self.check(encoding, position)
            if on_result is not None:
                on_result(res)
            results.append(res)
        return results


def analyse_reachability(
    paths, solver: SolverBackend, verbosity: int = 0
) -> tuple[StateEncoding, list[ReachabilityResult]]:
    """Parse *paths*, build the state model, and check every rule."""
    encoding = StatefulEncoder(Ruleset.from_paths(paths)).encode()
    checker = ReachabilityChecker(solver, verbosity=verbosity)
    return encoding, checker.find_dead(encoding)
