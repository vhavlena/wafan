"""Pairwise analyses over *firing* conditions rather than match conditions.

The checkers in :mod:`wafan.analyses.intersection` and
:mod:`~wafan.analyses.subsumption` compare two rules' match conditions in
isolation. That answers "could one request satisfy both patterns?", which is
not quite the question a rule author has. This module asks the stronger ones,
using the whole-ruleset model from :mod:`wafan.state`.

``intersection``
    Is there a single transaction in which **both rules actually fire** —
    both reached, both matched, given everything the ruleset does to ``TX``
    state and control flow before them?

``subsumption``
    Does **every** transaction that fires rule A also fire rule B?

``shadowing``
    For an earlier rule A and a later rule B whose dispositions conflict
    (one accepts, one denies): is there a request where A fires *and* B would
    also have matched? A is disruptive, so it ends the transaction and B's
    opposite decision never happens. The outcome is decided by rule order
    alone — which is the ordered-execution analogue of a contradiction.

Why "shadowing" and not "contradiction"
    In an ordered model, two genuinely disruptive rules can never both fire:
    whichever runs first terminates the transaction, so ``fire_A ∧ fire_B`` is
    unsatisfiable by construction and a literal "both fire with conflicting
    actions" query is vacuous. The real defect is not simultaneity but a
    silent precedence: two rules disagree about a request and the file order
    quietly picks the winner. Querying ``fire_A ∧ match_B`` — B's match
    condition with reachability factored out — is what exposes that, and is
    why :class:`~wafan.state.StateEncoding` carries ``match`` terms separately
    from ``fire``.

Two rules with no request variable in common can still interact through
``TX``, so this module does not apply the "no shared variable" pruning the
stateless checkers use — with state in the model, that filter is unsound.
Because that filter is gone, this is a genuine O(n²) sweep of solver calls;
:mod:`wafan.analyses.reachability` is O(n) and finds the dead-code class of
defect, so prefer it for a first pass over a large ruleset, then use
``positions=`` here to focus on what it flagged.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Optional, Sequence

from ..ruleset import Directive
from ..state import StateEncoding
from .common import chain_disposition
from .solver import SolverBackend, SolverResult

INTERSECTION = "intersection"
SUBSUMPTION = "subsumption"
SHADOWING = "shadowing"

MODES = (INTERSECTION, SUBSUMPTION, SHADOWING)

_SYMBOL = {INTERSECTION: "∩", SUBSUMPTION: "⊆", SHADOWING: "≻"}


@dataclass
class StatefulPairResult:
    """Outcome of one stateful pairwise query."""

    mode: str
    directive1: Directive
    directive2: Directive
    position1: int
    position2: int
    result: SolverResult
    elapsed_sec: float = 0.0
    error: str = ""
    # True when either side's match had to be over-approximated by the
    # encoder, so a positive verdict may be spurious (see wafan.state).
    approximate: bool = False
    approximate_reasons: list[str] = field(default_factory=list)

    @property
    def rule_ids(self) -> tuple[str, str]:
        return self.directive1.rule_id, self.directive2.rule_id

    @property
    def dispositions(self) -> tuple[str, str]:
        def of(d: Directive) -> str:
            return chain_disposition(d.chain) if d.chain else "unknown"

        return of(self.directive1), of(self.directive2)

    @property
    def dispositions_conflict(self) -> bool:
        return set(self.dispositions) == {"allow", "deny"}

    @property
    def holds(self) -> bool:
        """True when the queried relation holds for this pair."""
        if self.mode == SUBSUMPTION:
            return self.result == SolverResult.UNSAT
        if self.mode == SHADOWING:
            return self.result == SolverResult.SAT and self.dispositions_conflict
        return self.result == SolverResult.SAT

    @property
    def outcome(self) -> str:
        if self.result == SolverResult.UNKNOWN:
            return "unknown"
        if self.mode == SUBSUMPTION:
            return "subsumed" if self.result == SolverResult.UNSAT else "not_subsumed"
        if self.mode == SHADOWING:
            if self.result == SolverResult.UNSAT:
                return "no_shadowing"
            return "shadowing" if self.dispositions_conflict else "overlap_no_conflict"
        return "never_both_fire" if self.result == SolverResult.UNSAT else "both_fire"


class StatefulPairChecker:
    """Run a pairwise analysis over the ``fire``/``match`` terms of an encoding."""

    def __init__(self, solver: SolverBackend, mode: str, verbosity: int = 0) -> None:
        if mode not in MODES:
            raise ValueError(f"unknown mode '{mode}' (expected one of {MODES})")
        self._solver = solver
        self._mode = mode
        self._verbosity = verbosity

    def _assertions(self, encoding: StateEncoding, p: int, q: int) -> list[str]:
        fire_p, fire_q = encoding.fire[p], encoding.fire[q]
        if self._mode == SUBSUMPTION:
            # SAT ⇔ some transaction fires p but not q ⇒ p ⊄ q.
            return [fire_p, f"(not {fire_q})"]
        if self._mode == SHADOWING:
            # p fires (and, being disruptive, ends the transaction) on a
            # request that q would also have matched.
            return [fire_p, encoding.match[q]]
        return [fire_p, fire_q]

    def check_pair(self, encoding: StateEncoding, p: int, q: int) -> StatefulPairResult:
        """Query one ordered pair of execution positions.

        The script is sliced at ``max(p, q)``: state flows forward only, so
        nothing ordered after both positions can affect either one.
        """
        d1, d2 = encoding.order[p], encoding.order[q]
        reasons = [
            f"#{d.rule_id}: {encoding.abstracted[pos]}"
            for pos, d in ((p, d1), (q, d2))
            if pos in encoding.abstracted
        ]

        smt2 = encoding.script(self._assertions(encoding, p, q), upto=max(p, q))
        result = self._solver.solve(smt2)

        res = StatefulPairResult(
            mode=self._mode,
            directive1=d1,
            directive2=d2,
            position1=p,
            position2=q,
            result=result,
            elapsed_sec=getattr(self._solver, "last_elapsed_sec", 0.0),
            error=(
                getattr(self._solver, "last_error_text", "")
                if result == SolverResult.UNKNOWN
                else ""
            ),
            approximate=bool(reasons),
            approximate_reasons=reasons,
        )
        if self._verbosity >= 1:
            print(
                f"  #{d1.rule_id} {_SYMBOL[self._mode]} #{d2.rule_id}  [{res.outcome}]"
                + ("  (approximate)" if res.approximate else ""),
                flush=True,
            )
        return res

    def _pairs_to_check(self, positions: Sequence[int]):
        """Which ordered pairs this mode needs.

        Subsumption is directional, so it needs every ordered pair.
        Intersection is symmetric, so one of each unordered pair suffices.
        Shadowing is inherently directional *in execution order* — only an
        earlier rule can shadow a later one — so it needs exactly the pairs
        with ``p < q``.
        """
        for i, p in enumerate(positions):
            for j, q in enumerate(positions):
                if p == q:
                    continue
                if self._mode == SUBSUMPTION:
                    yield p, q
                elif j > i:
                    yield p, q

    def find_pairs(
        self,
        encoding: StateEncoding,
        on_result: Optional[Callable[[StatefulPairResult], None]] = None,
        positions: Optional[Sequence[int]] = None,
    ) -> list[StatefulPairResult]:
        """Sweep rule pairs according to the mode's directionality.

        *positions* restricts the sweep to a subset of execution positions,
        which is the practical way to use this on a large ruleset: run
        :mod:`~wafan.analyses.reachability` first, then pass the positions you
        actually care about.
        """
        if positions is None:
            positions = [i for i, d in enumerate(encoding.order) if d.kind == "rule"]

        results: list[StatefulPairResult] = []
        for p, q in self._pairs_to_check(positions):
            res = self.check_pair(encoding, p, q)
            if on_result is not None:
                on_result(res)
            results.append(res)
        return results
