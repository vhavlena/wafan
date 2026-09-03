"""Pairwise analyses over *firing* conditions rather than match conditions.

The checkers in :mod:`wafan.analyses.intersection` and
:mod:`~wafan.analyses.subsumption` compare two rules' match conditions in
isolation. That answers "could one request satisfy both patterns?", which is
not quite the question a rule author has. This module asks the stronger ones,
using the whole-ruleset model from :mod:`wafan.state`.

``intersection``
    Is there a single transaction in which **both rules actually fire on one
    member** — both reached, both matching the same argument, header or ``TX``
    variable, given everything the ruleset does to state and control flow
    before them? Both firing is not enough: a match is existential over the
    members a target resolves to, so two rules on ``ARGS`` both fire on
    ``?x=a&y=b`` while matching different arguments.

``subsumption``
    Does **every** transaction that fires rule A also fire rule B, matching
    every member A matched among those B reads?

``shadowing``
    For an earlier rule A that *pre-empts* a later rule B — A ends the
    transaction, or A skips over B — is there a request where A fires *and* B
    would also have matched? B never runs, so its decision is lost and the
    outcome is settled by rule order alone, which is the ordered-execution
    analogue of a contradiction.

    Both halves are load-bearing. ``fire_A ∧ match_B`` on its own says
    nothing about precedence: a ``pass`` rule that fires leaves B to run as
    usual, so the query would hold for any overlapping pair whatever. The
    pre-emption side condition is what makes it a statement about the pair,
    and it is static — see :func:`preempts`.

Why "shadowing" and not "contradiction"
    In an ordered model, two genuinely disruptive rules can never both fire:
    whichever runs first terminates the transaction, so ``fire_A ∧ fire_B`` is
    unsatisfiable by construction and a literal "both fire with conflicting
    actions" query is vacuous. The real defect is not simultaneity but a
    silent precedence: two rules disagree about a request and the file order
    quietly picks the winner. Querying ``fire_A ∧ match_B`` under pre-emption
    — B's match condition with reachability factored out — is what exposes
    that, and is
    why :class:`~wafan.state.StateEncoding` carries ``match`` terms separately
    from ``fire``.

Two rules with no request variable in common can still interact through
``TX``, so nothing here is pruned by comparing variable *names*. What does
settle an ``intersection`` or ``subsumption`` pair without a solver call is
having no address in common at all (see :func:`common_witness`), which is the
query's own answer rather than a filter in front of it. Shadowing is the
exception twice over: it is settled instead by pre-emption, and it is not
refined to a common address at all, since two rules can share no data and
still have one silently decide for the other. Everything else is a genuine O(n²) sweep of solver
calls; :mod:`wafan.analyses.reachability` is O(n) and finds the dead-code
class of defect, so prefer it for a first pass over a large ruleset, then use
``positions=`` here to focus on what it flagged.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Optional, Sequence

from ..ruleset import Directive
from ..state import StateEncoding
from .common import chain_disposition, solve_any, solver_timed_out
from .solver import SolverBackend, SolverResult

# ---------------------------------------------------------------------------
# Common and escaping witnesses
# ---------------------------------------------------------------------------
#
# A match is existential over the members a target list resolves to, and the
# state model makes each of those a slot of an array (or a name of a writable
# collection), so `fire_p and fire_q` is satisfiable by two rules witnessing
# at two *different* slots. That is the co-firing question --- the right one
# for whether a chain can complete or a verdict can be reached, and the weaker
# one for whether two rules inspect the same data. Equating the addresses is
# what separates the two, and is what these build.
#
# The addresses come from the encoding, which recorded them as it built each
# position's atoms (see StateEncoding.witness_map); the conditions are read at
# the state versions of their own positions, so a shared `TX` name whose value
# was rewritten in between is correctly two different values.


def common_witness(encoding: StateEncoding, p: int, q: int) -> list[str]:
    """One term per address at which both *p* and *q* can witness.

    Empty when they read no address in common: the two witness sets are then
    disjoint whatever the transaction does, so the pair does not overlap
    however freely both can fire.

    Returned per address rather than pre-disjoined, because the caller may
    have to ask the solver one address at a time (see
    :func:`~wafan.analyses.common.solve_any`).
    """
    w_p, w_q = encoding.witness_map(p), encoding.witness_map(q)
    return [f"(and {w_p[a]} {w_q[a]})" for a in w_p if a in w_q]


def escaping_witness(encoding: StateEncoding, p: int, q: int) -> list[str]:
    """One term per address at which *p* can witness and *q* cannot.

    This is the refutation of containment, and the second way subsumption can
    fail: the directive at *q* may fire in every transaction *p* fires in and
    still not match the member *p* matched.

    Only addresses both read contribute --- one *q* never looks at is no
    evidence that it misses anything, and counting it would leave a chain
    guarded on ``TX:flag`` un-subsumable by the plain rule whose pattern it
    repeats. Empty when they share no address at all, which leaves nothing to
    contain.
    """
    w_p, w_q = encoding.witness_map(p), encoding.witness_map(q)
    return [f"(and {w_p[a]} (not {w_q[a]}))" for a in w_p if a in w_q]


def witness_incomplete(encoding: StateEncoding, p: int, q: int) -> str:
    """Why *p* or *q* has no usable address map, or ``""`` when both do.

    An abstracted directive's map describes only the links that were encoded
    before the encoder gave up, so it must not be read as the addresses the
    directive really reads.
    """
    for pos in (p, q):
        reason = encoding.witness_partial.get(pos)
        if reason:
            return f"#{encoding.order[pos].rule_id}: {reason}"
    return ""


# ---------------------------------------------------------------------------
# Pre-emption
# ---------------------------------------------------------------------------


def preempts(encoding: StateEncoding, p: int, q: int) -> str:
    """How the directive at *p* stops the one at *q* running, or ``""``.

    Shadowing is only a question about a pair when firing *p* is what keeps
    *q* from executing, and there are exactly two ways for that to happen:

    * *p* ends the transaction, so ``fire_p`` falsifies the ``alive`` chain at
      every later position;
    * *p* jumps over or removes *q* (``skipAfter``, ``skip``,
      ``ctl:ruleRemoveById``), so ``reach_q`` carries ``(not fire_p)``
      directly.

    Either way ``fire_p ⇒ ¬reach_q``, which is why the query itself need not
    assert ``¬reach_q``: doing so would also admit models where some *third*
    directive between *p* and *q* is the one that terminated, reporting *p* as
    the shadower of a rule it never pre-empted.

    Nothing else counts. A ``pass`` rule that neither skips nor removes lets
    *q* run on exactly the requests it fires on, so however much the two
    patterns overlap there is no precedence to report --- and that is the
    great majority of pairs, which is why this is checked before the solver
    rather than after it.
    """
    if q <= p:
        return ""
    if encoding.order[p].terminates:
        return "terminates"
    if p in encoding.blocked_by.get(q, []):
        return "skips over it"
    return ""


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
    # True when the verdict follows from the addresses the two directives
    # read, with no solver call needed (see StatefulPairChecker.check_pair).
    derived: bool = False
    derived_reason: str = ""
    # Shadowing only: how the earlier directive stops the later one running
    # ("terminates" / "skips over it"), or "" when it does not (see preempts).
    preemption: str = ""

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
    def verdict_differs(self) -> bool:
        """Shadowing only: would the shadowed rule have decided differently?

        :func:`preempts` has already settled that the later rule does not run;
        this is the severity question layered on it. Two overlapping ``deny``
        rules pre-empt each other all over CRS and the request is blocked
        either way --- that is redundancy, and subsumption is the analysis for
        it. What makes an order-decided outcome a defect is the verdict
        changing.
        """
        first, second = self.dispositions
        if second == "unknown":
            # Nothing in the shadowed rule says what it would have decided, so
            # losing it costs setvars and log lines but no verdict.
            return False
        if first == "unknown":
            # An earlier directive with no explicit accept-or-deny still
            # pre-empted this one --- by skipping over it, or by terminating
            # with an action chain_disposition does not classify (redirect,
            # proxy). Either way nothing decides the request in its place.
            return True
        return first != second

    @property
    def holds(self) -> bool:
        """True when the queried relation holds for this pair."""
        if self.mode == SUBSUMPTION:
            return self.result == SolverResult.UNSAT
        if self.mode == SHADOWING:
            return self.result == SolverResult.SAT and self.verdict_differs
        return self.result == SolverResult.SAT

    @property
    def outcome(self) -> str:
        if self.derived and self.mode == SUBSUMPTION:
            # Not "unknown": nothing was left undecided. With no target in
            # common there is nothing to contain, and what remains is whether
            # the first rule can fire at all.
            return "degenerate"
        if self.result == SolverResult.UNKNOWN:
            return "unknown"
        if self.mode == SUBSUMPTION:
            return "subsumed" if self.result == SolverResult.UNSAT else "not_subsumed"
        if self.mode == SHADOWING:
            if self.result == SolverResult.UNSAT:
                return "no_shadowing"
            return "shadowing" if self.verdict_differs else "overlap_no_conflict"
        # Not "both_fire"/"never_both_fire": the query asks whether one
        # member witnesses both, and two rules that overlap nowhere can still
        # fire in the same transaction on two different members.
        return "no_overlap" if self.result == SolverResult.UNSAT else "overlap"


class StatefulPairChecker:
    """Run a pairwise analysis over the ``fire``/``match`` terms of an encoding."""

    def __init__(self, solver: SolverBackend, mode: str, verbosity: int = 0) -> None:
        if mode not in MODES:
            raise ValueError(f"unknown mode '{mode}' (expected one of {MODES})")
        self._solver = solver
        self._mode = mode
        self._verbosity = verbosity

    def _query(self, encoding: StateEncoding, p: int, q: int,
               refine: bool = True) -> Optional[tuple[list[str], list[str]]]:
        """The query for one ordered pair as (common part, alternatives).

        The alternatives are a disjunction: the query holds if any one of them
        does alongside the common part. Kept apart so a disjunction the solver
        cannot decide whole can be asked branch by branch.

        *refine* off falls back to the co-firing forms, which is what an
        incomplete address map leaves available.

        None means the addresses alone decide it: for intersection there is no
        common one, so no member can witness both; for subsumption there is
        nothing to contain, and what remains is whether the first directive
        can fire at all --- a question about one rule, which reachability
        answers. Shadowing never returns None; what settles it without the
        solver is pre-emption, which check_pair has already tested.
        """
        fire_p, fire_q = encoding.fire[p], encoding.fire[q]
        if self._mode == SUBSUMPTION:
            # SAT ⇔ some transaction fires p but not q, or p matches a member
            # q does not ⇒ p ⊄ q.
            if not refine:
                return [fire_p], [f"(not {fire_q})"]
            escaping = escaping_witness(encoding, p, q)
            if not escaping:
                return None
            return [fire_p], [f"(not {fire_q})", *escaping]

        if self._mode == SHADOWING:
            # p fires on a request q would also have matched. That p firing is
            # what keeps q from running is not asserted here: check_pair has
            # already established it statically, and that is what makes
            # `fire_p implies not reach_q` hold (see preempts).
            #
            # Deliberately *not* refined to a common witness. Unlike
            # intersection, shadowing is not a question about the two rules
            # reading the same data: the archetype is an allowlist on
            # REMOTE_ADDR pre-empting a deny on ARGS, which shares no address
            # with it at all. Demanding a common member would answer "no
            # shadowing" for precisely the pairs the analysis exists to find.
            return [fire_p, encoding.match[q]], []

        head = [fire_p, fire_q]
        if not refine:
            return head, []
        shared = common_witness(encoding, p, q)
        if not shared:
            return None
        return head, shared

    def _solve(self, encoding: StateEncoding, head: list[str],
               alternatives: list[str], upto: int) -> SolverResult:
        """Solve ``head and (or alternatives)``, splitting it if need be.

        One script first, since that is one solver call; on ``unknown`` the
        disjunction is asked one branch at a time, which is what a refined
        subsumption query usually needs --- a negated regex membership under a
        disjunction is where z3-noodler gives up, though it decides each
        branch of it (see :func:`~wafan.analyses.common.solve_any`).
        """
        if not alternatives:
            return self._solver.solve(encoding.script(head, upto=upto))

        combined = (
            alternatives[0] if len(alternatives) == 1
            else "(or " + " ".join(alternatives) + ")"
        )
        timeouts = getattr(self._solver, "timeout_count", 0)
        result = self._solver.solve(encoding.script(head + [combined], upto=upto))
        if (result != SolverResult.UNKNOWN or len(alternatives) == 1
                or solver_timed_out(self._solver, timeouts)):
            # A timeout is a different answer from a formula declined: every
            # branch carries the same expensive constraints, so splitting one
            # only multiplies the wait.
            return result
        return solve_any(
            self._solver,
            [encoding.script(head + [alt], upto=upto) for alt in alternatives],
        )

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

        preemption = preempts(encoding, p, q) if self._mode == SHADOWING else ""
        if self._mode == SHADOWING and not preemption:
            # Settled by control flow, and cheaply: firing d1 leaves d2 to run,
            # so file order decides nothing between them however much their
            # conditions overlap. Checked ahead of the solver because it rules
            # out most pairs -- `fire_p and match_q` on its own is satisfied by
            # any overlapping pair whatever, which is why the pre-emption side
            # condition belongs in the query rather than in a filter over its
            # results (see preempts).
            res = StatefulPairResult(
                mode=self._mode,
                directive1=d1,
                directive2=d2,
                position1=p,
                position2=q,
                result=SolverResult.UNSAT,
                approximate=bool(reasons),
                approximate_reasons=reasons,
                derived=True,
                derived_reason=(
                    f"#{d1.rule_id} neither terminates nor skips over "
                    f"#{d2.rule_id}: it cannot pre-empt it"
                ),
            )
            if self._verbosity >= 1:
                print(
                    f"  #{d1.rule_id} {_SYMBOL[self._mode]} #{d2.rule_id}"
                    f"  [{res.outcome}]  ({res.derived_reason})",
                    flush=True,
                )
            return res

        incomplete = witness_incomplete(encoding, p, q)
        if incomplete and self._mode != SHADOWING:
            # Shadowing is not refined to an address in the first place, so an
            # incomplete map costs it no precision and the note would mislead.
            reasons.append(f"address map incomplete ({incomplete}): co-firing only")
        query = self._query(encoding, p, q, refine=not incomplete)

        if query is None:
            # Settled by the target lists: no solver call, and no verdict
            # smuggled in either --- for subsumption what is left is a
            # dead-code question about one rule, reported as unknown rather
            # than as a subsumption so that a rule matching nothing does not
            # come out redundant given every unrelated one.
            derived = (
                SolverResult.UNKNOWN if self._mode == SUBSUMPTION
                else SolverResult.UNSAT
            )
            res = StatefulPairResult(
                mode=self._mode,
                directive1=d1,
                directive2=d2,
                position1=p,
                position2=q,
                result=derived,
                approximate=bool(reasons),
                approximate_reasons=reasons,
                derived=True,
                derived_reason=(
                    "no common target: subsumption could only hold degenerately"
                    if self._mode == SUBSUMPTION
                    else "no common target: witness sets are disjoint"
                ),
            )
            if self._verbosity >= 1:
                print(
                    f"  #{d1.rule_id} {_SYMBOL[self._mode]} #{d2.rule_id}"
                    f"  [{res.outcome}]  ({res.derived_reason})",
                    flush=True,
                )
            return res

        head, alternatives = query
        result = self._solve(encoding, head, alternatives, upto=max(p, q))

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
            preemption=preemption,
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
