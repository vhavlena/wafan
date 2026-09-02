"""Shared helpers used across the subsumption, intersection and witness analyses."""

from __future__ import annotations

from typing import Sequence

from ..parser import SecRule
from ..smt import (
    _merge_unique,
    _operator_builder,
    _restrictable_transform_keys,
    _rules_relevant_codepoints,
    chain_witness_map,
    effective_transforms,
    is_supported_operator,
    transform_preamble,
)
from ..targets import resolve_target
from .solver import SolverResult

_SMT_SEP = "  " + "-" * 62


def _print_smt_block(smt2: str) -> None:
    print(f"  SMT-LIB2:\n{_SMT_SEP}\n{smt2}\n{_SMT_SEP}", flush=True)


_INTERSECTION_OUTCOME_LABELS = {
    SolverResult.SAT: "intersecting",
    SolverResult.UNSAT: "disjoint",
    SolverResult.UNKNOWN: "unknown",
}


def intersection_outcome_label(result: SolverResult) -> str:
    """Human-readable outcome label for a SAT/UNSAT/UNKNOWN solver result in an
    intersection-shaped analysis (intersection, contradiction): SAT is a
    non-empty intersection ("intersecting"), UNSAT is disjoint."""
    return _INTERSECTION_OUTCOME_LABELS[result]


def _rule_label(rule: SecRule, pat_width: int = 35) -> str:
    """Return a compact human-readable identifier for *rule*.

    Format: ``#ID [VAR1,VAR2 OP "PATTERN"]``

    Each target is shown as written --- selector, ``&`` and ``!`` included ---
    since two rules differing only in a selector get different verdicts, and a
    label that dropped it would render them indistinguishable. The list is
    capped at three targets; the pattern is truncated to *pat_width*
    characters so the label fits on one terminal line.
    """
    var_names = [
        f"{'&' if v.counter else ''}{'!' if v.negated else ''}{v.name}"
        + (f":{v.part}" if v.part else "")
        for v in rule.variables
    ]
    if len(var_names) > 3:
        vars_str = ",".join(var_names[:3]) + ",..."
    else:
        vars_str = ",".join(var_names)
    pat = rule.operator_argument
    if len(pat) > pat_width:
        pat = pat[:pat_width - 3] + "..."
    op = rule.operator
    return f"#{rule.rule_id} [{vars_str} {op} \"{pat}\"]"


def _chain_label(chain: Sequence[SecRule], pat_width: int = 35) -> str:
    """Return a compact human-readable identifier for a chained rule.

    Single-link chains are labelled like a plain rule; multi-link chains are
    labelled after their first link, annotated with the number of additional
    chained links.
    """
    label = _rule_label(chain[0], pat_width=pat_width)
    if len(chain) > 1:
        label += f" +{len(chain) - 1} chained"
    return label


def _all_supported(chain: Sequence[SecRule]) -> bool:
    """True if every link of *chain* uses an SMT-convertible operator."""
    return all(is_supported_operator(r.operator) for r in chain)


def chain_support_status(chain: Sequence[SecRule]) -> str:
    """Classify why a chain can or cannot be turned into an SMT query.

    Returns one of ``"ok"``, ``"unsupported_operator"``,
    ``"unsupported_transform"`` or ``"unsupported_pattern"``. Used for
    reporting/statistics purposes (e.g. the ``--json`` summary), independent
    of any particular pairwise analysis.
    """
    return chain_support_detail(chain)[0]


def chain_support_detail(chain: Sequence[SecRule]) -> tuple[str, str]:
    """Like chain_support_status(), but also return *why*: which operator,
    transform or pattern construct is unsupported, and on which rule.

    Returns ``(status, detail)`` where ``detail`` is a human-readable
    explanation naming the offending construct (empty string for ``"ok"``).
    """
    unsupported_ops = sorted({
        f"rule {r.rule_id}: '{r.operator}'" for r in chain if not is_supported_operator(r.operator)
    })
    if unsupported_ops:
        return "unsupported_operator", f"operator not supported: {'; '.join(unsupported_ops)}"

    from ..regex_conv import UnsupportedPatternError
    from ..smt import UnsupportedOperatorError, UnsupportedTransformError, chain_to_smt

    try:
        chain_to_smt(chain)
    except UnsupportedTransformError as exc:
        return "unsupported_transform", str(exc)
    except UnsupportedPatternError as exc:
        return "unsupported_pattern", str(exc)
    except UnsupportedOperatorError as exc:
        # is_supported_operator() only checks the operator *name*; numeric
        # operators (@eq/@ge/...) can still fail deep in chain_to_smt() if
        # their argument isn't a literal integer (e.g. a ModSecurity
        # macro like %{tx.sampling_percentage}).
        return "unsupported_operator", str(exc)
    return "ok", ""


def _operator_assertion(rule: SecRule, var_expr: str) -> str:
    """Return the SMT-LIB2 assertion for *rule*'s operator applied to *var_expr*.

    Raises UnsupportedOperatorError if the rule's operator is not supported
    (or, for numeric operators, its argument is not an integer).
    """
    return _operator_builder(rule)(var_expr)


def _joint_transform_preamble(
    rules_a: Sequence[SecRule], rules_b: Sequence[SecRule]
) -> tuple[list[str], list[str]]:
    """Return ``(fun_declarations, axioms)`` for two rule/chain sides being
    merged into one pairwise SMT-LIB2 script (intersection or subsumption).

    A transform shared by both sides (e.g. ``t_urlDecode``) is one global SMT
    symbol, so it must get exactly one declaration across the merged script.
    Restricting that declaration to a codepoint set is only sound if it
    covers what *either* side needs, so *rules_a* and *rules_b* are analysed
    together: the relevant-codepoint set is the union of both sides' own sets
    (or None/unrestricted as soon as either side's is unknown), and a
    transform is only restricted if it is safe to restrict across every rule
    of both sides combined (see ``wafan.smt._restrictable_transform_keys``).
    """
    relevant_a = _rules_relevant_codepoints(rules_a)
    relevant_b = _rules_relevant_codepoints(rules_b)
    joint_relevant = (
        None if relevant_a is None or relevant_b is None else relevant_a | relevant_b
    )

    transform_lists = [effective_transforms(r) for r in (*rules_a, *rules_b)]
    joint_restrictable = _restrictable_transform_keys(transform_lists)

    fun_decls: list[str] = []
    axioms: list[str] = []
    for transforms in transform_lists:
        fd, ax = transform_preamble(transforms, joint_relevant, joint_restrictable)
        fun_decls = _merge_unique(fun_decls, fd)
        axioms = _merge_unique(axioms, ax)
    return fun_decls, axioms


def _variable_names(rule: SecRule) -> frozenset[str]:
    return frozenset(v.name for v in rule.variables)


def rules_share_variable(rule1: SecRule, rule2: SecRule) -> bool:
    """True if both rules target at least one common ModSecurity variable."""
    return bool(_variable_names(rule1) & _variable_names(rule2))


def _chain_variable_names(chain: Sequence[SecRule]) -> frozenset[str]:
    names: set[str] = set()
    for rule in chain:
        names.update(v.name for v in rule.variables)
    return frozenset(names)


def chains_share_variable(chain1: Sequence[SecRule], chain2: Sequence[SecRule]) -> bool:
    """True if any link of chain1 and any link of chain2 target a common variable.

    Compares the variable names as written, so ``ARGS`` and ``ARGS_NAMES``
    count as different: use :func:`chains_share_target` for the question the
    pairwise analyses actually ask, which is whether the two can read one
    common member.
    """
    return bool(_chain_variable_names(chain1) & _chain_variable_names(chain2))


# ---------------------------------------------------------------------------
# Common and escaping witnesses
# ---------------------------------------------------------------------------
#
# A rule's condition is existential over the members its target list resolves
# to, so two rules both firing on one request does not make them overlap: the
# witnesses may be two different arguments, or two unrelated collections. What
# the pairwise analyses ask is a relation between the two witness *sets* --- do
# they meet (intersection), is one contained in the other (subsumption) --- and
# both are decided here by conjoining the two sides' conditions on one shared
# address per collection (see the address model in wafan.smt).
#
# Reading the target lists only decides which addresses exist to share; every
# question about whether they can actually hold the same member --- selector
# against selector, exclusion, name against value, pattern against pattern ---
# goes to the solver as a constraint on the shared name and value symbols.


def chain_value_families(chain: Sequence[SecRule]) -> frozenset[str]:
    """The families whose members *chain* reads, i.e. where it can witness.

    A ``&`` spec is excluded: it reads a cardinality rather than a member, so
    it constrains no address and can never supply a common witness.
    """
    return frozenset(
        resolve_target(v).family
        for rule in chain
        for v in rule.variables
        if not v.negated and not v.counter
    )


def chains_share_target(chain1: Sequence[SecRule], chain2: Sequence[SecRule]) -> bool:
    """True if the two chains can read a common member.

    Resolves each spec onto its backing family, so ``ARGS``, ``ARGS:id`` and
    ``ARGS_NAMES`` all count as the same target --- they are the same members,
    filtered or viewed differently. Whether a *specific* member can satisfy
    both sides is left to the solver.
    """
    return bool(chain_value_families(chain1) & chain_value_families(chain2))


def solve_any(solver, scripts: Sequence[str]) -> SolverResult:
    """Solve a query given as a disjunction of scripts: SAT iff any is.

    Satisfiability distributes over disjunction, so a query the solver cannot
    decide in one piece can be asked one branch at a time --- and that is not
    a mere convenience. A refined pairwise query is a disjunction whose
    branches carry negated regex memberships, and z3-noodler answers
    ``unknown`` to the disjunction while deciding every branch of it: the
    two halves of ``fire_p and (not fire_q or (wit_p and not wit_q))`` come
    back ``unsat`` each, and the whole ``unknown``.

    UNSAT only when every branch is; UNKNOWN when none is SAT and some branch
    could not be decided.
    """
    verdict = SolverResult.UNSAT
    for script in scripts:
        result = solver.solve(script)
        if result == SolverResult.SAT:
            return SolverResult.SAT
        if result == SolverResult.UNKNOWN:
            verdict = SolverResult.UNKNOWN
    return verdict


def solver_timed_out(solver, before: int) -> bool:
    """Whether the solver's last call ran out of time, given its
    ``timeout_count`` from before that call.

    A timeout is not the same answer as a formula the solver declined to
    decide, and the difference decides whether splitting a disjunction is
    worth trying: splitting rescues the second and only multiplies the cost of
    the first, since every branch carries the same expensive constraints.
    """
    return getattr(solver, "timeout_count", 0) > before


def chain_common_witness(
    chain1: Sequence[SecRule],
    chain2: Sequence[SecRule],
) -> list[str]:
    """One term per target both chains can witness their match in.

    Empty when they share no target: with no address in common the two witness
    sets are disjoint whatever the request, so the pair does not intersect
    however freely both chains can fire.

    Returned per target rather than pre-disjoined, because the caller may have
    to ask the solver one at a time (see :func:`solve_any`).
    """
    w1 = chain_witness_map(chain1)
    w2 = chain_witness_map(chain2)
    return [f"(and {w1[family]} {w2[family]})" for family in w1 if family in w2]


def chain_escaping_witness(
    chain1: Sequence[SecRule],
    chain2: Sequence[SecRule],
) -> list[str]:
    """One term per target where chain1 witnesses and chain2 does not.

    This is the refutation of containment, and the second way subsumption can
    fail: chain2 may well fire on every request chain1 fires on and still not
    match the member chain1 matched.

    Only the targets both chains read contribute. A collection chain2 never
    looks at is no evidence that it misses anything --- its coverage is judged
    where it looks. Counting those too would mean a chain guarded on
    ``TX:flag`` could never be subsumed by the plain rule whose pattern it
    repeats, though deleting it changes no verdict. Whether the two read any
    common target at all is a question about the pair, settled before the
    query is built (see :func:`chains_share_target`).

    Empty when there is nothing to contain: no shared target, or no witness
    on chain1's side (a ``&``-only condition, whose containment is vacuous).
    """
    w1 = chain_witness_map(chain1)
    w2 = chain_witness_map(chain2)
    return [
        f"(and {w1[family]} (not {w2[family]}))" for family in w1 if family in w2
    ]


_DENY_ACTIONS = frozenset({"deny", "drop", "block"})
_ALLOW_ACTIONS = frozenset({"allow"})


def chain_disposition(chain: Sequence[SecRule]) -> str:
    """Classify a chain's disruptive action as ``"deny"``, ``"allow"`` or ``"unknown"``.

    Scans every link's own actions first (a chain's disruptive action is
    conventionally placed on its first link, but any link may carry one),
    then falls back to each link's inherited actions (from
    ``SecDefaultAction``) if none of the rule's own actions are conclusive.

    ``pass`` is deliberately not treated as ``"allow"``: it is ModSecurity's
    no-op/continue default (often used purely for flow control, e.g.
    ``skipAfter``), not an explicit decision to accept the request. Chains
    whose only disruptive-adjacent action is ``pass`` are ``"unknown"`` so
    they aren't paired against a real ``deny`` and flagged as a contradiction.
    """
    for link in chain:
        for action in link.actions:
            if action.name in _DENY_ACTIONS:
                return "deny"
            if action.name in _ALLOW_ACTIONS:
                return "allow"
    for link in chain:
        for action in link.inherited_actions:
            if action.name in _DENY_ACTIONS:
                return "deny"
            if action.name in _ALLOW_ACTIONS:
                return "allow"
    return "unknown"


def rule_disposition(rule: SecRule) -> str:
    """Classify a single rule's disruptive action; see chain_disposition()."""
    return chain_disposition([rule])
