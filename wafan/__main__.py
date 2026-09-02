"""Command-line entry point: python -m wafan  or  wafan (console script)."""

import argparse
import json
import os
import sys
import time
from pathlib import Path

from .analyses import (
    SolverResult,
    SubprocessSolver,
    SubsumptionChecker,
    IntersectionChecker,
    ContradictionChecker,
    WitnessChecker,
    chain_disposition,
    chain_support_detail,
    intersection_outcome_label,
    _chain_label,
)
from .analyses.reachability import (
    IMPOSSIBLE_MATCH,
    UNREACHABLE,
    ReachabilityChecker,
)
from .analyses.stateful import (
    INTERSECTION,
    SHADOWING,
    SUBSUMPTION,
    StatefulPairChecker,
)
from .parser import group_chains, parse_file
from .ruleset import Ruleset
from .solver_setup import ensure_z3_noodler
from .state import StatefulEncoder


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wafan",
        description="SMT-based analysis of ModSecurity SecRule rulesets.",
    )
    p.add_argument(
        "conf",
        type=Path,
        nargs="+",
        help=(
            "Path(s) to ModSecurity .conf file(s), in the order the web server "
            "includes them. Order matters: put crs-setup.conf first so its "
            "SecAction initialisers are visible to the rules that read them."
        ),
    )
    p.add_argument(
        "--solver",
        metavar="PATH",
        default=None,
        help=(
            "Path to the SMT solver binary. "
            "Must support re.from_ecma2020 (mainstream z3 does not). "
            "Falls back to WAFAN_Z3_PATH env var, then to an auto-downloaded "
            "z3-noodler build, then to 'z3' on PATH."
        ),
    )
    p.add_argument(
        "--no-auto-solver",
        action="store_true",
        help="Don't auto-download z3-noodler; use 'z3' on PATH unless --solver/WAFAN_Z3_PATH is set.",
    )
    p.add_argument(
        "--solver-args",
        metavar="ARGS",
        default="",
        help="Extra space-separated arguments forwarded to the solver binary.",
    )
    p.add_argument(
        "--analysis",
        choices=["subsumption", "intersection", "contradiction", "witness", "reachability"],
        default="subsumption",
        help="Analysis to run (default: subsumption). "
             "'witness' finds a concrete input satisfying each rule. "
             "'contradiction' is like 'intersection' but additionally requires "
             "the two rules to disagree on accepting/denying the shared input. "
             "'reachability' finds rules that can never fire, using the "
             "order-aware whole-ruleset state model (implies --stateful).",
    )
    p.add_argument(
        "--include-actions",
        action="store_true",
        help=(
            "Also analyse SecAction directives, not just rules. A SecAction is "
            "unconditional, so its reachability is a fact about control flow "
            "rather than about the directive -- but an unreachable one means "
            "its setvar initialisers never run, which is usually the cause of "
            "whatever dead rules follow it."
        ),
    )
    p.add_argument(
        "--stateful",
        action="store_true",
        help=(
            "Analyse rules as an ordered program with TX as mutable state, "
            "instead of comparing match conditions in isolation. Models "
            "SecAction/setvar, skipAfter, ctl:ruleRemoveById and disruptive "
            "actions, so pairs are compared on whether they can actually both "
            "*fire*. Applies to subsumption/intersection/contradiction."
        ),
    )
    p.add_argument(
        "--timeout",
        type=int,
        default=30,
        metavar="SEC",
        help="Per-query solver timeout in seconds (default: 30).",
    )
    p.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Print each rule pair being checked along with its result.",
    )
    p.add_argument(
        "-v2",
        action="store_true",
        dest="verbose2",
        help="Like -v, but also print the SMT-LIB2 formula for each query.",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help=(
            "Suppress the human-readable report and print newline-delimited "
            "JSON instead: one line per chain (unsupported-construct "
            "classification), one line per pair/chain checked (concrete "
            "rule ids, result, timing, solver error text), and a final "
            "line with the aggregate summary. Each line is flushed as soon "
            "as it's computed, so a process killed partway through (e.g. a "
            "wall-clock budget in a batch runner) still leaves the lines "
            "written so far on stdout. Intended for scripted/batch runs."
        ),
    )
    return p


def _make_solver(args: argparse.Namespace) -> SubprocessSolver:
    binary = args.solver or os.environ.get("WAFAN_Z3_PATH")
    if not binary and not args.no_auto_solver:
        downloaded = ensure_z3_noodler()
        binary = str(downloaded) if downloaded is not None else None
    binary = binary or "z3"
    argv = [binary, "-in"]
    if args.solver_args:
        argv += args.solver_args.split()
    return SubprocessSolver(argv=argv, timeout=args.timeout)


_SEP = "-" * 66


def _load_rules(confs: list[Path]) -> list:
    """Concatenate the rules of every conf file, in include order."""
    rules = []
    for conf in confs:
        rules.extend(parse_file(conf))
    return rules


def _conf_label(confs: list[Path]) -> str:
    return " ".join(str(c) for c in confs)


def _chain_ids(chain) -> list:
    return [r.rule_id for r in chain]


def _chain_details(rules: list, emit=None) -> list[dict]:
    """Classify every chain in *rules* by why it can/can't reach the solver.

    Returns one entry per chain: its rule ids, human-readable label, a
    ``status`` of ``ok`` / ``unsupported_operator`` / ``unsupported_transform``
    / ``unsupported_pattern``, and a ``detail`` string naming the concrete
    unsupported construct (e.g. which transform or operator, and on which
    rule id; empty for ``"ok"``). Used for the ``--json`` output so that rule
    files containing constructs wafan can't model are reported explicitly —
    with which concrete rules are affected — rather than silently dropped
    from the pairwise analysis.

    If *emit* is given, each entry is passed to it (kind="chain") as soon as
    it's computed, ahead of the (usually much slower) pairwise solver loop —
    so this classification survives even if the process is killed shortly
    after starting.
    """
    chains = group_chains(rules)
    details = []
    for chain in chains:
        status, detail = chain_support_detail(chain)
        entry = {
            "rule_ids": _chain_ids(chain),
            "label": _chain_label(chain, pat_width=50),
            "status": status,
            "detail": detail,
        }
        details.append(entry)
        if emit is not None:
            emit({"kind": "chain", **entry})
    return details


def _chain_support_stats(chain_details: list[dict]) -> dict:
    counts = {"ok": 0, "unsupported_operator": 0, "unsupported_transform": 0, "unsupported_pattern": 0}
    for d in chain_details:
        counts[d["status"]] += 1
    return {"chains_total": len(chain_details), **counts}


def _print_json(payload: dict) -> None:
    print(json.dumps(payload, sort_keys=True), flush=True)


def _subsumption_pair_json(res) -> dict:
    outcome = {
        SolverResult.UNSAT: "subsumed",
        SolverResult.SAT: "not_subsumed",
        SolverResult.UNKNOWN: "unknown",
    }[res.result]
    return {
        "chain1": _chain_ids(res.chain1),
        "chain2": _chain_ids(res.chain2),
        "label": f"{_chain_label(res.chain1, pat_width=50)}  subsumed by  {_chain_label(res.chain2, pat_width=50)}",
        "result": outcome,
        "skipped": res.skipped,
        "skip_reason": res.skip_reason,
        "elapsed_sec": round(res.elapsed_sec, 3),
        "error": res.error,
    }


def _run_subsumption(confs: list[Path], solver: SubprocessSolver, verbosity: int = 0, as_json: bool = False) -> int:
    start = time.monotonic()
    rules = _load_rules(confs)
    if verbosity >= 1 and not as_json:
        print(f"Loaded {len(rules)} rules from {_conf_label(confs)}")
    chain_details = _chain_details(rules, emit=_print_json if as_json else None)
    support = _chain_support_stats(chain_details)
    checker = SubsumptionChecker(solver, verbosity=0 if as_json else verbosity)

    on_result = (
        (lambda res: _print_json({"kind": "pair", **_subsumption_pair_json(res)}))
        if as_json else None
    )
    results = checker.find_subsumed_chains(rules, include_skipped=as_json, on_result=on_result)

    checked = [r for r in results if not r.skipped]
    subsumed = [r for r in checked if r.result == SolverResult.UNSAT]
    not_subsumed = [r for r in checked if r.result == SolverResult.SAT]
    unknown = [r for r in checked if r.result == SolverResult.UNKNOWN]

    if as_json:
        highlighted = {c.chain1[0].rule_id for c in subsumed}
        _print_json({
            "kind": "summary",
            "conf": _conf_label(confs),
            "analysis": "subsumption",
            "rules_total": len(rules),
            "elapsed_sec": round(time.monotonic() - start, 3),
            **support,
            "pairs_checked": len(checked),
            "pairs_succeeded": len(subsumed) + len(not_subsumed),
            "pairs_subsumed": len(subsumed),
            "pairs_not_subsumed": len(not_subsumed),
            "pairs_unknown": len(unknown),
            "chains_highlighted": len(highlighted),
            "solver_queries": solver.query_count,
            "solver_timeouts": solver.timeout_count,
            "solver_errors": solver.error_count,
        })
        return 0

    if verbosity >= 1:
        print(f"\n{_SEP}")
    if not subsumed:
        print("No subsumed rule pairs found.")
    else:
        print(f"Subsumed pairs  ({len(subsumed)} found)\n")
        for res in subsumed:
            print(f"  {_chain_label(res.chain1, pat_width=50)}")
            print(f"    ⊆  {_chain_label(res.chain2, pat_width=50)}")
        print(f"\n{len(not_subsumed)} pair(s) checked and found not subsumed.")
    if unknown:
        print(f"{len(unknown)} pair(s) returned unknown (solver timeout or unknown result).")
    return 0


def _intersection_pair_json(res) -> dict:
    outcome = intersection_outcome_label(res.result)
    return {
        "chain1": _chain_ids(res.chain1),
        "chain2": _chain_ids(res.chain2),
        "label": f"{_chain_label(res.chain1, pat_width=50)}  ∩  {_chain_label(res.chain2, pat_width=50)}",
        "result": outcome,
        "skipped": res.skipped,
        "skip_reason": res.skip_reason,
        "elapsed_sec": round(res.elapsed_sec, 3),
        "error": res.error,
    }


def _run_intersection(confs: list[Path], solver: SubprocessSolver, verbosity: int = 0, as_json: bool = False) -> int:
    start = time.monotonic()
    rules = _load_rules(confs)
    if verbosity >= 1 and not as_json:
        print(f"Loaded {len(rules)} rules from {_conf_label(confs)}")
    chain_details = _chain_details(rules, emit=_print_json if as_json else None)
    support = _chain_support_stats(chain_details)
    checker = IntersectionChecker(solver, verbosity=0 if as_json else verbosity)

    on_result = (
        (lambda res: _print_json({"kind": "pair", **_intersection_pair_json(res)}))
        if as_json else None
    )
    results = checker.find_intersecting_chains(rules, include_skipped=as_json, on_result=on_result)

    checked = [r for r in results if not r.skipped]
    intersecting = [r for r in checked if r.result == SolverResult.SAT]
    disjoint = [r for r in checked if r.result == SolverResult.UNSAT]
    unknown = [r for r in checked if r.result == SolverResult.UNKNOWN]

    if as_json:
        highlighted = set()
        for res in intersecting:
            highlighted.add(res.chain1[0].rule_id)
            highlighted.add(res.chain2[0].rule_id)
        _print_json({
            "kind": "summary",
            "conf": _conf_label(confs),
            "analysis": "intersection",
            "rules_total": len(rules),
            "elapsed_sec": round(time.monotonic() - start, 3),
            **support,
            "pairs_checked": len(checked),
            "pairs_succeeded": len(intersecting) + len(disjoint),
            "pairs_intersecting": len(intersecting),
            "pairs_disjoint": len(disjoint),
            "pairs_unknown": len(unknown),
            "chains_highlighted": len(highlighted),
            "solver_queries": solver.query_count,
            "solver_timeouts": solver.timeout_count,
            "solver_errors": solver.error_count,
        })
        return 0

    if verbosity >= 1:
        print(f"\n{_SEP}")
    if not intersecting:
        print("No intersecting rule pairs found.")
    else:
        print(f"Intersecting pairs  ({len(intersecting)} found)\n")
        for res in intersecting:
            print(f"  {_chain_label(res.chain1, pat_width=50)}")
            print(f"    ∩  {_chain_label(res.chain2, pat_width=50)}")
        print(f"\n{len(disjoint)} pair(s) checked and found disjoint.")
    if unknown:
        print(f"{len(unknown)} pair(s) returned unknown (solver timeout or unknown result).")
    return 0


def _contradiction_pair_json(res) -> dict:
    outcome = intersection_outcome_label(res.result)
    return {
        "chain1": _chain_ids(res.chain1),
        "chain2": _chain_ids(res.chain2),
        "label": f"{_chain_label(res.chain1, pat_width=50)}  ⨯  {_chain_label(res.chain2, pat_width=50)}",
        "result": outcome,
        "contradiction": res.is_contradiction,
        "disposition1": chain_disposition(res.chain1),
        "disposition2": chain_disposition(res.chain2),
        "skipped": res.skipped,
        "skip_reason": res.skip_reason,
        "elapsed_sec": round(res.elapsed_sec, 3),
        "error": res.error,
    }


def _run_contradiction(confs: list[Path], solver: SubprocessSolver, verbosity: int = 0, as_json: bool = False) -> int:
    start = time.monotonic()
    rules = _load_rules(confs)
    if verbosity >= 1 and not as_json:
        print(f"Loaded {len(rules)} rules from {_conf_label(confs)}")
    chain_details = _chain_details(rules, emit=_print_json if as_json else None)
    support = _chain_support_stats(chain_details)
    checker = ContradictionChecker(solver, verbosity=0 if as_json else verbosity)

    on_result = (
        (lambda res: _print_json({"kind": "pair", **_contradiction_pair_json(res)}))
        if as_json else None
    )
    results = checker.find_contradicting_chains(rules, include_skipped=as_json, on_result=on_result)

    checked = [r for r in results if not r.skipped]
    contradicting = [r for r in checked if r.is_contradiction]
    intersecting = [r for r in checked if r.result == SolverResult.SAT and not r.is_contradiction]
    disjoint = [r for r in checked if r.result == SolverResult.UNSAT]
    unknown = [r for r in checked if r.result == SolverResult.UNKNOWN]

    if as_json:
        highlighted = set()
        for res in contradicting:
            highlighted.add(res.chain1[0].rule_id)
            highlighted.add(res.chain2[0].rule_id)
        _print_json({
            "kind": "summary",
            "conf": _conf_label(confs),
            "analysis": "contradiction",
            "rules_total": len(rules),
            "elapsed_sec": round(time.monotonic() - start, 3),
            **support,
            "pairs_checked": len(checked),
            "pairs_succeeded": len(contradicting) + len(intersecting) + len(disjoint),
            "pairs_contradicting": len(contradicting),
            "pairs_intersecting": len(intersecting),
            "pairs_disjoint": len(disjoint),
            "pairs_unknown": len(unknown),
            "chains_highlighted": len(highlighted),
            "solver_queries": solver.query_count,
            "solver_timeouts": solver.timeout_count,
            "solver_errors": solver.error_count,
        })
        return 0

    if verbosity >= 1:
        print(f"\n{_SEP}")
    if not contradicting:
        print("No contradicting rule pairs found.")
    else:
        print(f"Contradicting pairs  ({len(contradicting)} found)\n")
        for res in contradicting:
            print(f"  {_chain_label(res.chain1, pat_width=50)}  [{chain_disposition(res.chain1)}]")
            print(f"    ⨯  {_chain_label(res.chain2, pat_width=50)}  [{chain_disposition(res.chain2)}]")
        print(
            f"\n{len(intersecting)} intersecting pair(s) with no action conflict, "
            f"{len(disjoint)} disjoint pair(s) checked."
        )
    if unknown:
        print(f"{len(unknown)} pair(s) returned unknown (solver timeout or unknown result).")
    return 0


def _witness_result_json(res) -> dict:
    outcome = {
        SolverResult.SAT: "sat",
        SolverResult.UNSAT: "unsat",
        SolverResult.UNKNOWN: "unknown",
    }[res.result]
    return {
        "chain": _chain_ids(res.chain),
        "label": _chain_label(res.chain, pat_width=50),
        "result": outcome,
        "skipped": res.skipped,
        "skip_reason": res.skip_reason,
        "elapsed_sec": round(res.elapsed_sec, 3),
        "error": res.error,
        "model": res.model,
    }


def _run_witness(confs: list[Path], solver: SubprocessSolver, verbosity: int = 0, as_json: bool = False) -> int:
    start = time.monotonic()
    rules = _load_rules(confs)
    if verbosity >= 1 and not as_json:
        print(f"Loaded {len(rules)} rules from {_conf_label(confs)}")
    chain_details = _chain_details(rules, emit=_print_json if as_json else None)
    support = _chain_support_stats(chain_details)
    checker = WitnessChecker(solver, verbosity=0 if as_json else verbosity)

    on_result = (
        (lambda res: _print_json({"kind": "result", **_witness_result_json(res)}))
        if as_json else None
    )
    results = checker.find_chain_witnesses(rules, on_result=on_result)

    sat_results = [r for r in results if r.has_witness]
    unsat_results = [r for r in results if not r.skipped and r.result.value == "unsat"]
    unknown_results = [r for r in results if r.result.value == "unknown"]
    solved_unknown = [r for r in unknown_results if not r.skipped]

    if as_json:
        _print_json({
            "kind": "summary",
            "conf": _conf_label(confs),
            "analysis": "witness",
            "rules_total": len(rules),
            "elapsed_sec": round(time.monotonic() - start, 3),
            **support,
            "chains_checked": len(sat_results) + len(unsat_results) + len(solved_unknown),
            "chains_succeeded": len(sat_results) + len(unsat_results),
            "chains_sat": len(sat_results),
            "chains_unsat": len(unsat_results),
            "chains_unknown": len(solved_unknown),
            "chains_highlighted": len(sat_results),
            "solver_queries": solver.query_count,
            "solver_timeouts": solver.timeout_count,
            "solver_errors": solver.error_count,
        })
        return 0

    if verbosity >= 1:
        print(f"\n{_SEP}")
    if not sat_results:
        print("No satisfiable rules found (all rules are either unsatisfiable or unknown).")
        return 0

    print(f"Concrete triggering inputs  ({len(sat_results)} rule(s))\n")
    for res in sat_results:
        print(f"  {_chain_label(res.chain, pat_width=50)}")
        print(res.format_model())
        print()

    if unsat_results:
        print(f"Rules that never match  ({len(unsat_results)})")
        for res in unsat_results:
            print(f"  {_chain_label(res.chain, pat_width=50)}")
        print()

    if unknown_results:
        print(f"Rules with unknown result  ({len(unknown_results)}, unsupported features or timeout)")
        for res in unknown_results:
            print(f"  {_chain_label(res.chain, pat_width=50)}")

    return 0


# ---------------------------------------------------------------------------
# Stateful analyses (order-aware whole-ruleset model)
# ---------------------------------------------------------------------------

def _build_encoding(confs: list[Path], pairwise: bool = False):
    """Build the state model. A pairwise analysis asserts two rules' conditions
    in one query, so multi-valued collections need twice the array bound."""
    return StatefulEncoder(Ruleset.from_paths(confs), pairwise=pairwise).encode()


def _encoding_summary(encoding) -> dict:
    """Machine-readable description of the state model's shape and limits."""
    return {
        "directives": len(encoding.order),
        "rules": sum(1 for d in encoding.order if d.kind == "rule"),
        "sec_actions": sum(1 for d in encoding.order if d.kind == "action"),
        "state_vars": len(encoding.tx_sorts),
        "collection_members": encoding.members,
        "collection_counts_exact": encoding.closed,
        "collection_open_targets": encoding.open_targets,
        "state_vars_int": sum(1 for v in encoding.tx_sorts.values() if v == "Int"),
        "state_read_never_written": sorted(
            f"{c}.{n}" for (c, n) in encoding.never_written()
        ),
        "state_read_before_write": sorted(
            f"{c}.{n}" for (c, n) in encoding.reads_before_write
        ),
        "abstracted_directives": len(encoding.abstracted),
        "unmodelled_target_removals": len(encoding.target_removals),
        "unresolved_markers": encoding.unresolved_markers,
    }


def _reachability_json(res) -> dict:
    return {
        "rule_id": res.rule_id,
        "directive_kind": res.directive.kind,
        "position": res.position,
        "label": res.directive.label(),
        "lineno": res.directive.lineno,
        "phase": res.directive.phase,
        "verdict": res.verdict,
        "approximate": res.abstracted,
        "approximate_reason": res.abstract_reason,
        "elapsed_sec": round(res.elapsed_sec, 3),
        "error": res.error,
    }


def _run_reachability(
    confs: list[Path],
    solver: SubprocessSolver,
    verbosity: int = 0,
    as_json: bool = False,
    include_actions: bool = False,
) -> int:
    start = time.monotonic()
    encoding = _build_encoding(confs)
    if verbosity >= 1 and not as_json:
        rules = sum(1 for d in encoding.order if d.kind == "rule")
        print(f"Loaded {rules} rules from {_conf_label(confs)}")
        print(f"State model: {len(encoding.tx_sorts)} stateful variable(s)\n")

    checker = ReachabilityChecker(solver, verbosity=0 if as_json else verbosity)
    on_result = (
        (lambda r: _print_json({"kind": "rule", **_reachability_json(r)}))
        if as_json else None
    )
    results = checker.find_dead(
        encoding, on_result=on_result, include_actions=include_actions
    )

    dead = [r for r in results if r.is_dead]
    unreachable = [r for r in dead if r.verdict == UNREACHABLE]
    impossible = [r for r in dead if r.verdict == IMPOSSIBLE_MATCH]
    unknown = [r for r in results if r.verdict == "unknown"]

    if as_json:
        _print_json({
            "kind": "summary",
            "conf": _conf_label(confs),
            "analysis": "reachability",
            "elapsed_sec": round(time.monotonic() - start, 3),
            **_encoding_summary(encoding),
            "include_actions": include_actions,
            "rules_checked": sum(1 for r in results if r.directive.kind == "rule"),
            "actions_checked": sum(1 for r in results if r.directive.kind == "action"),
            "directives_checked": len(results),
            # Counted over whatever was checked; with --include-actions that
            # includes SecAction directives, so the per-kind splits are given
            # alongside rather than folding actions into "rules".
            "rules_dead": sum(1 for r in dead if r.directive.kind == "rule"),
            "actions_dead": sum(1 for r in dead if r.directive.kind == "action"),
            "directives_dead": len(dead),
            "rules_unreachable": len(unreachable),
            "rules_impossible_match": len(impossible),
            "rules_unknown": len(unknown),
            "solver_queries": solver.query_count,
            "solver_timeouts": solver.timeout_count,
            "solver_errors": solver.error_count,
        })
        return 0

    if verbosity >= 1:
        print(f"\n{_SEP}")
    noun = "directive" if include_actions else "rule"
    if not dead:
        print(f"No dead {noun}s found  ({len(results)} {noun}(s) checked).")
    else:
        print(f"Dead {noun}s  ({len(dead)} of {len(results)} checked)\n")
        if unreachable:
            print("  Never executed (control flow):")
            for r in unreachable:
                print(f"    {r.directive.label()}  line {r.directive.lineno}")
            print()
        if impossible:
            print("  Executed, but the condition can never hold:")
            for r in impossible:
                print(f"    {r.directive.label()}  line {r.directive.lineno}")
            print()
    if unknown:
        print(f"{len(unknown)} rule(s) returned unknown (solver timeout or unknown result).")
    for caveat in encoding.caveats():
        print(f"note: {caveat}")
    return 0


# `--analysis contradiction --stateful` runs the shadowing query: in an ordered
# model two disruptive rules can never both fire, so the meaningful conflict is
# an earlier rule silently pre-empting a later one (see wafan.analyses.stateful).
_STATEFUL_MODE = {
    "subsumption": SUBSUMPTION,
    "intersection": INTERSECTION,
    "contradiction": SHADOWING,
}
_STATEFUL_SYMBOL = {SUBSUMPTION: "\u2286", INTERSECTION: "\u2229", SHADOWING: "\u227b"}


def _stateful_pair_json(res) -> dict:
    return {
        "rule1": res.rule_ids[0],
        "rule2": res.rule_ids[1],
        "label": f"#{res.rule_ids[0]} {_STATEFUL_SYMBOL[res.mode]} #{res.rule_ids[1]}",
        "result": res.outcome,
        "holds": res.holds,
        "approximate": res.approximate,
        "approximate_reasons": res.approximate_reasons,
        "derived": res.derived,
        "derived_reason": res.derived_reason,
        "elapsed_sec": round(res.elapsed_sec, 3),
        "error": res.error,
    }


def _run_stateful_pairs(
    confs: list[Path],
    solver: SubprocessSolver,
    mode: str,
    verbosity: int = 0,
    as_json: bool = False,
    include_actions: bool = False,
) -> int:
    start = time.monotonic()
    encoding = _build_encoding(confs, pairwise=True)
    if verbosity >= 1 and not as_json:
        rules = sum(1 for d in encoding.order if d.kind == "rule")
        print(f"Loaded {rules} rules from {_conf_label(confs)}")
        print(f"Stateful {mode} analysis: {rules * (rules - 1)} pair(s)\n")

    checker = StatefulPairChecker(solver, _STATEFUL_MODE[mode], verbosity=0 if as_json else verbosity)
    on_result = (
        (lambda r: _print_json({"kind": "pair", **_stateful_pair_json(r)}))
        if as_json else None
    )
    kinds = ("rule", "action") if include_actions else ("rule",)
    positions = [i for i, d in enumerate(encoding.order) if d.kind in kinds]
    results = checker.find_pairs(encoding, on_result=on_result, positions=positions)

    holding = [r for r in results if r.holds]
    # A derived verdict comes from the two directives' target lists, not from
    # the solver, so it is neither a timeout nor an unknown answer.
    derived = [r for r in results if r.derived]
    unknown = [r for r in results if r.result == SolverResult.UNKNOWN and not r.derived]

    if as_json:
        _print_json({
            "kind": "summary",
            "conf": _conf_label(confs),
            "analysis": f"stateful-{mode}",
            "elapsed_sec": round(time.monotonic() - start, 3),
            **_encoding_summary(encoding),
            "pairs_checked": len(results),
            "pairs_holding": len(holding),
            "pairs_approximate": sum(1 for r in results if r.approximate),
            "pairs_derived": len(derived),
            "pairs_unknown": len(unknown),
            "solver_queries": solver.query_count,
            "solver_timeouts": solver.timeout_count,
            "solver_errors": solver.error_count,
        })
        return 0

    if verbosity >= 1:
        print(f"\n{_SEP}")
    symbol = _STATEFUL_SYMBOL[_STATEFUL_MODE[mode]]
    heading = {
        "subsumption": "Pairs where every transaction firing A also fires B",
        "intersection": "Pairs that can both fire on one common member",
        "contradiction": "Pairs where the earlier rule shadows a conflicting later one",
    }[mode]
    if not holding:
        print(f"None found  ({len(results)} pair(s) checked).")
    else:
        print(f"{heading}  ({len(holding)} found)\n")
        for r in holding:
            flag = "  (approximate)" if r.approximate else ""
            print(f"  {r.directive1.label()}")
            print(f"    {symbol}  {r.directive2.label()}{flag}")
    if derived:
        print(f"\n{len(derived)} pair(s) settled without the solver (no common target).")
    if unknown:
        print(f"{len(unknown)} pair(s) returned unknown (solver timeout or unknown result).")
    for caveat in encoding.caveats():
        print(f"note: {caveat}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    missing = [c for c in args.conf if not c.is_file()]
    if missing:
        label = " ".join(str(c) for c in missing)
        if args.json:
            _print_json({
                "kind": "summary", "conf": label,
                "analysis": args.analysis, "error": "not a file",
            })
            return 1
        print(f"error: {label} is not a file", file=sys.stderr)
        return 1

    solver = _make_solver(args)
    verbosity = 2 if args.verbose2 else (1 if args.verbose else 0)

    if args.analysis == "reachability":
        return _run_reachability(
            args.conf, solver, verbosity=verbosity, as_json=args.json,
            include_actions=args.include_actions,
        )
    if args.stateful and args.analysis in ("subsumption", "intersection", "contradiction"):
        return _run_stateful_pairs(
            args.conf, solver, args.analysis, verbosity=verbosity, as_json=args.json,
            include_actions=args.include_actions,
        )
    if args.analysis == "subsumption":
        return _run_subsumption(args.conf, solver, verbosity=verbosity, as_json=args.json)
    if args.analysis == "intersection":
        return _run_intersection(args.conf, solver, verbosity=verbosity, as_json=args.json)
    if args.analysis == "contradiction":
        return _run_contradiction(args.conf, solver, verbosity=verbosity, as_json=args.json)
    if args.analysis == "witness":
        return _run_witness(args.conf, solver, verbosity=verbosity, as_json=args.json)

    print(f"error: unknown analysis '{args.analysis}'", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
