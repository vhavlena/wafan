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
    WitnessChecker,
    chain_support_status,
    _chain_label,
)
from .parser import group_chains, parse_file
from .solver_setup import ensure_z3_noodler


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wafan",
        description="SMT-based analysis of ModSecurity SecRule rulesets.",
    )
    p.add_argument("conf", type=Path, help="Path to a ModSecurity .conf file.")
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
        choices=["subsumption", "intersection", "witness"],
        default="subsumption",
        help="Analysis to run (default: subsumption). "
             "'witness' finds a concrete input satisfying each rule.",
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


def _chain_ids(chain) -> list:
    return [r.rule_id for r in chain]


def _chain_details(rules: list, emit=None) -> list[dict]:
    """Classify every chain in *rules* by why it can/can't reach the solver.

    Returns one entry per chain: its rule ids, human-readable label, and a
    ``status`` of ``ok`` / ``unsupported_operator`` / ``unsupported_transform``
    / ``unsupported_pattern``. Used for the ``--json`` output so that rule
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
        entry = {
            "rule_ids": _chain_ids(chain),
            "label": _chain_label(chain, pat_width=50),
            "status": chain_support_status(chain),
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


def _run_subsumption(conf: Path, solver: SubprocessSolver, verbosity: int = 0, as_json: bool = False) -> int:
    start = time.monotonic()
    rules = parse_file(conf)
    if verbosity >= 1 and not as_json:
        print(f"Loaded {len(rules)} rules from {conf}")
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
            "conf": str(conf),
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
    outcome = {
        SolverResult.SAT: "intersecting",
        SolverResult.UNSAT: "disjoint",
        SolverResult.UNKNOWN: "unknown",
    }[res.result]
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


def _run_intersection(conf: Path, solver: SubprocessSolver, verbosity: int = 0, as_json: bool = False) -> int:
    start = time.monotonic()
    rules = parse_file(conf)
    if verbosity >= 1 and not as_json:
        print(f"Loaded {len(rules)} rules from {conf}")
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
            "conf": str(conf),
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


def _run_witness(conf: Path, solver: SubprocessSolver, verbosity: int = 0, as_json: bool = False) -> int:
    start = time.monotonic()
    rules = parse_file(conf)
    if verbosity >= 1 and not as_json:
        print(f"Loaded {len(rules)} rules from {conf}")
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
            "conf": str(conf),
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


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    if not args.conf.is_file():
        if args.json:
            _print_json({"kind": "summary", "conf": str(args.conf), "analysis": args.analysis, "error": "not a file"})
            return 1
        print(f"error: {args.conf} is not a file", file=sys.stderr)
        return 1

    solver = _make_solver(args)
    verbosity = 2 if args.verbose2 else (1 if args.verbose else 0)

    if args.analysis == "subsumption":
        return _run_subsumption(args.conf, solver, verbosity=verbosity, as_json=args.json)
    if args.analysis == "intersection":
        return _run_intersection(args.conf, solver, verbosity=verbosity, as_json=args.json)
    if args.analysis == "witness":
        return _run_witness(args.conf, solver, verbosity=verbosity, as_json=args.json)

    print(f"error: unknown analysis '{args.analysis}'", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
