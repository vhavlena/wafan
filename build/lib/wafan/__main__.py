"""Command-line entry point: python -m wafan  or  wafan (console script)."""

import argparse
import os
import sys
from pathlib import Path

from .analyses import SubprocessSolver, SubsumptionChecker, IntersectionChecker, WitnessChecker, _chain_label
from .parser import parse_file


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
            "Falls back to WAFAN_Z3_PATH env var, then 'z3'."
        ),
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
    return p


def _make_solver(args: argparse.Namespace) -> SubprocessSolver:
    binary = args.solver or os.environ.get("WAFAN_Z3_PATH") or "z3"
    argv = [binary, "-in"]
    if args.solver_args:
        argv += args.solver_args.split()
    return SubprocessSolver(argv=argv, timeout=args.timeout)


_SEP = "-" * 66


def _run_subsumption(conf: Path, solver: SubprocessSolver, verbosity: int = 0) -> int:
    rules = parse_file(conf)
    if verbosity >= 1:
        print(f"Loaded {len(rules)} rules from {conf}")
    checker = SubsumptionChecker(solver, verbosity=verbosity)
    results = checker.find_subsumed_chains(rules)

    subsumed = [r for r in results if r.is_subsumed]
    not_subsumed = [r for r in results if not r.is_subsumed]

    if verbosity >= 1:
        print(f"\n{_SEP}")
    if not subsumed:
        print("No subsumed rule pairs found.")
        return 0

    print(f"Subsumed pairs  ({len(subsumed)} found)\n")
    for res in subsumed:
        print(f"  {_chain_label(res.chain1, pat_width=50)}")
        print(f"    ⊆  {_chain_label(res.chain2, pat_width=50)}")
    print(f"\n{len(not_subsumed)} pair(s) checked and found not subsumed.")
    return 0


def _run_intersection(conf: Path, solver: SubprocessSolver, verbosity: int = 0) -> int:
    rules = parse_file(conf)
    if verbosity >= 1:
        print(f"Loaded {len(rules)} rules from {conf}")
    checker = IntersectionChecker(solver, verbosity=verbosity)
    results = checker.find_intersecting_chains(rules)

    intersecting = [r for r in results if r.has_intersection]
    disjoint = [r for r in results if not r.has_intersection]

    if verbosity >= 1:
        print(f"\n{_SEP}")
    if not intersecting:
        print("No intersecting rule pairs found.")
        return 0

    print(f"Intersecting pairs  ({len(intersecting)} found)\n")
    for res in intersecting:
        print(f"  {_chain_label(res.chain1, pat_width=50)}")
        print(f"    ∩  {_chain_label(res.chain2, pat_width=50)}")
    print(f"\n{len(disjoint)} pair(s) checked and found disjoint.")
    return 0


def _run_witness(conf: Path, solver: SubprocessSolver, verbosity: int = 0) -> int:
    rules = parse_file(conf)
    if verbosity >= 1:
        print(f"Loaded {len(rules)} rules from {conf}")
    checker = WitnessChecker(solver, verbosity=verbosity)
    results = checker.find_chain_witnesses(rules)

    sat_results = [r for r in results if r.has_witness]
    unsat_results = [r for r in results if r.result.value == "unsat"]
    unknown_results = [r for r in results if r.result.value == "unknown"]

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
        print(f"error: {args.conf} is not a file", file=sys.stderr)
        return 1

    solver = _make_solver(args)
    verbosity = 2 if args.verbose2 else (1 if args.verbose else 0)

    if args.analysis == "subsumption":
        return _run_subsumption(args.conf, solver, verbosity=verbosity)
    if args.analysis == "intersection":
        return _run_intersection(args.conf, solver, verbosity=verbosity)
    if args.analysis == "witness":
        return _run_witness(args.conf, solver, verbosity=verbosity)

    print(f"error: unknown analysis '{args.analysis}'", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
