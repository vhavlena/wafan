"""Command-line entry point: python -m wafan  or  wafan (console script)."""

import argparse
import sys
from pathlib import Path

from .analysis import SubprocessSolver, SubsumptionChecker, IntersectionChecker
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
            "Path (or name) of the SMT solver binary. "
            "The solver must accept SMT-LIB2 on stdin and print sat/unsat on stdout. "
            "Default: z3 (use z3-noodler for full re.from_ecma2020 support)."
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
        choices=["subsumption", "intersection"],
        default="subsumption",
        help="Analysis to run (default: subsumption).",
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
    binary = args.solver or "z3"
    argv = [binary, "-in"]
    if args.solver_args:
        argv += args.solver_args.split()
    return SubprocessSolver(argv=argv, timeout=args.timeout)


def _run_subsumption(conf: Path, solver: SubprocessSolver, verbosity: int = 0) -> int:
    rules = parse_file(conf)
    if verbosity >= 1:
        print(f"[parse] {len(rules)} rules loaded from {conf}")
    checker = SubsumptionChecker(solver, verbosity=verbosity)
    results = checker.find_subsumed(rules)

    subsumed = [r for r in results if r.is_subsumed]
    not_subsumed = [r for r in results if not r.is_subsumed]

    if not subsumed:
        print("No subsumed rule pairs found.")
        return 0

    print(f"Found {len(subsumed)} subsumed pair(s):\n")
    for res in subsumed:
        r1, r2 = res.rule1, res.rule2
        print(
            f"  rule {r1.rule_id:>8}  ⊆  rule {r2.rule_id:<8}"
            f"  ({r1.operator_argument[:60]})"
        )

    print(f"\n{len(not_subsumed)} pair(s) checked and found NOT subsumed.")
    return 0


def _run_intersection(conf: Path, solver: SubprocessSolver, verbosity: int = 0) -> int:
    rules = parse_file(conf)
    if verbosity >= 1:
        print(f"[parse] {len(rules)} rules loaded from {conf}")
    checker = IntersectionChecker(solver, verbosity=verbosity)
    results = checker.find_intersecting(rules)

    intersecting = [r for r in results if r.has_intersection]
    disjoint = [r for r in results if not r.has_intersection]

    if not intersecting:
        print("No intersecting rule pairs found.")
        return 0

    print(f"Found {len(intersecting)} intersecting pair(s):\n")
    for res in intersecting:
        r1, r2 = res.rule1, res.rule2
        print(
            f"  rule {r1.rule_id:>8}  ∩  rule {r2.rule_id:<8}"
            f"  ({r1.operator_argument[:60]})"
        )

    print(f"\n{len(disjoint)} pair(s) checked and found disjoint.")
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

    print(f"error: unknown analysis '{args.analysis}'", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
