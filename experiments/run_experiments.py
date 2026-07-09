#!/usr/bin/env python3
"""Batch-run wafan over a list of WAF rule files and aggregate the results.

Reads a text file listing one ModSecurity ``.conf`` path per line, invokes
``wafan --json`` on each (with the analysis/solver parameters given on the
command line), and summarises how many files succeeded, contained
unsupported constructs, timed out, or crashed.

wafan's ``--json`` output is newline-delimited JSON: one line per chain
(unsupported-construct classification), one line per pair/chain checked
(concrete rule ids, result, timing, solver error text), and a final line
with the aggregate summary for that file. Every line is flushed as soon as
it's computed. This script collects all of it into a single combined JSON
report (one file for the whole batch, per file records nested inside) plus
a CSV with one row per file for a quick overview.

Each ``.conf`` file is analysed in its own ``wafan`` subprocess so that a
crash or a runaway query on one file can't affect the rest of the batch: a
per-file wall-clock budget (``--process-timeout``) is enforced independently
of wafan's own per-SMT-query ``--timeout``, so a file can be killed even if
it is stuck in a way the solver-level timeout doesn't cover (e.g. parsing an
enormous file, or many queries each individually under the solver timeout
but summing past the budget). Because wafan flushes each NDJSON line as it
goes, a killed subprocess still leaves whatever lines it managed to print on
stdout; this script salvages that partial output instead of discarding it,
so a file that times out still contributes whatever chains/pairs it got
through before being killed.

Usage:
    python run_experiments.py --input files.txt --analysis subsumption \\
        --timeout 30 --process-timeout 600 --out-dir results/
"""

from __future__ import annotations

import argparse
import csv
import json
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any


@dataclass
class FileResult:
    conf: str
    status: str  # ok | missing_file | error | parse_error | process_timeout | incomplete
    wall_sec: float
    error: str = ""
    summary: dict[str, Any] | None = None
    records: list[dict[str, Any]] = field(default_factory=list)  # chain/pair/result lines


def read_file_list(path: Path) -> list[str]:
    lines = []
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        lines.append(line)
    return lines


def _parse_ndjson(text: str) -> tuple[dict[str, Any] | None, list[dict[str, Any]]]:
    """Split wafan's --json stdout into (summary, other_records).

    Lines that aren't valid JSON (e.g. a line truncated by a kill signal
    mid-write) are silently skipped rather than failing the whole parse,
    since NDJSON lines are independent and earlier ones are still useful.
    """
    summary: dict[str, Any] | None = None
    records: list[dict[str, Any]] = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if obj.get("kind") == "summary":
            summary = obj
        else:
            records.append(obj)
    return summary, records


def run_one(
    conf: str,
    analysis: str,
    query_timeout: int,
    process_timeout: int,
    solver: str | None,
    solver_args: str,
    no_auto_solver: bool,
    wafan_cmd: list[str],
) -> FileResult:
    conf_path = Path(conf)
    if not conf_path.is_file():
        return FileResult(conf=conf, status="missing_file", wall_sec=0.0, error="file not found")

    cmd = [
        *wafan_cmd,
        str(conf_path),
        "--analysis", analysis,
        "--timeout", str(query_timeout),
        "--json",
    ]
    if solver:
        cmd += ["--solver", solver]
    if solver_args:
        cmd += ["--solver-args", solver_args]
    if no_auto_solver:
        cmd.append("--no-auto-solver")

    start = time.monotonic()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=process_timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        proc.kill()
        # Second communicate() (no timeout) drains whatever was already
        # buffered plus anything flushed before the kill signal landed, so
        # NDJSON lines wafan wrote before being killed aren't lost.
        stdout, stderr = proc.communicate()
    wall_sec = time.monotonic() - start

    summary, records = _parse_ndjson(stdout or "")

    if timed_out:
        return FileResult(
            conf=conf, status="process_timeout", wall_sec=wall_sec,
            error=f"exceeded --process-timeout ({process_timeout}s)",
            summary=summary, records=records,
        )

    if proc.returncode != 0:
        return FileResult(
            conf=conf, status="error", wall_sec=wall_sec,
            error=(stderr or stdout or "").strip()[-2000:],
            summary=summary, records=records,
        )

    if summary is not None and "error" in summary:
        return FileResult(conf=conf, status="error", wall_sec=wall_sec, error=str(summary["error"]))

    if summary is None:
        return FileResult(
            conf=conf, status=("parse_error" if not records else "incomplete"), wall_sec=wall_sec,
            error="no summary line found in wafan output", records=records,
        )

    return FileResult(conf=conf, status="ok", wall_sec=wall_sec, summary=summary, records=records)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--input", type=Path, required=True, help="File listing one .conf path per line.")
    p.add_argument("--analysis", choices=["subsumption", "intersection", "witness"], default="subsumption")
    p.add_argument("--timeout", type=int, default=30, help="Per-SMT-query timeout in seconds, forwarded to wafan (default: 30).")
    p.add_argument("--process-timeout", type=int, default=600, help="Wall-clock budget per file in seconds; the wafan subprocess is killed if exceeded (default: 600).")
    p.add_argument("--solver", default=None, help="Forwarded to wafan --solver.")
    p.add_argument("--solver-args", default="", help="Forwarded to wafan --solver-args.")
    p.add_argument("--no-auto-solver", action="store_true", help="Forwarded to wafan --no-auto-solver.")
    p.add_argument("--wafan-cmd", default=f"{sys.executable} -m wafan", help="Command used to invoke wafan (default: '%(default)s').")
    p.add_argument("--jobs", type=int, default=1, help="Number of files to analyse concurrently (default: 1, sequential).")
    p.add_argument("--out-dir", type=Path, default=Path("results"), help="Directory to write the combined JSON/CSV report into (default: ./results).")
    return p


def aggregate(results: list[FileResult]) -> dict[str, Any]:
    total = len(results)
    by_status: dict[str, int] = {}
    for r in results:
        by_status[r.status] = by_status.get(r.status, 0) + 1

    numeric_totals: dict[str, float] = {}
    for r in results:
        if r.summary is None:
            continue
        for key, value in r.summary.items():
            if isinstance(value, (int, float)) and not isinstance(value, bool):
                numeric_totals[key] = numeric_totals.get(key, 0) + value

    return {
        "files_total": total,
        "by_status": by_status,
        "sum_over_files_with_a_summary": numeric_totals,
    }


def _scalar_summary(summary: dict[str, Any] | None) -> dict[str, Any]:
    if not summary:
        return {}
    return {k: v for k, v in summary.items() if not isinstance(v, (list, dict))}


def write_csv(results: list[FileResult], path: Path) -> None:
    stat_keys: list[str] = []
    seen = set()
    for r in results:
        for key in _scalar_summary(r.summary):
            if key not in seen:
                seen.add(key)
                stat_keys.append(key)

    fieldnames = ["conf", "status", "wall_sec", "error", "record_count", *stat_keys]
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in results:
            row = {
                "conf": r.conf, "status": r.status, "wall_sec": round(r.wall_sec, 3),
                "error": r.error, "record_count": len(r.records),
            }
            row.update(_scalar_summary(r.summary))
            writer.writerow(row)


def write_json_report(
    results: list[FileResult], summary: dict[str, Any], path: Path, input_path: Path, args: argparse.Namespace,
) -> None:
    """Write one combined JSON file for the whole batch: parameters, the
    aggregate summary, and every file's full detail (chain classifications,
    per-pair/per-chain results, and partial records salvaged from timed-out
    or crashed subprocesses) nested under "files".
    """
    report = {
        "input_file": str(input_path),
        "analysis": args.analysis,
        "generated_at": datetime.now().isoformat(timespec="seconds"),
        "parameters": {
            "timeout": args.timeout,
            "process_timeout": args.process_timeout,
            "solver": args.solver,
            "solver_args": args.solver_args,
            "no_auto_solver": args.no_auto_solver,
        },
        "aggregate": summary,
        "files": [
            {
                "conf": r.conf,
                "status": r.status,
                "wall_sec": round(r.wall_sec, 3),
                "error": r.error,
                "summary": r.summary,
                "records": r.records,
            }
            for r in results
        ],
    }
    path.write_text(json.dumps(report, indent=2, sort_keys=True))


def print_summary(summary: dict[str, Any], analysis: str) -> None:
    print(f"\nAnalysis: {analysis}")
    print(f"Files total:      {summary['files_total']}")
    for status, count in sorted(summary["by_status"].items()):
        print(f"  {status:<16} {count}")

    totals = summary["sum_over_files_with_a_summary"]
    if not totals:
        return
    print("\nTotals across files that produced a summary (includes partial/timed-out files with one):")
    for key in sorted(totals):
        value = totals[key]
        value_str = f"{value:g}" if isinstance(value, float) else str(value)
        print(f"  {key:<26} {value_str}")


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    if not args.input.is_file():
        print(f"error: {args.input} is not a file", file=sys.stderr)
        return 1

    confs = read_file_list(args.input)
    if not confs:
        print(f"error: {args.input} contains no file paths", file=sys.stderr)
        return 1

    wafan_cmd = args.wafan_cmd.split()

    results: list[FileResult] = []
    if args.jobs <= 1:
        for i, conf in enumerate(confs, 1):
            print(f"[{i}/{len(confs)}] {conf}", file=sys.stderr)
            results.append(run_one(
                conf, args.analysis, args.timeout, args.process_timeout,
                args.solver, args.solver_args, args.no_auto_solver, wafan_cmd,
            ))
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {
                pool.submit(
                    run_one, conf, args.analysis, args.timeout, args.process_timeout,
                    args.solver, args.solver_args, args.no_auto_solver, wafan_cmd,
                ): conf
                for conf in confs
            }
            done = 0
            for fut in as_completed(futures):
                done += 1
                print(f"[{done}/{len(confs)}] {futures[fut]}", file=sys.stderr)
                results.append(fut.result())
        order = {conf: i for i, conf in enumerate(confs)}
        results.sort(key=lambda r: order[r.conf])

    args.out_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    base = f"{args.input.stem}-{stamp}"
    json_path = args.out_dir / f"{base}.json"
    csv_path = args.out_dir / f"{base}.csv"

    summary = aggregate(results)
    write_json_report(results, summary, json_path, args.input, args)
    write_csv(results, csv_path)

    print_summary(summary, args.analysis)
    print(f"\nCombined report: {json_path}")
    print(f"Overview CSV:    {csv_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
