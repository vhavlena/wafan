"""Helpers for browse_results.ipynb: load wafan JSON reports and shape them into DataFrames."""
from __future__ import annotations

import glob
import json
import os

import pandas as pd

RESULTS_DIR = os.path.join(os.path.dirname(__file__), "..", "results")


def load_reports(results_dir: str = RESULTS_DIR) -> dict[str, dict]:
    """Map report path -> parsed JSON, for every *.json report in results_dir."""
    return {p: json.load(open(p)) for p in sorted(glob.glob(f"{results_dir}/*.json"))}


def report_index(reports: dict[str, dict]) -> pd.DataFrame:
    """One row per report: path, analysis, generated_at, files_total."""
    return pd.DataFrame([
        {"path": p, "analysis": r["analysis"], "generated_at": r["generated_at"],
         "files_total": r["aggregate"]["files_total"]}
        for p, r in reports.items()
    ]).sort_values("generated_at").reset_index(drop=True)


def latest_per_analysis(index_df: pd.DataFrame) -> pd.DataFrame:
    """Most recent report per analysis type."""
    return index_df.loc[index_df.groupby("analysis")["generated_at"].idxmax()].reset_index(drop=True)


def file_summary(reports: dict[str, dict]) -> pd.DataFrame:
    """One row per (report, conf file): status, timing, and the file's summary counters."""
    rows = []
    for p, r in reports.items():
        for f in r["files"]:
            row = {"report": os.path.basename(p), "analysis": r["analysis"],
                   "conf": f["conf"], "status": f["status"], "wall_sec": f["wall_sec"], "error": f["error"]}
            row.update(f.get("summary") or {})
            rows.append(row)
    return pd.DataFrame(rows)


def aggregate_stats(files_df: pd.DataFrame) -> pd.DataFrame:
    """Per-report sums of the numeric summary counters (pairs, chains, solver stats)."""
    num_cols = ["pairs_checked", "pairs_disjoint", "pairs_intersecting", "pairs_unknown",
                "chains_total", "chains_highlighted", "solver_timeouts", "solver_errors",
                "unsupported_operator", "unsupported_pattern", "unsupported_transform"]
    cols = [c for c in num_cols if c in files_df.columns]
    return files_df.groupby("report")[cols].sum()


def _all_records(reports: dict[str, dict], kind: str):
    for p, r in reports.items():
        for f in r["files"]:
            for rec in f.get("records", []):
                if rec["kind"] == kind:
                    yield os.path.basename(p), f["conf"], rec


def chain_status_counts(reports: dict[str, dict]) -> pd.DataFrame:
    """Chain-record status counts per report (ok / unsupported_transform / unsupported_operator / ...)."""
    rows = [{"report": rep, "status": rec.get("status") or "unknown"}
            for rep, _conf, rec in _all_records(reports, "chain")]
    if not rows:
        return pd.DataFrame()
    return pd.crosstab(pd.DataFrame(rows)["report"], pd.DataFrame(rows)["status"])


def unsupported_details(reports: dict[str, dict]) -> pd.DataFrame:
    """One row per chain record whose status is not ok, with its label (which feature triggered it)."""
    rows = [{"report": rep, "conf": conf, "status": rec["status"], "label": rec["label"]}
            for rep, conf, rec in _all_records(reports, "chain") if rec.get("status") not in (None, "ok")]
    return pd.DataFrame(rows)


def _classify_pair(rec: dict) -> str:
    if rec.get("skipped"):
        return "skipped: " + (rec.get("skip_reason") or "unknown reason")
    err = rec.get("error") or ""
    if "timed out" in err:
        return "solver timeout"
    if err:
        return "solver error"
    return rec.get("result", "unknown")


def pair_outcome_counts(reports: dict[str, dict]) -> pd.DataFrame:
    """Pair-record outcome counts per report: disjoint/intersecting/skipped reasons/solver timeouts/errors."""
    rows = [{"report": rep, "outcome": _classify_pair(rec)}
            for rep, _conf, rec in _all_records(reports, "pair")]
    if not rows:
        return pd.DataFrame()
    df = pd.DataFrame(rows)
    return pd.crosstab(df["report"], df["outcome"])


def pair_records_for(reports: dict[str, dict], path: str, conf: str) -> pd.DataFrame:
    """Full pair/chain record table for a single (report, conf) pair."""
    entry = next(f for f in reports[path]["files"] if f["conf"] == conf)
    return pd.DataFrame(entry["records"])
