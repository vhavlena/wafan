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
    num_cols = ["pairs_checked", "pairs_disjoint", "pairs_intersecting", "pairs_contradicting",
                "pairs_unknown", "chains_total", "chains_highlighted", "solver_timeouts",
                "solver_errors", "unsupported_operator", "unsupported_pattern", "unsupported_transform"]
    cols = [c for c in num_cols if c in files_df.columns]
    return files_df.groupby("report")[cols].sum()


def _all_records(reports: dict[str, dict], kind: str):
    for p, r in reports.items():
        for f in r["files"]:
            for rec in f.get("records", []):
                if rec["kind"] == kind:
                    yield os.path.basename(p), r["analysis"], f["conf"], rec


def chain_status_counts(reports: dict[str, dict]) -> pd.DataFrame:
    """Chain-record status counts per report (ok / unsupported_transform / unsupported_operator / ...)."""
    rows = [{"report": rep, "status": rec.get("status") or "unknown"}
            for rep, _analysis, _conf, rec in _all_records(reports, "chain")]
    if not rows:
        return pd.DataFrame()
    return pd.crosstab(pd.DataFrame(rows)["report"], pd.DataFrame(rows)["status"])


def unsupported_details(reports: dict[str, dict]) -> pd.DataFrame:
    """One row per chain record whose status is not ok: which feature (status),
    concretely what's unsupported (detail — e.g. which transform/operator and
    rule id), and its label."""
    rows = [{"report": rep, "conf": conf, "status": rec["status"],
              "detail": rec.get("detail") or "", "label": rec["label"]}
            for rep, _analysis, conf, rec in _all_records(reports, "chain") if rec.get("status") not in (None, "ok")]
    return pd.DataFrame(rows)


# Per-analysis mapping from the raw solver "result" to whether that pair is
# the analysis's highlighted finding ("violates") or a clean pair ("ok").
# "unknown" (solver returned unknown but didn't error/time out) passes through.
_RESULT_TO_OUTCOME = {
    "intersection": {"intersecting": "violates", "disjoint": "ok"},
    "subsumption": {"subsumed": "violates", "not_subsumed": "ok"},
}


def _classify_pair(rec: dict, analysis: str) -> str:
    if rec.get("skipped"):
        # "no shared variable" is a pair-level fact with no chain-level
        # equivalent (unlike unsupported operators/transforms, which are
        # also broken out per-chain in unsupported_details()), so it gets
        # its own bucket instead of being collapsed into a generic
        # "skipped" that would hide it.
        if rec.get("skip_reason") == "no shared variable":
            return "skipped: no shared variable"
        return "skipped: unsupported"
    err = rec.get("error") or ""
    if "timed out" in err:
        return "solver timeout"
    if err:
        return "solver error"
    if analysis == "contradiction":
        # "disjoint" vs "intersecting" isn't the question contradiction asks:
        # an intersecting pair with matching disposition is still fine. Only
        # pairs with an actual accept/deny conflict are a real violation.
        return "violates" if rec.get("contradiction") else "ok"
    result = rec.get("result", "unknown")
    return _RESULT_TO_OUTCOME.get(analysis, {}).get(result, result)


def pair_outcome_counts(reports: dict[str, dict]) -> pd.DataFrame:
    """Pair-record outcome counts per (report, analysis): outcome vocabulary
    depends on the analysis (contradiction: violates/ok; intersection:
    disjoint/intersecting; subsumption: subsumed/not_subsumed), plus shared
    skipped/solver-timeout/solver-error buckets."""
    rows = [{"report": rep, "analysis": analysis, "outcome": _classify_pair(rec, analysis)}
            for rep, analysis, _conf, rec in _all_records(reports, "pair")]
    if not rows:
        return pd.DataFrame()
    df = pd.DataFrame(rows)
    counts = pd.crosstab([df["report"], df["analysis"]], df["outcome"])
    return counts.rename_axis(columns=None).reset_index()


def violating_pairs(reports: dict[str, dict]) -> pd.DataFrame:
    """One row per pair record classified as "violates" (the analysis's
    flagged finding: contradicting rules, intersecting rules, or a subsumed
    chain) — which rule chains and conf file, for drilling into specifics."""
    rows = []
    for rep, analysis, conf, rec in _all_records(reports, "pair"):
        if _classify_pair(rec, analysis) != "violates":
            continue
        row = {
            "report": rep, "analysis": analysis, "conf": conf,
            "label": rec.get("label"), "result": rec.get("result"),
            "chain1": rec.get("chain1"), "chain2": rec.get("chain2"),
        }
        if analysis == "contradiction":
            row["disposition1"] = rec.get("disposition1")
            row["disposition2"] = rec.get("disposition2")
        rows.append(row)
    return pd.DataFrame(rows)


def pair_records_for(reports: dict[str, dict], path: str, conf: str) -> pd.DataFrame:
    """Full pair/chain record table for a single (report, conf) pair."""
    entry = next(f for f in reports[path]["files"] if f["conf"] == conf)
    return pd.DataFrame(entry["records"])
