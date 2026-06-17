"""SMT solver backends used by the analyses.

The analyses are solver-agnostic: any object implementing SolverBackend can
be supplied. SubprocessSolver calls an external binary (default: z3-noodler)
via stdin/stdout using the SMT-LIB2 format produced by wafan.smt.
"""

from __future__ import annotations

import re as _re
import subprocess
from enum import Enum
from typing import Protocol


class SolverResult(Enum):
    SAT = "sat"        # counterexample found → not subsumed
    UNSAT = "unsat"    # no counterexample   → subsumed
    UNKNOWN = "unknown"


class SolverBackend(Protocol):
    """Minimal interface for an SMT solver backend."""

    def solve(self, smt2: str) -> SolverResult: ...


class SubprocessSolver:
    """Call an external SMT solver (e.g. z3-noodler) via stdin/stdout."""

    def __init__(self, argv: list[str] | None = None, timeout: int = 30) -> None:
        self.argv = argv or ["z3", "-in"]
        self.timeout = timeout

    def solve(self, smt2: str) -> SolverResult:
        try:
            proc = subprocess.run(
                self.argv,
                input=smt2,
                capture_output=True,
                text=True,
                timeout=self.timeout,
            )
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return SolverResult.UNKNOWN

        first = proc.stdout.strip().splitlines()[0] if proc.stdout.strip() else ""
        try:
            return SolverResult(first)
        except ValueError:
            return SolverResult.UNKNOWN

    def solve_with_model(self, smt2: str) -> tuple[SolverResult, dict[str, str] | None]:
        """Run solver and return (result, model).

        The model is a dict mapping variable names to their string values, or
        None if the result is not SAT or the model could not be parsed.

        The formula must include a (get-value ...) command after (check-sat),
        and the solver must be invoked with model generation enabled.  This is
        handled automatically by the witness analysis: the solver argv is
        extended with 'model=true' when needed.
        """
        model_argv = _argv_with_model(self.argv)
        try:
            proc = subprocess.run(
                model_argv,
                input=smt2,
                capture_output=True,
                text=True,
                timeout=self.timeout,
            )
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return SolverResult.UNKNOWN, None

        output = proc.stdout.strip()
        lines = output.splitlines()
        first = lines[0] if lines else ""
        try:
            result = SolverResult(first)
        except ValueError:
            return SolverResult.UNKNOWN, None

        if result != SolverResult.SAT:
            return result, None

        model = _parse_get_value_output("\n".join(lines[1:]))
        return result, model


def _argv_with_model(argv: list[str]) -> list[str]:
    """Return argv extended with model=true unless already present."""
    if any(a.startswith("model") for a in argv):
        return argv
    return argv + ["model=true"]


def _parse_get_value_output(text: str) -> dict[str, str] | None:
    """Parse z3's (get-value ...) response into {name: value} dict.

    Expected format (one or more bindings):
        ((VAR1 "value1")
         (VAR2 "value2"))

    Returns None if parsing fails.
    """
    result: dict[str, str] = {}
    for m in _re.finditer(r'\((\w+)\s+"((?:[^"\\]|\\.)*)"\)', text):
        name = m.group(1)
        value = m.group(2).replace('\\"', '"').replace("\\\\", "\\")
        result[name] = value
    return result if result else None
