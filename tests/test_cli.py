"""Tests for wafan.__main__ – CLI entry point."""

from pathlib import Path

import pytest

from wafan.__main__ import main, _build_parser, _make_solver
from wafan.analysis import SubprocessSolver

SUBSUMPTION_CONF = Path(__file__).parent / "data" / "subsumption.conf"
REAL_CONF = Path(__file__).parent.parent / "RESPONSE-954-DATA-LEAKAGES-IIS.conf"


class TestArgumentParser:
    def test_conf_required(self):
        with pytest.raises(SystemExit):
            _build_parser().parse_args([])

    def test_conf_positional(self):
        args = _build_parser().parse_args([str(REAL_CONF)])
        assert args.conf == REAL_CONF

    def test_default_analysis_is_subsumption(self):
        args = _build_parser().parse_args([str(REAL_CONF)])
        assert args.analysis == "subsumption"

    def test_default_solver_is_none(self):
        args = _build_parser().parse_args([str(REAL_CONF)])
        assert args.solver is None

    def test_solver_flag(self):
        args = _build_parser().parse_args([str(REAL_CONF), "--solver", "/usr/bin/z3-noodler"])
        assert args.solver == "/usr/bin/z3-noodler"

    def test_solver_args_flag(self):
        args = _build_parser().parse_args([str(REAL_CONF), "--solver-args", "--smt2 --quiet"])
        assert "--smt2" in args.solver_args

    def test_timeout_flag(self):
        args = _build_parser().parse_args([str(REAL_CONF), "--timeout", "60"])
        assert args.timeout == 60

    def test_default_timeout(self):
        args = _build_parser().parse_args([str(REAL_CONF)])
        assert args.timeout == 30

    def test_analysis_choices(self):
        args = _build_parser().parse_args([str(REAL_CONF), "--analysis", "subsumption"])
        assert args.analysis == "subsumption"

    def test_invalid_analysis_rejected(self):
        with pytest.raises(SystemExit):
            _build_parser().parse_args([str(REAL_CONF), "--analysis", "unknown"])


class TestMakeSolver:
    def test_default_solver_uses_z3(self):
        args = _build_parser().parse_args([str(REAL_CONF)])
        solver = _make_solver(args)
        assert isinstance(solver, SubprocessSolver)
        assert solver.argv[0] == "z3"

    def test_custom_solver_path(self):
        args = _build_parser().parse_args([str(REAL_CONF), "--solver", "/opt/z3-noodler"])
        solver = _make_solver(args)
        assert solver.argv[0] == "/opt/z3-noodler"

    def test_solver_receives_dash_in_flag(self):
        args = _build_parser().parse_args([str(REAL_CONF)])
        solver = _make_solver(args)
        assert "-in" in solver.argv

    def test_extra_solver_args_appended(self):
        args = _build_parser().parse_args(
            [str(REAL_CONF), "--solver-args", "--quiet --smt2"]
        )
        solver = _make_solver(args)
        assert "--quiet" in solver.argv
        assert "--smt2" in solver.argv

    def test_timeout_propagated(self):
        args = _build_parser().parse_args([str(REAL_CONF), "--timeout", "5"])
        solver = _make_solver(args)
        assert solver.timeout == 5


class TestMainFunction:
    def test_missing_file_returns_1(self):
        assert main(["nonexistent.conf"]) == 1

    def test_valid_file_returns_0_with_missing_solver(self):
        # Solver binary doesn't exist → all queries return UNKNOWN → no pairs → exit 0
        rc = main([str(SUBSUMPTION_CONF), "--solver", "__no_such_solver__"])
        assert rc == 0

    def test_help_exits(self):
        with pytest.raises(SystemExit) as exc:
            main(["--help"])
        assert exc.value.code == 0

    def test_module_runnable(self):
        import subprocess, sys
        result = subprocess.run(
            [sys.executable, "-m", "wafan", "--help"],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0
        assert "solver" in result.stdout

    def test_output_contains_solver_description(self):
        import subprocess, sys
        result = subprocess.run(
            [sys.executable, "-m", "wafan", "--help"],
            capture_output=True,
            text=True,
        )
        assert "SMT solver" in result.stdout or "solver" in result.stdout
