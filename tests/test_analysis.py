"""Tests for wafan.analysis – subsumption and intersection checking.

The e2e tests use a PythonReSolver that resolves queries by extracting
patterns from the SMT2 text and checking them with Python's re module.
This is only sound for the simple patterns used in the test fixture;
it is intentionally NOT used for production code.
"""

from __future__ import annotations

import re as _re
from pathlib import Path
from typing import Callable

import pytest

from wafan.parser import parse_rx_rules, SecRule, SecRuleVariable, SecRuleAction
from wafan.smt import UnsupportedTransformError
from wafan.analysis import (
    SolverResult,
    SubprocessSolver,
    SubsumptionResult,
    SubsumptionChecker,
    subsumption_smt2,
    IntersectionResult,
    IntersectionChecker,
    intersection_smt2,
    rules_share_variable,
)

CONF = Path(__file__).parent / "data" / "subsumption.conf"
SUBSUMPTION_CONF = Path(__file__).parent / "data" / "subsumption.conf"


# ---------------------------------------------------------------------------
# Helpers / fixtures
# ---------------------------------------------------------------------------

def make_action(name: str, arg: str = "") -> SecRuleAction:
    return SecRuleAction(name=name, arg=arg)


def make_rule(
    rule_id: str = "1",
    var_name: str = "ARGS",
    pattern: str = "test",
    negated: bool = False,
    operator: str = "@rx",
    transforms: list[str] | None = None,
) -> SecRule:
    actions = [make_action("t", t) for t in (transforms or [])]
    return SecRule(
        rule_id=rule_id,
        variables=[SecRuleVariable(name=var_name)],
        operator=operator,
        operator_argument=pattern,
        negated=negated,
        actions=actions,
        chained=False,
        lineno=1,
    )


class ConstantSolver:
    """Always returns the same SolverResult (useful for logic tests)."""

    def __init__(self, result: SolverResult) -> None:
        self._result = result

    def solve(self, _smt2: str) -> SolverResult:
        return self._result


class CallbackSolver:
    """Delegates to a user-supplied callable."""

    def __init__(self, fn: Callable[[str], SolverResult]) -> None:
        self._fn = fn

    def solve(self, smt2: str) -> SolverResult:
        return self._fn(smt2)


class PythonReSolver:
    """Approximate solver using Python's re module for e2e tests.

    Extracts both assert lines from the SMT2 text, parses each condition
    (handling (not …) wrappers), then searches a fixed set of candidate
    strings.  If any candidate satisfies both asserts the query is SAT,
    otherwise UNSAT.

    Only reliable for simple patterns without complex features.  Intended
    for e2e tests only.
    """

    _CANDIDATES = [
        "", "a", "b", "z",
        "foo", "bar", "baz", "foobar", "foobaz",
        "Foo", "FOO", "BAR", "BAZ",
        "test", "Test", "TEST",
        "abc", "xyz", "123",
        "foo bar", "foo|bar",
    ]

    @staticmethod
    def _parse_assert(line: str) -> tuple[str, bool]:
        """Return (pattern, effective_negation) for one (assert …) line."""
        inner = line[len("(assert "):-1]
        nots = 0
        while inner.startswith("(not "):
            inner = inner[5:-1]
            nots += 1
        m = _re.search(r're\.from_ecma2020 "([^"]*)"', inner)
        if not m:
            return ("", False)
        pat = m.group(1).replace("\\\\", "\\")
        return (pat, nots % 2 == 1)

    def _eval(self, pattern: str, negated: bool, s: str) -> bool:
        try:
            matched = bool(_re.fullmatch(pattern, s))
        except _re.error:
            return False
        return (not matched) if negated else matched

    def solve(self, smt2: str) -> SolverResult:
        assert_lines = [l.strip() for l in smt2.splitlines() if l.strip().startswith("(assert")]
        if len(assert_lines) != 2:
            return SolverResult.UNKNOWN

        pat1, neg1 = self._parse_assert(assert_lines[0])
        pat2, neg2 = self._parse_assert(assert_lines[1])

        if not pat1 or not pat2:
            return SolverResult.UNKNOWN

        for s in self._CANDIDATES:
            if self._eval(pat1, neg1, s) and self._eval(pat2, neg2, s):
                return SolverResult.SAT

        return SolverResult.UNSAT


@pytest.fixture(scope="module")
def py_solver() -> PythonReSolver:
    return PythonReSolver()


@pytest.fixture(scope="module")
def sub_rules() -> list[SecRule]:
    return parse_rx_rules(SUBSUMPTION_CONF)


# ---------------------------------------------------------------------------
# subsumption_smt2 – structure tests
# ---------------------------------------------------------------------------

class TestSubsumptionSmt2:
    def test_returns_string(self):
        r1 = make_rule(rule_id="1", pattern="foo")
        r2 = make_rule(rule_id="2", pattern="foo|bar")
        assert isinstance(subsumption_smt2(r1, r2), str)

    def test_contains_set_logic(self):
        r1, r2 = make_rule(pattern="a"), make_rule(pattern="b")
        assert "(set-logic" in subsumption_smt2(r1, r2)

    def test_declares_single_variable_x(self):
        r1, r2 = make_rule(pattern="a"), make_rule(pattern="b")
        assert "(declare-const x String)" in subsumption_smt2(r1, r2)

    def test_both_patterns_present(self):
        r1 = make_rule(pattern="ALPHA")
        r2 = make_rule(pattern="BETA")
        smt2 = subsumption_smt2(r1, r2)
        assert "ALPHA" in smt2
        assert "BETA" in smt2

    def test_uses_re_from_ecma2020(self):
        r1, r2 = make_rule(pattern="x"), make_rule(pattern="y")
        assert subsumption_smt2(r1, r2).count("re.from_ecma2020") == 2

    def test_ends_with_check_sat(self):
        r1, r2 = make_rule(pattern="x"), make_rule(pattern="y")
        assert subsumption_smt2(r1, r2).strip().endswith("(check-sat)")

    def test_two_assert_lines(self):
        r1, r2 = make_rule(pattern="x"), make_rule(pattern="y")
        asserts = [l for l in subsumption_smt2(r1, r2).splitlines() if "(assert" in l]
        assert len(asserts) == 2

    def test_rule_ids_in_comment(self):
        r1 = make_rule(rule_id="11")
        r2 = make_rule(rule_id="22")
        smt2 = subsumption_smt2(r1, r2)
        assert "11" in smt2 and "22" in smt2

    def test_positive_rule1_no_leading_not(self):
        r1 = make_rule(pattern="x", negated=False)
        r2 = make_rule(pattern="y")
        smt2 = subsumption_smt2(r1, r2)
        assert_lines = [l.strip() for l in smt2.splitlines() if l.strip().startswith("(assert")]
        # First assert must not be (assert (not …)) for a positive rule
        assert not assert_lines[0].startswith("(assert (not")

    def test_negated_rule1_has_not(self):
        r1 = make_rule(pattern="x", negated=True)
        r2 = make_rule(pattern="y")
        smt2 = subsumption_smt2(r1, r2)
        assert_lines = [l.strip() for l in smt2.splitlines() if l.strip().startswith("(assert")]
        assert assert_lines[0].startswith("(assert (not")

    def test_counterexample_assert_wraps_rule2_with_not(self):
        r1 = make_rule(pattern="x")
        r2 = make_rule(pattern="y", negated=False)
        smt2 = subsumption_smt2(r1, r2)
        assert_lines = [l.strip() for l in smt2.splitlines() if l.strip().startswith("(assert")]
        # Second assert is always negated (counterexample condition)
        assert assert_lines[1].startswith("(assert (not")

    def test_transform_reflected_in_smt2(self):
        r1 = make_rule(pattern="foo", transforms=["lowercase"])
        r2 = make_rule(pattern="foo|bar")
        smt2 = subsumption_smt2(r1, r2)
        assert "str.to_lower" in smt2

    def test_unsupported_transform_raises(self):
        r1 = make_rule(pattern="x", transforms=["__unknown_transform__"])
        r2 = make_rule(pattern="y")
        with pytest.raises(UnsupportedTransformError):
            subsumption_smt2(r1, r2)


# ---------------------------------------------------------------------------
# rules_share_variable
# ---------------------------------------------------------------------------

class TestRulesShareVariable:
    def test_same_variable_true(self):
        r1 = make_rule(var_name="ARGS")
        r2 = make_rule(var_name="ARGS")
        assert rules_share_variable(r1, r2)

    def test_different_variable_false(self):
        r1 = make_rule(var_name="ARGS")
        r2 = make_rule(var_name="RESPONSE_BODY")
        assert not rules_share_variable(r1, r2)

    def test_multi_variable_overlap(self):
        r1 = SecRule("1", [SecRuleVariable("ARGS"), SecRuleVariable("BODY")], "@rx", "x", False, [], False, 1)
        r2 = SecRule("2", [SecRuleVariable("BODY"), SecRuleVariable("URI")], "@rx", "y", False, [], False, 1)
        assert rules_share_variable(r1, r2)

    def test_no_overlap_multi_variable(self):
        r1 = SecRule("1", [SecRuleVariable("A"), SecRuleVariable("B")], "@rx", "x", False, [], False, 1)
        r2 = SecRule("2", [SecRuleVariable("C"), SecRuleVariable("D")], "@rx", "y", False, [], False, 1)
        assert not rules_share_variable(r1, r2)


# ---------------------------------------------------------------------------
# SubsumptionChecker.check_pair – unit tests with ConstantSolver
# ---------------------------------------------------------------------------

class TestCheckPair:
    def test_unsat_gives_subsumed(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        res = checker.check_pair(make_rule(rule_id="1"), make_rule(rule_id="2"))
        assert res.is_subsumed

    def test_sat_gives_not_subsumed(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.SAT))
        res = checker.check_pair(make_rule(rule_id="1"), make_rule(rule_id="2"))
        assert not res.is_subsumed

    def test_unknown_from_solver_propagates(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNKNOWN))
        res = checker.check_pair(make_rule(rule_id="1"), make_rule(rule_id="2"))
        assert res.result == SolverResult.UNKNOWN

    def test_disjoint_variables_returns_unknown(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        r1 = make_rule(var_name="ARGS")
        r2 = make_rule(var_name="RESPONSE_BODY")
        res = checker.check_pair(r1, r2)
        assert res.result == SolverResult.UNKNOWN

    def test_unsupported_transform_returns_unknown(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        r1 = make_rule(transforms=["__unknown_transform__"])
        r2 = make_rule()
        assert checker.check_pair(r1, r2).result == SolverResult.UNKNOWN

    def test_result_carries_both_rules(self):
        r1 = make_rule(rule_id="A")
        r2 = make_rule(rule_id="B")
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        res = checker.check_pair(r1, r2)
        assert res.rule1.rule_id == "A"
        assert res.rule2.rule_id == "B"

    def test_solver_receives_smt2_text(self):
        received: list[str] = []

        def capture(smt2: str) -> SolverResult:
            received.append(smt2)
            return SolverResult.UNSAT

        checker = SubsumptionChecker(CallbackSolver(capture))
        checker.check_pair(make_rule(rule_id="1", pattern="foo"), make_rule(rule_id="2", pattern="bar"))
        assert len(received) == 1
        assert "foo" in received[0]
        assert "bar" in received[0]


# ---------------------------------------------------------------------------
# SubsumptionChecker.find_subsumed – unit tests
# ---------------------------------------------------------------------------

class TestFindSubsumed:
    def test_returns_list(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.SAT))
        assert isinstance(checker.find_subsumed([make_rule()]), list)

    def test_single_rule_no_pairs(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        assert checker.find_subsumed([make_rule()]) == []

    def test_non_rx_rules_skipped(self):
        r_pm = make_rule()
        r_pm.operator = "@pm"
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        assert checker.find_subsumed([r_pm, r_pm]) == []

    def test_unknown_results_excluded(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNKNOWN))
        rules = [make_rule(rule_id="1"), make_rule(rule_id="2")]
        assert checker.find_subsumed(rules) == []

    def test_all_subsumed_when_solver_always_unsat(self):
        rules = [make_rule(rule_id=str(i)) for i in range(3)]
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        results = checker.find_subsumed(rules)
        # 3 rules → 3×2 = 6 ordered pairs
        assert len(results) == 6
        assert all(r.is_subsumed for r in results)

    def test_result_items_are_subsumption_result(self):
        rules = [make_rule(rule_id="1"), make_rule(rule_id="2")]
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        for res in checker.find_subsumed(rules):
            assert isinstance(res, SubsumptionResult)

    def test_disjoint_variable_pairs_excluded(self):
        r1 = make_rule(rule_id="1", var_name="ARGS")
        r2 = make_rule(rule_id="2", var_name="RESPONSE_BODY")
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        # Both directions are disjoint → UNKNOWN → excluded
        assert checker.find_subsumed([r1, r2]) == []


# ---------------------------------------------------------------------------
# E2E tests – full pipeline with PythonReSolver and test fixture
# ---------------------------------------------------------------------------

class TestSubsumptionE2E:
    def test_parses_fixture_conf(self, sub_rules):
        assert len(sub_rules) > 0
        ids = {r.rule_id for r in sub_rules}
        assert {"100", "200", "300", "400"}.issubset(ids)

    def test_rule_600_different_variable(self, sub_rules):
        r600 = next(r for r in sub_rules if r.rule_id == "600")
        assert r600.variables[0].name == "RESPONSE_BODY"

    def test_100_subsumed_by_200(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r200 = next(r for r in sub_rules if r.rule_id == "200")
        res = SubsumptionChecker(py_solver).check_pair(r100, r200)
        assert res.is_subsumed, "foo ⊆ foo|bar should be subsumed"

    def test_200_not_subsumed_by_100(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r200 = next(r for r in sub_rules if r.rule_id == "200")
        res = SubsumptionChecker(py_solver).check_pair(r200, r100)
        assert not res.is_subsumed, "bar triggers 200 but not 100"

    def test_100_subsumed_by_400(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r400 = next(r for r in sub_rules if r.rule_id == "400")
        res = SubsumptionChecker(py_solver).check_pair(r100, r400)
        assert res.is_subsumed, "foo ⊆ .+"

    def test_200_subsumed_by_400(self, sub_rules, py_solver):
        r200 = next(r for r in sub_rules if r.rule_id == "200")
        r400 = next(r for r in sub_rules if r.rule_id == "400")
        res = SubsumptionChecker(py_solver).check_pair(r200, r400)
        assert res.is_subsumed, "foo|bar ⊆ .+"

    def test_300_subsumed_by_400(self, sub_rules, py_solver):
        r300 = next(r for r in sub_rules if r.rule_id == "300")
        r400 = next(r for r in sub_rules if r.rule_id == "400")
        res = SubsumptionChecker(py_solver).check_pair(r300, r400)
        assert res.is_subsumed, "baz ⊆ .+"

    def test_300_not_subsumed_by_200(self, sub_rules, py_solver):
        r200 = next(r for r in sub_rules if r.rule_id == "200")
        r300 = next(r for r in sub_rules if r.rule_id == "300")
        res = SubsumptionChecker(py_solver).check_pair(r300, r200)
        assert not res.is_subsumed, "baz does not match foo|bar"

    def test_400_not_subsumed_by_100(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r400 = next(r for r in sub_rules if r.rule_id == "400")
        res = SubsumptionChecker(py_solver).check_pair(r400, r100)
        assert not res.is_subsumed, ".+ is broader than foo"

    def test_600_not_paired_with_args_rules(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r600 = next(r for r in sub_rules if r.rule_id == "600")
        res = SubsumptionChecker(py_solver).check_pair(r100, r600)
        assert res.result == SolverResult.UNKNOWN, "different variables → UNKNOWN"

    def test_find_subsumed_finds_expected_pairs(self, sub_rules, py_solver):
        checker = SubsumptionChecker(py_solver)
        results = checker.find_subsumed(sub_rules)
        subsumed_pairs = {(r.rule1.rule_id, r.rule2.rule_id) for r in results if r.is_subsumed}
        # Known subsumed pairs (with PythonReSolver approximation)
        assert ("100", "200") in subsumed_pairs
        assert ("100", "400") in subsumed_pairs
        assert ("200", "400") in subsumed_pairs
        assert ("300", "400") in subsumed_pairs

    def test_find_subsumed_excludes_non_subsumed(self, sub_rules, py_solver):
        checker = SubsumptionChecker(py_solver)
        results = checker.find_subsumed(sub_rules)
        subsumed_pairs = {(r.rule1.rule_id, r.rule2.rule_id) for r in results if r.is_subsumed}
        assert ("200", "100") not in subsumed_pairs
        assert ("300", "200") not in subsumed_pairs
        assert ("400", "100") not in subsumed_pairs

    def test_find_subsumed_result_count_plausible(self, sub_rules, py_solver):
        checker = SubsumptionChecker(py_solver)
        results = checker.find_subsumed(sub_rules)
        # At least the 4 known subsumed pairs are found
        subsumed = [r for r in results if r.is_subsumed]
        assert len(subsumed) >= 4

    def test_smt2_for_real_conf_rules_is_well_formed(self):
        rules = parse_rx_rules(CONF)
        for r1 in rules[:3]:
            for r2 in rules[:3]:
                if r1.rule_id == r2.rule_id:
                    continue
                smt2 = subsumption_smt2(r1, r2)
                assert "(set-logic" in smt2
                assert "(declare-const x String)" in smt2
                assert smt2.strip().endswith("(check-sat)")


# ---------------------------------------------------------------------------
# SubprocessSolver – construction only (no real solver required)
# ---------------------------------------------------------------------------

class TestSubprocessSolver:
    def test_default_argv(self):
        s = SubprocessSolver()
        assert s.argv == ["z3", "-in"]

    def test_custom_argv(self):
        s = SubprocessSolver(argv=["z3-noodler", "--smt2"])
        assert s.argv[0] == "z3-noodler"

    def test_missing_binary_returns_unknown(self):
        s = SubprocessSolver(argv=["__no_such_binary__"])
        assert s.solve("(check-sat)") == SolverResult.UNKNOWN


# ---------------------------------------------------------------------------
# intersection_smt2 – structure tests
# ---------------------------------------------------------------------------

class TestIntersectionSmt2:
    def test_returns_string(self):
        r1, r2 = make_rule(pattern="foo"), make_rule(pattern="bar")
        assert isinstance(intersection_smt2(r1, r2), str)

    def test_contains_set_logic(self):
        r1, r2 = make_rule(pattern="a"), make_rule(pattern="b")
        assert "(set-logic" in intersection_smt2(r1, r2)

    def test_declares_single_variable_x(self):
        r1, r2 = make_rule(pattern="a"), make_rule(pattern="b")
        assert "(declare-const x String)" in intersection_smt2(r1, r2)

    def test_both_patterns_present(self):
        r1 = make_rule(pattern="ALPHA")
        r2 = make_rule(pattern="BETA")
        smt2 = intersection_smt2(r1, r2)
        assert "ALPHA" in smt2
        assert "BETA" in smt2

    def test_two_re_from_ecma2020(self):
        r1, r2 = make_rule(pattern="x"), make_rule(pattern="y")
        assert intersection_smt2(r1, r2).count("re.from_ecma2020") == 2

    def test_ends_with_check_sat(self):
        r1, r2 = make_rule(pattern="x"), make_rule(pattern="y")
        assert intersection_smt2(r1, r2).strip().endswith("(check-sat)")

    def test_two_assert_lines(self):
        r1, r2 = make_rule(pattern="x"), make_rule(pattern="y")
        asserts = [l for l in intersection_smt2(r1, r2).splitlines() if "(assert" in l]
        assert len(asserts) == 2

    def test_positive_rules_no_leading_not(self):
        r1 = make_rule(pattern="x", negated=False)
        r2 = make_rule(pattern="y", negated=False)
        smt2 = intersection_smt2(r1, r2)
        asserts = [l.strip() for l in smt2.splitlines() if l.strip().startswith("(assert")]
        assert not asserts[0].startswith("(assert (not")
        assert not asserts[1].startswith("(assert (not")

    def test_negated_rule1_has_not(self):
        r1 = make_rule(pattern="x", negated=True)
        r2 = make_rule(pattern="y", negated=False)
        smt2 = intersection_smt2(r1, r2)
        asserts = [l.strip() for l in smt2.splitlines() if l.strip().startswith("(assert")]
        assert asserts[0].startswith("(assert (not")
        assert not asserts[1].startswith("(assert (not")

    def test_negated_rule2_has_not(self):
        r1 = make_rule(pattern="x", negated=False)
        r2 = make_rule(pattern="y", negated=True)
        smt2 = intersection_smt2(r1, r2)
        asserts = [l.strip() for l in smt2.splitlines() if l.strip().startswith("(assert")]
        assert not asserts[0].startswith("(assert (not")
        assert asserts[1].startswith("(assert (not")

    def test_differs_from_subsumption_smt2(self):
        r1, r2 = make_rule(pattern="x"), make_rule(pattern="y")
        assert intersection_smt2(r1, r2) != subsumption_smt2(r1, r2)

    def test_transform_reflected(self):
        r1 = make_rule(pattern="foo", transforms=["lowercase"])
        r2 = make_rule(pattern="bar")
        assert "str.to_lower" in intersection_smt2(r1, r2)

    def test_unsupported_transform_raises(self):
        r1 = make_rule(pattern="x", transforms=["__unknown_transform__"])
        r2 = make_rule(pattern="y")
        with pytest.raises(UnsupportedTransformError):
            intersection_smt2(r1, r2)

    def test_rule_ids_in_comment(self):
        r1 = make_rule(rule_id="11")
        r2 = make_rule(rule_id="22")
        smt2 = intersection_smt2(r1, r2)
        assert "11" in smt2 and "22" in smt2


# ---------------------------------------------------------------------------
# IntersectionChecker.check_pair – unit tests
# ---------------------------------------------------------------------------

class TestIntersectionCheckPair:
    def test_sat_gives_has_intersection(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        res = checker.check_pair(make_rule(rule_id="1"), make_rule(rule_id="2"))
        assert res.has_intersection

    def test_unsat_gives_no_intersection(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.UNSAT))
        res = checker.check_pair(make_rule(rule_id="1"), make_rule(rule_id="2"))
        assert not res.has_intersection

    def test_unknown_propagates(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.UNKNOWN))
        res = checker.check_pair(make_rule(rule_id="1"), make_rule(rule_id="2"))
        assert res.result == SolverResult.UNKNOWN

    def test_disjoint_variables_returns_unknown(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        r1 = make_rule(var_name="ARGS")
        r2 = make_rule(var_name="RESPONSE_BODY")
        assert checker.check_pair(r1, r2).result == SolverResult.UNKNOWN

    def test_unsupported_transform_returns_unknown(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        r1 = make_rule(transforms=["__unknown_transform__"])
        r2 = make_rule()
        assert checker.check_pair(r1, r2).result == SolverResult.UNKNOWN

    def test_result_carries_both_rules(self):
        r1 = make_rule(rule_id="A")
        r2 = make_rule(rule_id="B")
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        res = checker.check_pair(r1, r2)
        assert res.rule1.rule_id == "A"
        assert res.rule2.rule_id == "B"

    def test_result_is_intersection_result(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        assert isinstance(checker.check_pair(make_rule(), make_rule()), IntersectionResult)

    def test_solver_receives_smt2_text(self):
        received: list[str] = []

        def capture(smt2: str) -> SolverResult:
            received.append(smt2)
            return SolverResult.SAT

        checker = IntersectionChecker(CallbackSolver(capture))
        checker.check_pair(make_rule(pattern="foo"), make_rule(pattern="bar"))
        assert len(received) == 1
        assert "foo" in received[0]
        assert "bar" in received[0]


# ---------------------------------------------------------------------------
# IntersectionChecker.find_intersecting – unit tests
# ---------------------------------------------------------------------------

class TestFindIntersecting:
    def test_returns_list(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        assert isinstance(checker.find_intersecting([make_rule()]), list)

    def test_single_rule_no_pairs(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        assert checker.find_intersecting([make_rule()]) == []

    def test_non_rx_rules_skipped(self):
        r_pm = make_rule()
        r_pm.operator = "@pm"
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        assert checker.find_intersecting([r_pm, r_pm]) == []

    def test_unknown_results_excluded(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.UNKNOWN))
        rules = [make_rule(rule_id="1"), make_rule(rule_id="2")]
        assert checker.find_intersecting(rules) == []

    def test_three_rules_unordered_pairs(self):
        # 3 rules → 3 unordered pairs
        rules = [make_rule(rule_id=str(i)) for i in range(3)]
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        assert len(checker.find_intersecting(rules)) == 3

    def test_each_pair_checked_once(self):
        calls: list[tuple[str, str]] = []

        def capture(smt2: str) -> SolverResult:
            ids = [l.split()[-1] for l in smt2.splitlines() if l.startswith("; intersection")]
            calls.append(tuple(ids[0].split("∩")) if ids else ("?", "?"))
            return SolverResult.SAT

        rules = [make_rule(rule_id=str(i)) for i in range(3)]
        IntersectionChecker(CallbackSolver(capture)).find_intersecting(rules)
        assert len(calls) == 3

    def test_disjoint_variable_pairs_excluded(self):
        r1 = make_rule(rule_id="1", var_name="ARGS")
        r2 = make_rule(rule_id="2", var_name="RESPONSE_BODY")
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        assert checker.find_intersecting([r1, r2]) == []


# ---------------------------------------------------------------------------
# E2E intersection tests with PythonReSolver
# ---------------------------------------------------------------------------

class TestIntersectionE2E:
    def test_100_and_200_intersect(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r200 = next(r for r in sub_rules if r.rule_id == "200")
        res = IntersectionChecker(py_solver).check_pair(r100, r200)
        assert res.has_intersection, "foo matches both foo and foo|bar"

    def test_100_and_300_disjoint(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r300 = next(r for r in sub_rules if r.rule_id == "300")
        res = IntersectionChecker(py_solver).check_pair(r100, r300)
        assert not res.has_intersection, "foo and baz are disjoint"

    def test_200_and_300_disjoint(self, sub_rules, py_solver):
        r200 = next(r for r in sub_rules if r.rule_id == "200")
        r300 = next(r for r in sub_rules if r.rule_id == "300")
        res = IntersectionChecker(py_solver).check_pair(r200, r300)
        assert not res.has_intersection, "foo|bar and baz are disjoint"

    def test_100_and_400_intersect(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r400 = next(r for r in sub_rules if r.rule_id == "400")
        res = IntersectionChecker(py_solver).check_pair(r100, r400)
        assert res.has_intersection, "foo matches .+"

    def test_300_and_400_intersect(self, sub_rules, py_solver):
        r300 = next(r for r in sub_rules if r.rule_id == "300")
        r400 = next(r for r in sub_rules if r.rule_id == "400")
        res = IntersectionChecker(py_solver).check_pair(r300, r400)
        assert res.has_intersection, "baz matches .+"

    def test_600_and_100_unknown_different_vars(self, sub_rules, py_solver):
        r100 = next(r for r in sub_rules if r.rule_id == "100")
        r600 = next(r for r in sub_rules if r.rule_id == "600")
        res = IntersectionChecker(py_solver).check_pair(r100, r600)
        assert res.result == SolverResult.UNKNOWN

    def test_find_intersecting_finds_expected_pairs(self, sub_rules, py_solver):
        results = IntersectionChecker(py_solver).find_intersecting(sub_rules)
        pairs = {frozenset([r.rule1.rule_id, r.rule2.rule_id]) for r in results if r.has_intersection}
        assert frozenset(["100", "200"]) in pairs
        assert frozenset(["100", "400"]) in pairs
        assert frozenset(["200", "400"]) in pairs
        assert frozenset(["300", "400"]) in pairs

    def test_find_intersecting_excludes_disjoint(self, sub_rules, py_solver):
        results = IntersectionChecker(py_solver).find_intersecting(sub_rules)
        pairs = {frozenset([r.rule1.rule_id, r.rule2.rule_id]) for r in results if r.has_intersection}
        assert frozenset(["100", "300"]) not in pairs
        assert frozenset(["200", "300"]) not in pairs

    def test_smt2_for_real_conf_intersection_is_well_formed(self):
        rules = parse_rx_rules(CONF)
        for r1 in rules[:3]:
            for r2 in rules[:3]:
                if r1.rule_id == r2.rule_id:
                    continue
                smt2 = intersection_smt2(r1, r2)
                assert "(set-logic" in smt2
                assert "(declare-const x String)" in smt2
                assert smt2.strip().endswith("(check-sat)")
