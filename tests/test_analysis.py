"""Tests for wafan.analyses – subsumption, intersection and witness checking.

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

from wafan.parser import parse_rx_rules, group_chains, SecRule, SecRuleVariable, SecRuleAction
from wafan.smt import UnsupportedOperatorError, UnsupportedTransformError, chain_to_smt
from wafan.analyses.common import (
    chain_common_witness,
    chain_escaping_witness,
    chains_share_target,
    solve_any,
)
from wafan.analyses.subsumption import subsumption_alternatives
from wafan.analyses import (
    SolverResult,
    SubprocessSolver,
    SubsumptionResult,
    SubsumptionChecker,
    subsumption_smt2,
    IntersectionResult,
    IntersectionChecker,
    intersection_smt2,
    rules_share_variable,
    ContradictionResult,
    ContradictionChecker,
    contradiction_smt2,
    rule_disposition,
    chain_disposition,
    WitnessResult,
    WitnessChecker,
    witness_smt2,
    ChainSubsumptionResult,
    ChainIntersectionResult,
    ChainContradictionResult,
    ChainWitnessResult,
    chain_subsumption_smt2,
    chain_intersection_smt2,
    chain_contradiction_smt2,
    chain_witness_smt2,
    chains_share_variable,
    _parse_get_value_output,
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

    def test_shared_transform_gets_single_declaration(self):
        # Same concern as intersection_smt2: a shared transform restricted
        # differently by each rule's own pattern must still collapse to one
        # consistent declaration, sized to the union of both patterns.
        r1 = make_rule(rule_id="1", pattern="A", transforms=["urlDecode"])
        r2 = make_rule(rule_id="2", pattern="Z", transforms=["urlDecode"])
        smt2 = subsumption_smt2(r1, r2)
        decls = _re.findall(r"\(define-fun t_urlDecode .*", smt2)
        assert len(decls) == 1
        assert '"\\u{41}"' in decls[0]
        assert '"\\u{5a}"' in decls[0]


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
        r_pm.operator = "@geoLookup"
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        assert checker.find_subsumed([r_pm, r_pm]) == []

    def test_solver_unknown_results_kept(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNKNOWN))
        rules = [make_rule(rule_id="1"), make_rule(rule_id="2")]
        results = checker.find_subsumed(rules)
        assert len(results) == 2
        assert all(r.result == SolverResult.UNKNOWN for r in results)

    def test_skipped_results_excluded(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        rules = [
            make_rule(rule_id="1", var_name="ARGS"),
            make_rule(rule_id="2", var_name="REQUEST_HEADERS"),
        ]
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

    def test_shared_transform_gets_single_declaration(self):
        # Both rules restrict a shared transform (urlDecode) to their own
        # narrow @rx pattern; the merged script must declare "t_urlDecode"
        # exactly once, using the union of both patterns' codepoints, not two
        # conflicting declarations for the same SMT symbol.
        r1 = make_rule(rule_id="1", pattern="A", transforms=["urlDecode"])
        r2 = make_rule(rule_id="2", pattern="Z", transforms=["urlDecode"])
        smt2 = intersection_smt2(r1, r2)
        decls = _re.findall(r"\(define-fun t_urlDecode .*", smt2)
        assert len(decls) == 1
        # Union: passes for both 'A' (0x41) and 'Z' (0x5a) must be present.
        assert '"\\u{41}"' in decls[0]
        assert '"\\u{5a}"' in decls[0]


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
        r_pm.operator = "@geoLookup"
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        assert checker.find_intersecting([r_pm, r_pm]) == []

    def test_solver_unknown_results_kept(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.UNKNOWN))
        rules = [make_rule(rule_id="1"), make_rule(rule_id="2")]
        results = checker.find_intersecting(rules)
        assert len(results) == 1
        assert results[0].result == SolverResult.UNKNOWN

    def test_skipped_results_excluded(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        rules = [
            make_rule(rule_id="1", var_name="ARGS"),
            make_rule(rule_id="2", var_name="REQUEST_HEADERS"),
        ]
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


# ---------------------------------------------------------------------------
# rule_disposition / chain_disposition – unit tests
# ---------------------------------------------------------------------------

class TestDisposition:
    def test_deny_action_is_deny(self):
        r = make_rule()
        r.actions.append(make_action("deny"))
        assert rule_disposition(r) == "deny"

    def test_drop_and_block_are_deny(self):
        for name in ("drop", "block"):
            r = make_rule()
            r.actions.append(make_action(name))
            assert rule_disposition(r) == "deny"

    def test_allow_action_is_allow(self):
        r = make_rule()
        r.actions.append(make_action("allow"))
        assert rule_disposition(r) == "allow"

    def test_pass_action_is_unknown(self):
        # "pass" is ModSecurity's no-op/continue default, not an explicit
        # allow decision (e.g. paranoia-level skipAfter guards use it purely
        # for flow control), so it must not be conflated with "allow".
        r = make_rule()
        r.actions.append(make_action("pass"))
        assert rule_disposition(r) == "unknown"

    def test_no_disruptive_action_is_unknown(self):
        r = make_rule()
        assert rule_disposition(r) == "unknown"

    def test_own_action_takes_precedence_over_inherited(self):
        r = make_rule()
        r.actions.append(make_action("allow"))
        r.inherited_actions.append(make_action("deny"))
        assert rule_disposition(r) == "allow"

    def test_inherited_action_used_as_fallback(self):
        r = make_rule()
        r.inherited_actions.append(make_action("deny"))
        assert rule_disposition(r) == "deny"

    def test_chain_disposition_checks_every_link(self):
        r1 = make_rule(rule_id="1")
        r2 = make_rule(rule_id="2")
        r2.actions.append(make_action("deny"))
        assert chain_disposition([r1, r2]) == "deny"


# ---------------------------------------------------------------------------
# ContradictionChecker.check_pair – unit tests
# ---------------------------------------------------------------------------

class TestContradictionCheckPair:
    def test_intersecting_with_conflicting_actions_is_contradiction(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        r1 = make_rule(rule_id="1")
        r1.actions.append(make_action("deny"))
        r2 = make_rule(rule_id="2")
        r2.actions.append(make_action("allow"))
        res = checker.check_pair(r1, r2)
        assert res.has_intersection
        assert res.is_contradiction

    def test_intersecting_with_same_action_is_not_contradiction(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        r1 = make_rule(rule_id="1")
        r1.actions.append(make_action("deny"))
        r2 = make_rule(rule_id="2")
        r2.actions.append(make_action("deny"))
        res = checker.check_pair(r1, r2)
        assert res.has_intersection
        assert not res.is_contradiction

    def test_intersecting_with_unknown_disposition_is_not_contradiction(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        r1 = make_rule(rule_id="1")
        r1.actions.append(make_action("deny"))
        r2 = make_rule(rule_id="2")
        res = checker.check_pair(r1, r2)
        assert res.has_intersection
        assert not res.is_contradiction

    def test_disjoint_is_not_contradiction_even_with_conflicting_actions(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.UNSAT))
        r1 = make_rule(rule_id="1")
        r1.actions.append(make_action("deny"))
        r2 = make_rule(rule_id="2")
        r2.actions.append(make_action("allow"))
        res = checker.check_pair(r1, r2)
        assert not res.has_intersection
        assert not res.is_contradiction

    def test_disjoint_variables_returns_unknown(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        r1 = make_rule(var_name="ARGS")
        r2 = make_rule(var_name="RESPONSE_BODY")
        assert checker.check_pair(r1, r2).result == SolverResult.UNKNOWN

    def test_result_is_contradiction_result(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        assert isinstance(checker.check_pair(make_rule(), make_rule()), ContradictionResult)

    def test_contradiction_smt2_matches_intersection_smt2(self):
        r1, r2 = make_rule(rule_id="1", pattern="foo"), make_rule(rule_id="2", pattern="bar")
        assert contradiction_smt2(r1, r2) == intersection_smt2(r1, r2)


# ---------------------------------------------------------------------------
# ContradictionChecker.find_contradicting – unit tests
# ---------------------------------------------------------------------------

class TestFindContradicting:
    def test_only_conflicting_pair_flagged(self):
        r1 = make_rule(rule_id="1")
        r1.actions.append(make_action("deny"))
        r2 = make_rule(rule_id="2")
        r2.actions.append(make_action("deny"))
        r3 = make_rule(rule_id="3")
        r3.actions.append(make_action("allow"))
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        results = checker.find_contradicting([r1, r2, r3])
        contradicting = {frozenset([r.rule1.rule_id, r.rule2.rule_id]) for r in results if r.is_contradiction}
        assert contradicting == {frozenset(["1", "3"]), frozenset(["2", "3"])}


# ---------------------------------------------------------------------------
# _parse_get_value_output – unit tests
# ---------------------------------------------------------------------------

class TestParseGetValueOutput:
    def test_single_variable(self):
        text = '((x "foo"))'
        result = _parse_get_value_output(text)
        assert result == {"x": "foo"}

    def test_multiple_variables(self):
        text = '((ARGS "hello")\n (REQUEST_URI "world"))'
        result = _parse_get_value_output(text)
        assert result == {"ARGS": "hello", "REQUEST_URI": "world"}

    def test_empty_string_value(self):
        text = '((x ""))'
        result = _parse_get_value_output(text)
        assert result == {"x": ""}

    def test_escaped_quotes_in_value(self):
        text = r'((x "say \"hello\""))'
        result = _parse_get_value_output(text)
        assert result is not None
        assert result["x"] == 'say "hello"'

    def test_empty_text_returns_none(self):
        assert _parse_get_value_output("") is None

    def test_no_bindings_returns_none(self):
        assert _parse_get_value_output("unsat") is None


# ---------------------------------------------------------------------------
# witness_smt2 – structure tests
# ---------------------------------------------------------------------------

class TestWitnessSmt2:
    def test_returns_string(self):
        r = make_rule(rule_id="1", pattern="foo")
        assert isinstance(witness_smt2(r), str)

    def test_contains_set_logic(self):
        r = make_rule(pattern="foo")
        assert "(set-logic" in witness_smt2(r)

    def test_declares_variable(self):
        r = make_rule(var_name="ARGS", pattern="foo")
        smt2 = witness_smt2(r)
        assert "(declare-const ARGS String)" in smt2

    def test_contains_check_sat(self):
        r = make_rule(pattern="foo")
        assert "(check-sat)" in witness_smt2(r)

    def test_ends_with_get_value(self):
        r = make_rule(var_name="ARGS", pattern="foo")
        smt2 = witness_smt2(r)
        assert smt2.strip().endswith(")")
        assert "(get-value" in smt2

    def test_pattern_present(self):
        r = make_rule(pattern="secretpattern")
        assert "secretpattern" in witness_smt2(r)

    def test_multiple_variables_in_get_value(self):
        rule = SecRule(
            rule_id="1",
            variables=[SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI")],
            operator="@rx",
            operator_argument="test",
            negated=False,
            actions=[],
            chained=False,
            lineno=1,
        )
        smt2 = witness_smt2(rule)
        assert "ARGS" in smt2
        assert "REQUEST_URI" in smt2
        assert "(get-value" in smt2

    def test_transform_reflected(self):
        r = make_rule(pattern="foo", transforms=["lowercase"])
        assert "str.to_lower" in witness_smt2(r)

    def test_unsupported_transform_raises(self):
        r = make_rule(pattern="x", transforms=["__unknown_transform__"])
        with pytest.raises(UnsupportedTransformError):
            witness_smt2(r)

    def test_non_rx_operator_raises(self):
        r = make_rule(pattern="foo")
        r.operator = "@geoLookup"
        with pytest.raises(UnsupportedOperatorError):
            witness_smt2(r)


# ---------------------------------------------------------------------------
# WitnessChecker – unit tests with mock solvers
# ---------------------------------------------------------------------------

class ModelSolver:
    """Solver stub that returns a fixed result and model."""

    def __init__(self, result: SolverResult, model: dict[str, str] | None = None) -> None:
        self._result = result
        self._model = model

    def solve(self, smt2: str) -> SolverResult:
        return self._result

    def solve_with_model(self, smt2: str) -> tuple[SolverResult, dict[str, str] | None]:
        return self._result, self._model


class TestWitnessCheckerUnit:
    def test_sat_result_has_witness(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "foo"})
        checker = WitnessChecker(solver)
        res = checker.check_rule(make_rule(rule_id="1"))
        assert res.has_witness

    def test_unsat_result_no_witness(self):
        solver = ModelSolver(SolverResult.UNSAT)
        checker = WitnessChecker(solver)
        res = checker.check_rule(make_rule(rule_id="1"))
        assert not res.has_witness

    def test_unknown_propagates(self):
        solver = ModelSolver(SolverResult.UNKNOWN)
        checker = WitnessChecker(solver)
        res = checker.check_rule(make_rule(rule_id="1"))
        assert res.result == SolverResult.UNKNOWN

    def test_model_attached_on_sat(self):
        model = {"ARGS": "hello"}
        solver = ModelSolver(SolverResult.SAT, model)
        checker = WitnessChecker(solver)
        res = checker.check_rule(make_rule(rule_id="1"))
        assert res.model == model

    def test_model_none_on_unsat(self):
        solver = ModelSolver(SolverResult.UNSAT)
        checker = WitnessChecker(solver)
        res = checker.check_rule(make_rule())
        assert res.model is None

    def test_non_rx_operator_returns_unknown(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "x"})
        checker = WitnessChecker(solver)
        r = make_rule()
        r.operator = "@geoLookup"
        res = checker.check_rule(r)
        assert res.result == SolverResult.UNKNOWN

    def test_unsupported_transform_returns_unknown(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "x"})
        checker = WitnessChecker(solver)
        r = make_rule(transforms=["__unknown_transform__"])
        res = checker.check_rule(r)
        assert res.result == SolverResult.UNKNOWN

    def test_result_carries_rule(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "v"})
        checker = WitnessChecker(solver)
        r = make_rule(rule_id="42")
        res = checker.check_rule(r)
        assert res.rule.rule_id == "42"

    def test_find_witnesses_returns_all_rx_rules(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "v"})
        checker = WitnessChecker(solver)
        rules = [make_rule(rule_id=str(i)) for i in range(3)]
        results = checker.find_witnesses(rules)
        assert len(results) == 3

    def test_find_witnesses_skips_non_rx(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "v"})
        checker = WitnessChecker(solver)
        r_pm = make_rule()
        r_pm.operator = "@geoLookup"
        results = checker.find_witnesses([r_pm, make_rule(rule_id="2")])
        assert len(results) == 1

    def test_format_model_no_model(self):
        res = WitnessResult(make_rule(), SolverResult.UNKNOWN, None)
        assert res.format_model() == "    (no model)"

    def test_format_model_with_model(self):
        res = WitnessResult(make_rule(), SolverResult.SAT, {"ARGS": "hello"})
        out = res.format_model()
        assert "ARGS" in out
        assert "hello" in out


# ---------------------------------------------------------------------------
# WitnessChecker – E2E tests with real z3 solver
# ---------------------------------------------------------------------------

import os as _os

# Requires a z3 build with re.from_ecma2020 support (not in mainstream z3).
# Set WAFAN_Z3_PATH to the path of such a binary to enable E2E tests.
Z3_PATH = _os.environ.get("WAFAN_Z3_PATH")
_Z3_AVAILABLE = Z3_PATH is not None and _os.path.exists(Z3_PATH)


@pytest.fixture(scope="module")
def z3_solver() -> SubprocessSolver:
    return SubprocessSolver(argv=[Z3_PATH, "-in"], timeout=30)


@pytest.mark.skipif(not _Z3_AVAILABLE, reason="WAFAN_Z3_PATH not set or binary not found")
class TestWitnessE2E:
    def test_simple_pattern_has_witness(self, z3_solver):
        r = make_rule(rule_id="1", var_name="ARGS", pattern="foo|bar")
        checker = WitnessChecker(z3_solver)
        res = checker.check_rule(r)
        assert res.has_witness
        assert res.model is not None
        assert "ARGS" in res.model

    def test_witness_value_satisfies_pattern(self, z3_solver):
        import re
        r = make_rule(rule_id="1", var_name="ARGS", pattern="foo|bar")
        checker = WitnessChecker(z3_solver)
        res = checker.check_rule(r)
        assert res.has_witness and res.model is not None
        value = res.model.get("ARGS", "")
        assert re.fullmatch("foo|bar", value) is not None

    def test_fixture_rules_have_witnesses(self, z3_solver, sub_rules):
        checker = WitnessChecker(z3_solver)
        results = checker.find_witnesses(sub_rules)
        sat = [r for r in results if r.has_witness]
        assert len(sat) >= 4

    def test_witness_model_keys_match_variables(self, z3_solver):
        r = make_rule(rule_id="5", var_name="REQUEST_URI", pattern="select")
        checker = WitnessChecker(z3_solver)
        res = checker.check_rule(r)
        assert res.has_witness
        assert "REQUEST_URI" in res.model


# ---------------------------------------------------------------------------
# Chained rule semantics
# ---------------------------------------------------------------------------

def make_chain(specs: list[dict]) -> list[SecRule]:
    """Build a chain of SecRules; all but the last get chained=True."""
    rules = []
    for i, spec in enumerate(specs):
        rule = make_rule(**spec)
        rule.chained = i < len(specs) - 1
        rules.append(rule)
    return rules


class TestGroupChains:
    def test_single_unchained_rule_is_its_own_chain(self):
        rules = [make_rule(rule_id="1")]
        assert group_chains(rules) == [[rules[0]]]

    def test_chained_rules_grouped_together(self):
        chain = make_chain([
            dict(rule_id="1", var_name="REQUEST_HEADERS", pattern="foo"),
            dict(rule_id="", var_name="ARGS", pattern="bar"),
        ])
        groups = group_chains(chain)
        assert groups == [chain]

    def test_independent_chains_kept_separate(self):
        chain1 = make_chain([
            dict(rule_id="1", pattern="foo"),
            dict(rule_id="", pattern="bar"),
        ])
        chain2 = [make_rule(rule_id="2", pattern="baz")]
        groups = group_chains(chain1 + chain2)
        assert groups == [chain1, chain2]

    def test_trailing_chained_rule_without_terminator(self):
        rules = make_chain([dict(rule_id="1"), dict(rule_id="")])
        # both links are chained=True; the helper still groups them together
        rules[-1].chained = True
        assert group_chains(rules) == [rules]


class TestChainToSmt:
    def test_single_link_matches_rx_rule_to_smt(self):
        rule = make_rule(rule_id="1", pattern="foo")
        formula = chain_to_smt([rule])
        assert formula.rule_id == "1"
        assert "foo" in formula.assertion

    def test_multi_link_assertion_is_conjunction(self):
        chain = make_chain([
            dict(rule_id="1", var_name="REQUEST_HEADERS", pattern="foo"),
            dict(rule_id="", var_name="ARGS", pattern="bar"),
        ])
        formula = chain_to_smt(chain)
        assert formula.rule_id == "1"
        assert formula.assertion.startswith("(and ")
        assert "foo" in formula.assertion
        assert "bar" in formula.assertion
        assert "REQUEST_HEADERS" in formula.assertion
        assert "ARGS" in formula.assertion

    def test_declarations_deduplicated_for_shared_variable(self):
        chain = make_chain([
            dict(rule_id="1", var_name="ARGS", pattern="foo"),
            dict(rule_id="", var_name="ARGS", pattern="bar"),
        ])
        formula = chain_to_smt(chain)
        assert formula.declarations == ["(declare-const ARGS String)"]

    def test_non_rx_link_raises(self):
        chain = make_chain([
            dict(rule_id="1", pattern="foo"),
            dict(rule_id="", pattern="bar"),
        ])
        chain[1].operator = "@geoLookup"
        with pytest.raises(UnsupportedOperatorError):
            chain_to_smt(chain)

    def test_unsupported_transform_raises(self):
        chain = make_chain([
            dict(rule_id="1", pattern="foo", transforms=["__unknown__"]),
            dict(rule_id="", pattern="bar"),
        ])
        with pytest.raises(UnsupportedTransformError):
            chain_to_smt(chain)


class TestChainsShareVariable:
    def test_shares_variable_via_any_link(self):
        chain1 = make_chain([
            dict(rule_id="1", var_name="REQUEST_HEADERS", pattern="foo"),
            dict(rule_id="", var_name="ARGS", pattern="bar"),
        ])
        chain2 = [make_rule(rule_id="2", var_name="ARGS", pattern="baz")]
        assert chains_share_variable(chain1, chain2)

    def test_disjoint_variables(self):
        chain1 = [make_rule(rule_id="1", var_name="ARGS", pattern="foo")]
        chain2 = [make_rule(rule_id="2", var_name="RESPONSE_BODY", pattern="bar")]
        assert not chains_share_variable(chain1, chain2)


class TestChainSubsumptionAndIntersectionSmt2:
    def test_subsumption_query_structure(self):
        chain1 = [make_rule(rule_id="1", pattern="foo")]
        chain2 = [make_rule(rule_id="2", pattern="foo|bar")]
        smt2 = chain_subsumption_smt2(chain1, chain2)
        assert "(declare-const ARGS String)" in smt2
        assert smt2.count("(declare-const ARGS String)") == 1
        assert "(assert (not " in smt2

    def test_intersection_query_shares_declarations(self):
        chain1 = make_chain([
            dict(rule_id="1", var_name="ARGS", pattern="foo"),
            dict(rule_id="", var_name="REQUEST_HEADERS", pattern="bar"),
        ])
        chain2 = [make_rule(rule_id="2", var_name="ARGS", pattern="baz")]
        smt2 = chain_intersection_smt2(chain1, chain2)
        assert smt2.count("(declare-const ARGS String)") == 1
        assert "(declare-const REQUEST_HEADERS String)" in smt2

    def test_intersection_shared_transform_gets_single_declaration(self):
        # chain1 and chain2 each independently restrict "urlDecode" to their
        # own @rx pattern's codepoints; merged, the query must declare
        # "t_urlDecode" exactly once, sized to the union of both patterns —
        # not two differently-restricted declarations of the same symbol.
        chain1 = [make_rule(rule_id="1", pattern="A", transforms=["urlDecode"])]
        chain2 = [make_rule(rule_id="2", pattern="Z", transforms=["urlDecode"])]
        smt2 = chain_intersection_smt2(chain1, chain2)
        decls = _re.findall(r"\(define-fun t_urlDecode .*", smt2)
        assert len(decls) == 1
        assert '"\\u{41}"' in decls[0]
        assert '"\\u{5a}"' in decls[0]

    def test_subsumption_shared_transform_gets_single_declaration(self):
        chain1 = [make_rule(rule_id="1", pattern="A", transforms=["urlDecode"])]
        chain2 = [make_rule(rule_id="2", pattern="Z", transforms=["urlDecode"])]
        smt2 = chain_subsumption_smt2(chain1, chain2)
        decls = _re.findall(r"\(define-fun t_urlDecode .*", smt2)
        assert len(decls) == 1
        assert '"\\u{41}"' in decls[0]
        assert '"\\u{5a}"' in decls[0]

    def test_precomputed_formulas_still_get_joint_restriction(self):
        # The f1/f2 precomputed-formula fast path (used when reusing
        # chain_to_smt results across many pairwise comparisons) must not
        # bypass the joint restriction: each chain's own chain_to_smt() call
        # restricts urlDecode to its own narrow pattern, but the pairwise
        # query must still recompute a single, union-sized declaration.
        chain1 = [make_rule(rule_id="1", pattern="A", transforms=["urlDecode"])]
        chain2 = [make_rule(rule_id="2", pattern="Z", transforms=["urlDecode"])]
        f1 = chain_to_smt(chain1)
        f2 = chain_to_smt(chain2)
        smt2 = chain_intersection_smt2(chain1, chain2, f1, f2)
        decls = _re.findall(r"\(define-fun t_urlDecode .*", smt2)
        assert len(decls) == 1
        assert '"\\u{41}"' in decls[0]
        assert '"\\u{5a}"' in decls[0]


class TestSubsumptionCheckerChainPair:
    def test_skips_when_chain_has_non_rx_link(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        chain1 = make_chain([dict(rule_id="1"), dict(rule_id="")])
        chain1[1].operator = "@geoLookup"
        chain2 = [make_rule(rule_id="2")]
        res = checker.check_chain_pair(chain1, chain2)
        assert res.result == SolverResult.UNKNOWN

    def test_skips_when_no_shared_variable(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        chain1 = [make_rule(rule_id="1", var_name="ARGS")]
        chain2 = [make_rule(rule_id="2", var_name="RESPONSE_BODY")]
        res = checker.check_chain_pair(chain1, chain2)
        assert res.result == SolverResult.UNKNOWN

    def test_unsat_means_subsumed(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        chain1 = [make_rule(rule_id="1")]
        chain2 = [make_rule(rule_id="2")]
        res = checker.check_chain_pair(chain1, chain2)
        assert isinstance(res, ChainSubsumptionResult)
        assert res.is_subsumed

    def test_find_subsumed_chains_groups_rules(self):
        checker = SubsumptionChecker(ConstantSolver(SolverResult.UNSAT))
        chain = make_chain([
            dict(rule_id="1", pattern="foo"),
            dict(rule_id="", pattern="bar"),
        ])
        other = [make_rule(rule_id="2", pattern="baz")]
        results = checker.find_subsumed_chains(chain + other)
        assert len(results) == 2  # (chain⊆other) and (other⊆chain)
        for res in results:
            assert isinstance(res, ChainSubsumptionResult)


class TestIntersectionCheckerChainPair:
    def test_sat_means_intersecting(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        chain1 = [make_rule(rule_id="1")]
        chain2 = [make_rule(rule_id="2")]
        res = checker.check_chain_pair(chain1, chain2)
        assert isinstance(res, ChainIntersectionResult)
        assert res.has_intersection

    def test_find_intersecting_chains_groups_rules(self):
        checker = IntersectionChecker(ConstantSolver(SolverResult.SAT))
        chain = make_chain([
            dict(rule_id="1", pattern="foo"),
            dict(rule_id="", pattern="bar"),
        ])
        other = [make_rule(rule_id="2", pattern="baz")]
        results = checker.find_intersecting_chains(chain + other)
        assert len(results) == 1
        assert isinstance(results[0], ChainIntersectionResult)


class TestContradictionCheckerChainPair:
    def test_sat_with_conflicting_actions_is_contradiction(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        chain1 = [make_rule(rule_id="1")]
        chain1[0].actions.append(make_action("deny"))
        chain2 = [make_rule(rule_id="2")]
        chain2[0].actions.append(make_action("allow"))
        res = checker.check_chain_pair(chain1, chain2)
        assert isinstance(res, ChainContradictionResult)
        assert res.has_intersection
        assert res.is_contradiction

    def test_sat_with_same_action_is_not_contradiction(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        chain1 = [make_rule(rule_id="1")]
        chain1[0].actions.append(make_action("deny"))
        chain2 = [make_rule(rule_id="2")]
        chain2[0].actions.append(make_action("deny"))
        res = checker.check_chain_pair(chain1, chain2)
        assert res.has_intersection
        assert not res.is_contradiction

    def test_find_contradicting_chains_groups_rules(self):
        checker = ContradictionChecker(ConstantSolver(SolverResult.SAT))
        chain = make_chain([
            dict(rule_id="1", pattern="foo"),
            dict(rule_id="", pattern="bar"),
        ])
        chain[0].actions.append(make_action("deny"))
        other = [make_rule(rule_id="2", pattern="baz")]
        other[0].actions.append(make_action("allow"))
        results = checker.find_contradicting_chains(chain + other)
        assert len(results) == 1
        assert isinstance(results[0], ChainContradictionResult)
        assert results[0].is_contradiction


class TestWitnessCheckerChain:
    def test_chain_witness_sat(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "foo", "REQUEST_HEADERS": "bar"})
        checker = WitnessChecker(solver)
        chain = make_chain([
            dict(rule_id="1", var_name="ARGS", pattern="foo"),
            dict(rule_id="", var_name="REQUEST_HEADERS", pattern="bar"),
        ])
        res = checker.check_chain(chain)
        assert isinstance(res, ChainWitnessResult)
        assert res.has_witness
        assert res.model == {"ARGS": "foo", "REQUEST_HEADERS": "bar"}

    def test_chain_with_non_rx_link_returns_unknown(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "foo"})
        checker = WitnessChecker(solver)
        chain = make_chain([dict(rule_id="1"), dict(rule_id="")])
        chain[1].operator = "@geoLookup"
        res = checker.check_chain(chain)
        assert res.result == SolverResult.UNKNOWN

    def test_find_chain_witnesses_groups_rules(self):
        solver = ModelSolver(SolverResult.SAT, {"ARGS": "foo"})
        checker = WitnessChecker(solver)
        chain = make_chain([
            dict(rule_id="1", pattern="foo"),
            dict(rule_id="", pattern="bar"),
        ])
        other = [make_rule(rule_id="2", pattern="baz")]
        results = checker.find_chain_witnesses(chain + other)
        assert len(results) == 2


# ---------------------------------------------------------------------------
# Common and escaping witnesses: what makes a pairwise verdict about the pair
# ---------------------------------------------------------------------------

def target_rule(*variables: SecRuleVariable, pattern="a", rule_id="1", operator="@rx") -> SecRule:
    return SecRule(
        rule_id=rule_id,
        variables=list(variables),
        operator=operator,
        operator_argument=pattern,
        negated=False,
        actions=[],
        chained=False,
        lineno=1,
    )


class TestChainsShareTarget:
    def test_selector_shares_with_the_bare_collection(self):
        # ARGS:id reads members of ARGS, so the two can match one member --
        # a relation `chains_share_variable` sees only by accident of both
        # specs being spelled "ARGS".
        c1 = [target_rule(SecRuleVariable("ARGS", "id"))]
        c2 = [target_rule(SecRuleVariable("ARGS"))]
        assert chains_share_target(c1, c2)

    def test_names_view_shares_with_a_value_view(self):
        c1 = [target_rule(SecRuleVariable("ARGS_NAMES"))]
        c2 = [target_rule(SecRuleVariable("ARGS"))]
        assert chains_share_target(c1, c2)
        # ... which the name-based test misses, ARGS_NAMES being a different
        # variable name.
        assert not chains_share_variable(c1, c2)

    def test_counter_shares_no_address(self):
        # `&ARGS` reads how many members there are, not what one of them
        # says, so it can never supply a common witness.
        c1 = [target_rule(SecRuleVariable("ARGS", counter=True), operator="@eq", pattern="3")]
        c2 = [target_rule(SecRuleVariable("ARGS"))]
        assert not chains_share_target(c1, c2)
        assert chains_share_variable(c1, c2)

    def test_disjoint_collections_share_nothing(self):
        c1 = [target_rule(SecRuleVariable("ARGS"))]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"))]
        assert not chains_share_target(c1, c2)

    def test_exclusions_do_not_count_as_reads(self):
        c1 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI", negated=True))]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"))]
        assert not chains_share_target(c1, c2)


class TestCommonWitness:
    def test_disjoint_targets_leave_no_common_witness(self):
        c1 = [target_rule(SecRuleVariable("ARGS"))]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"))]
        assert chain_common_witness(c1, c2) == []
        # The query then carries its own answer.
        assert "(assert false)" in chain_intersection_smt2(c1, c2)

    def test_single_shared_address_needs_no_extra_assertion(self):
        # Two single-target rules on one collection have only one address to
        # witness at, so their own conditions already say it.
        c1 = [target_rule(SecRuleVariable("ARGS"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("ARGS"), pattern="b")]
        asserts = [l for l in chain_intersection_smt2(c1, c2).splitlines() if l.startswith("(assert")]
        assert len(asserts) == 2

    def test_overlapping_target_lists_require_the_shared_one(self):
        # Each rule can fire on a collection the other ignores, so co-firing
        # is easy; overlapping means agreeing on REQUEST_URI.
        c1 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"), SecRuleVariable("REQUEST_HEADERS"), pattern="b")]
        assert chain_common_witness(c1, c2) == [
            '(and (str.in_re REQUEST_URI (re.from_ecma2020 "a")) '
            '(str.in_re REQUEST_URI (re.from_ecma2020 "b")))'
        ]
        asserts = [l for l in chain_intersection_smt2(c1, c2).splitlines() if l.startswith("(assert")]
        assert len(asserts) == 3

    def test_selector_pair_shares_the_name_symbol(self):
        c1 = [target_rule(SecRuleVariable("ARGS", "id"))]
        c2 = [target_rule(SecRuleVariable("ARGS", "user"))]
        # One address, so no extra assertion -- but the two conditions now
        # constrain one name symbol, which is what makes the pair unsat.
        smt2 = chain_intersection_smt2(c1, c2)
        assert len([l for l in smt2.splitlines() if l.startswith("(assert")]) == 2
        assert '(= ARGS_name "id")' in smt2 and '(= ARGS_name "user")' in smt2

    def test_one_alternative_per_shared_target(self):
        # Asked one at a time when the solver cannot take the disjunction.
        c1 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="b")]
        terms = chain_common_witness(c1, c2)
        assert len(terms) == 2
        single = chain_intersection_smt2(c1, c2, alternatives=[terms[0]])
        assert terms[0] in single and terms[1] not in single


class TestEscapingWitness:
    def test_selector_is_subsumed_by_the_bare_collection(self):
        # `ARGS:id "@rx a"` matches only members `ARGS "@rx a"` also matches,
        # so the refutation must come out unsatisfiable.
        c1 = [target_rule(SecRuleVariable("ARGS", "id"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("ARGS"), pattern="a")]
        f1, f2 = chain_to_smt(c1), chain_to_smt(c2)
        # The one escaping term is `chain1 and not chain2`, which the first
        # disjunct already says, so the refutation stays the plain one.
        assert subsumption_alternatives(c1, c2, f1, f2) == [f"(not {f2.assertion})"]
        smt2 = chain_subsumption_smt2(c1, c2, f1, f2)
        assert f"(assert {f1.assertion})" in smt2
        assert f"(assert (not {f2.assertion}))" in smt2

    def test_unshared_target_contributes_no_escape(self):
        # A collection chain2 never reads is no evidence that it misses
        # anything: its coverage is judged where it looks. Whether the pair
        # shares a target at all is settled before the query is built.
        c1 = [target_rule(SecRuleVariable("ARGS"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"), pattern="a")]
        assert chain_escaping_witness(c1, c2) == []

    def test_partial_overlap_escapes_only_on_the_shared_target(self):
        c1 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"), pattern="b")]
        assert chain_escaping_witness(c1, c2) == [
            '(and (str.in_re REQUEST_URI (re.from_ecma2020 "a")) '
            '(not (str.in_re REQUEST_URI (re.from_ecma2020 "b"))))'
        ]

    def test_guarded_chain_is_still_subsumed_by_the_rule_it_repeats(self):
        # A chain whose extra link reads TX matches no ARGS member the plain
        # rule misses, so deleting it changes nothing -- an escape on TX would
        # make every guarded chain un-subsumable.
        link = target_rule(SecRuleVariable("ARGS"), pattern="a", rule_id="1")
        link.chained = True
        guard = target_rule(SecRuleVariable("TX", "flag"), pattern="1", operator="@streq", rule_id="")
        c1 = [link, guard]
        c2 = [target_rule(SecRuleVariable("ARGS"), pattern="a", rule_id="2")]
        f1, f2 = chain_to_smt(c1), chain_to_smt(c2)
        escaping = chain_escaping_witness(c1, c2)
        assert all("TX__flag" not in term for term in escaping)
        smt2 = chain_subsumption_smt2(c1, c2, f1, f2)
        assert '(= TX__flag "1")' in smt2.split("(assert")[1]   # f1 keeps the guard
        assert '(= TX__flag "1")' not in smt2.split("(assert")[2]  # the refutation drops it

    def test_counter_only_condition_has_no_witness_to_escape(self):
        c1 = [target_rule(SecRuleVariable("ARGS", counter=True), operator="@eq", pattern="3")]
        c2 = [target_rule(SecRuleVariable("ARGS"), pattern="a")]
        assert chain_escaping_witness(c1, c2) == []


class TestDerivedPairVerdicts:
    def test_unshared_targets_are_disjoint_without_the_solver(self):
        solver = ConstantSolver(SolverResult.SAT)
        c1 = [target_rule(SecRuleVariable("ARGS"), rule_id="1")]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"), rule_id="2")]
        res = IntersectionChecker(solver).check_chain_pair(c1, c2)
        # The verdict follows from the query's own shared-witness assertion,
        # so a solver that says SAT to everything cannot change it.
        assert res.result == SolverResult.UNSAT
        assert "no common target" in res.skip_reason

    def test_unshared_targets_leave_subsumption_degenerate(self):
        solver = ConstantSolver(SolverResult.UNSAT)
        c1 = [target_rule(SecRuleVariable("ARGS"), rule_id="1")]
        c2 = [target_rule(SecRuleVariable("REQUEST_URI"), rule_id="2")]
        res = SubsumptionChecker(solver).check_chain_pair(c1, c2)
        # Not reported as a subsumption: what is left is whether chain1 is
        # dead code, which is a question about one rule.
        assert res.skipped
        assert not res.is_subsumed
        assert "no common target" in res.skip_reason

    def test_names_view_pair_is_checked_rather_than_skipped(self):
        solver = ConstantSolver(SolverResult.SAT)
        c1 = [target_rule(SecRuleVariable("ARGS_NAMES"), rule_id="1")]
        c2 = [target_rule(SecRuleVariable("ARGS"), rule_id="2")]
        res = IntersectionChecker(solver).check_chain_pair(c1, c2)
        assert not res.skipped
        assert res.has_intersection


class TestModelParsingIntegers:
    def test_integer_binding_is_parsed(self):
        # A `&` spec's witness is a count, printed unquoted.
        from wafan.analyses.solver import _parse_get_value_output
        assert _parse_get_value_output('((ARGS "abc")\n (cnt_ARGS 3))') == {
            "ARGS": "abc", "cnt_ARGS": "3",
        }

    def test_quoted_digits_stay_strings(self):
        from wafan.analyses.solver import _parse_get_value_output
        assert _parse_get_value_output('((ARGS "3"))') == {"ARGS": "3"}


class TestSolveAny:
    def test_sat_when_any_branch_is(self):
        results = iter([SolverResult.UNSAT, SolverResult.SAT])
        solver = CallbackSolver(lambda _: next(results))
        assert solve_any(solver, ["a", "b"]) == SolverResult.SAT

    def test_unsat_only_when_every_branch_is(self):
        solver = ConstantSolver(SolverResult.UNSAT)
        assert solve_any(solver, ["a", "b", "c"]) == SolverResult.UNSAT

    def test_undecided_branch_leaves_the_whole_unknown(self):
        results = iter([SolverResult.UNSAT, SolverResult.UNKNOWN])
        solver = CallbackSolver(lambda _: next(results))
        assert solve_any(solver, ["a", "b"]) == SolverResult.UNKNOWN

    def test_stops_at_the_first_sat(self):
        calls = []
        solver = CallbackSolver(lambda s: calls.append(s) or SolverResult.SAT)
        solve_any(solver, ["a", "b", "c"])
        assert calls == ["a"]


class TestTimeoutIsNotIndecision:
    def test_split_is_skipped_after_a_timeout(self):
        # Every branch carries the same expensive constraints, so splitting a
        # query that ran out of time only multiplies the wait.
        class TimingOutSolver:
            def __init__(self):
                self.timeout_count = 0
                self.calls = 0

            def solve(self, _smt2):
                self.calls += 1
                self.timeout_count += 1
                return SolverResult.UNKNOWN

        c1 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="b")]
        solver = TimingOutSolver()
        res = IntersectionChecker(solver).check_chain_pair(c1, c2)
        assert res.result == SolverResult.UNKNOWN
        assert solver.calls == 1

    def test_split_runs_when_the_solver_merely_declined(self):
        class DecliningSolver:
            def __init__(self):
                self.timeout_count = 0
                self.calls = 0

            def solve(self, _smt2):
                self.calls += 1
                return SolverResult.UNKNOWN if self.calls == 1 else SolverResult.UNSAT

        c1 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="a")]
        c2 = [target_rule(SecRuleVariable("ARGS"), SecRuleVariable("REQUEST_URI"), pattern="b")]
        solver = DecliningSolver()
        res = IntersectionChecker(solver).check_chain_pair(c1, c2)
        assert res.result == SolverResult.UNSAT
        assert solver.calls == 3  # the disjunction, then one target at a time
