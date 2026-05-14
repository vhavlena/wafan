"""Tests for wafan.smt – SMT-LIB2 formula generation."""

import pytest
from pathlib import Path

from wafan.parser import parse_rx_rules, SecRule, SecRuleVariable, SecRuleAction
from wafan.smt import rx_rule_to_smt, rules_to_smt, SmtFormula, SMT_LOGIC

CONF = Path(__file__).parent.parent / "RESPONSE-954-DATA-LEAKAGES-IIS.conf"


def make_rule(
    rule_id="1",
    var_name="RESPONSE_BODY",
    pattern="test",
    negated=False,
    operator="@rx",
) -> SecRule:
    return SecRule(
        rule_id=rule_id,
        variables=[SecRuleVariable(name=var_name)],
        operator=operator,
        operator_argument=pattern,
        negated=negated,
        actions=[],
        chained=False,
        lineno=1,
    )


class TestSmtFormula:
    def test_to_smt2_contains_set_logic(self):
        f = SmtFormula(rule_id="1", declarations=["(declare-const x String)"], assertion="true")
        assert f"(set-logic {SMT_LOGIC})" in f.to_smt2()

    def test_to_smt2_contains_rule_id_comment(self):
        f = SmtFormula(rule_id="42", declarations=[], assertion="true")
        assert "rule id:42" in f.to_smt2()

    def test_to_smt2_contains_declarations(self):
        decl = "(declare-const RESPONSE_BODY String)"
        f = SmtFormula(rule_id="1", declarations=[decl], assertion="true")
        assert decl in f.to_smt2()

    def test_to_smt2_contains_assert(self):
        f = SmtFormula(rule_id="1", declarations=[], assertion="(= x x)")
        assert "(assert (= x x))" in f.to_smt2()

    def test_to_smt2_ends_with_check_sat(self):
        f = SmtFormula(rule_id="1", declarations=[], assertion="true")
        assert f.to_smt2().strip().endswith("(check-sat)")


class TestRxRuleToSmt:
    def test_returns_smt_formula(self):
        rule = make_rule()
        assert isinstance(rx_rule_to_smt(rule), SmtFormula)

    def test_declares_variable(self):
        rule = make_rule(var_name="RESPONSE_BODY")
        f = rx_rule_to_smt(rule)
        assert any("RESPONSE_BODY" in d for d in f.declarations)

    def test_declaration_is_string_sort(self):
        rule = make_rule(var_name="REQUEST_URI")
        f = rx_rule_to_smt(rule)
        assert any("String" in d for d in f.declarations)

    def test_assertion_uses_str_in_re(self):
        rule = make_rule(pattern="foo.*bar")
        f = rx_rule_to_smt(rule)
        assert "str.in_re" in f.assertion

    def test_assertion_uses_from_ecma2020(self):
        rule = make_rule(pattern="foo.*bar")
        f = rx_rule_to_smt(rule)
        assert "re.from_ecma2020" in f.assertion

    def test_pattern_embedded_in_assertion(self):
        rule = make_rule(pattern="(?i)[a-z]+inetpub")
        f = rx_rule_to_smt(rule)
        assert "(?i)[a-z]+inetpub" in f.assertion

    def test_positive_assertion_no_not(self):
        rule = make_rule(negated=False)
        f = rx_rule_to_smt(rule)
        assert not f.assertion.startswith("(not ")

    def test_negated_rule_wraps_with_not(self):
        rule = make_rule(negated=True)
        f = rx_rule_to_smt(rule)
        assert f.assertion.startswith("(not ")

    def test_operator_bang_rx_treated_as_negated(self):
        rule = make_rule(operator="!@rx", negated=False)
        f = rx_rule_to_smt(rule)
        assert f.assertion.startswith("(not ")

    def test_non_rx_operator_raises(self):
        rule = make_rule()
        rule.operator = "@pm"
        with pytest.raises(ValueError, match="not @rx"):
            rx_rule_to_smt(rule)

    def test_backslash_in_pattern_escaped(self):
        rule = make_rule(pattern=r"[a-z]:\inetpub")
        f = rx_rule_to_smt(rule)
        # The backslash must be escaped in the SMT string literal
        assert "\\\\" in f.assertion

    def test_multiple_variables_uses_or(self):
        rule = SecRule(
            rule_id="99",
            variables=[
                SecRuleVariable(name="REQUEST_BODY"),
                SecRuleVariable(name="RESPONSE_BODY"),
            ],
            operator="@rx",
            operator_argument="test",
            negated=False,
            actions=[],
            chained=False,
            lineno=1,
        )
        f = rx_rule_to_smt(rule)
        assert f.assertion.startswith("(or ")

    def test_multiple_variables_deduped_declarations(self):
        rule = SecRule(
            rule_id="99",
            variables=[
                SecRuleVariable(name="BODY"),
                SecRuleVariable(name="BODY"),
            ],
            operator="@rx",
            operator_argument="x",
            negated=False,
            actions=[],
            chained=False,
            lineno=1,
        )
        f = rx_rule_to_smt(rule)
        assert len(f.declarations) == 1

    def test_variable_part_included_in_name(self):
        rule = SecRule(
            rule_id="1",
            variables=[SecRuleVariable(name="REQUEST_HEADERS", part="User-Agent")],
            operator="@rx",
            operator_argument="curl",
            negated=False,
            actions=[],
            chained=False,
            lineno=1,
        )
        f = rx_rule_to_smt(rule)
        assert "REQUEST_HEADERS__User_Agent" in f.declarations[0]

    def test_rule_id_preserved(self):
        rule = make_rule(rule_id="954100")
        f = rx_rule_to_smt(rule)
        assert f.rule_id == "954100"


class TestRulesToSmt:
    def test_skips_non_rx_rules(self):
        from wafan.parser import parse_file
        rules = parse_file(CONF)
        formulas = rules_to_smt(rules)
        for formula in formulas:
            # Every formula came from an @rx rule
            assert "str.in_re" in formula.assertion

    def test_count_matches_rx_only(self):
        from wafan.parser import parse_file, parse_rx_rules
        all_rules = parse_file(CONF)
        rx_only = parse_rx_rules(CONF)
        formulas = rules_to_smt(all_rules)
        assert len(formulas) == len(rx_only)

    def test_full_smt2_output_parseable(self):
        rules = parse_rx_rules(CONF)
        formulas = rules_to_smt(rules)
        for f in formulas:
            smt2 = f.to_smt2()
            assert "(set-logic" in smt2
            assert "(declare-const" in smt2
            assert "(assert" in smt2
            assert "(check-sat)" in smt2
