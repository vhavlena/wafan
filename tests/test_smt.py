"""Tests for wafan.smt – SMT-LIB2 formula generation."""

import pytest
from pathlib import Path

from wafan.parser import parse_file, parse_rx_rules, SecRule, SecRuleVariable, SecRuleAction
from wafan.smt import (
    rx_rule_to_smt,
    rules_to_smt,
    extract_transforms,
    apply_transforms_smt,
    SmtFormula,
    SMT_LOGIC,
    UnsupportedTransformError,
)

CONF = Path(__file__).parent.parent / "RESPONSE-954-DATA-LEAKAGES-IIS.conf"


def make_action(name: str, arg: str = "") -> SecRuleAction:
    return SecRuleAction(name=name, arg=arg)


def make_rule(
    rule_id="1",
    var_name="RESPONSE_BODY",
    pattern="test",
    negated=False,
    operator="@rx",
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


# ---------------------------------------------------------------------------
# SmtFormula
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# extract_transforms
# ---------------------------------------------------------------------------

class TestExtractTransforms:
    def test_empty_actions(self):
        assert extract_transforms([]) == []

    def test_single_lowercase(self):
        assert extract_transforms([make_action("t", "lowercase")]) == ["lowercase"]

    def test_single_uppercase(self):
        assert extract_transforms([make_action("t", "uppercase")]) == ["uppercase"]

    def test_none_resets_empty_list(self):
        assert extract_transforms([make_action("t", "none")]) == []

    def test_none_resets_prior_transforms(self):
        actions = [make_action("t", "lowercase"), make_action("t", "none")]
        assert extract_transforms(actions) == []

    def test_none_in_middle_resets(self):
        actions = [
            make_action("t", "lowercase"),
            make_action("t", "none"),
            make_action("t", "uppercase"),
        ]
        assert extract_transforms(actions) == ["uppercase"]

    def test_none_case_insensitive(self):
        assert extract_transforms([make_action("t", "None")]) == []

    def test_non_t_actions_ignored(self):
        actions = [make_action("id", "42"), make_action("t", "lowercase"), make_action("phase", "4")]
        assert extract_transforms(actions) == ["lowercase"]

    def test_multiple_transforms_order_preserved(self):
        actions = [make_action("t", "lowercase"), make_action("t", "uppercase")]
        assert extract_transforms(actions) == ["lowercase", "uppercase"]


# ---------------------------------------------------------------------------
# apply_transforms_smt
# ---------------------------------------------------------------------------

class TestApplyTransformsSmt:
    def test_no_transforms_returns_expr_unchanged(self):
        assert apply_transforms_smt("BODY", []) == "BODY"

    def test_lowercase_wraps_with_str_lower(self):
        assert apply_transforms_smt("BODY", ["lowercase"]) == "(str.lower BODY)"

    def test_uppercase_wraps_with_str_upper(self):
        assert apply_transforms_smt("BODY", ["uppercase"]) == "(str.upper BODY)"

    def test_lowerCase_alias(self):
        assert apply_transforms_smt("BODY", ["lowerCase"]) == "(str.lower BODY)"

    def test_upperCase_alias(self):
        assert apply_transforms_smt("BODY", ["upperCase"]) == "(str.upper BODY)"

    def test_stacking_order_innermost_first(self):
        # lowercase applied first (innermost), then uppercase wraps it
        result = apply_transforms_smt("BODY", ["lowercase", "uppercase"])
        assert result == "(str.upper (str.lower BODY))"

    def test_unsupported_transform_raises(self):
        with pytest.raises(UnsupportedTransformError, match="urlDecode"):
            apply_transforms_smt("BODY", ["urlDecode"])

    def test_unsupported_transform_message_contains_name(self):
        with pytest.raises(UnsupportedTransformError) as exc_info:
            apply_transforms_smt("BODY", ["base64Decode"])
        assert "base64Decode" in str(exc_info.value)


# ---------------------------------------------------------------------------
# rx_rule_to_smt (transform integration)
# ---------------------------------------------------------------------------

class TestRxRuleToSmt:
    def test_returns_smt_formula(self):
        assert isinstance(rx_rule_to_smt(make_rule()), SmtFormula)

    def test_declares_variable(self):
        f = rx_rule_to_smt(make_rule(var_name="RESPONSE_BODY"))
        assert any("RESPONSE_BODY" in d for d in f.declarations)

    def test_declaration_is_string_sort(self):
        f = rx_rule_to_smt(make_rule(var_name="REQUEST_URI"))
        assert any("String" in d for d in f.declarations)

    def test_assertion_uses_str_in_re(self):
        f = rx_rule_to_smt(make_rule(pattern="foo.*bar"))
        assert "str.in_re" in f.assertion

    def test_assertion_uses_from_ecma2020(self):
        f = rx_rule_to_smt(make_rule(pattern="foo.*bar"))
        assert "re.from_ecma2020" in f.assertion

    def test_pattern_embedded_in_assertion(self):
        f = rx_rule_to_smt(make_rule(pattern="(?i)[a-z]+inetpub"))
        assert "(?i)[a-z]+inetpub" in f.assertion

    def test_positive_assertion_no_not(self):
        f = rx_rule_to_smt(make_rule(negated=False))
        assert not f.assertion.startswith("(not ")

    def test_negated_rule_wraps_with_not(self):
        f = rx_rule_to_smt(make_rule(negated=True))
        assert f.assertion.startswith("(not ")

    def test_operator_bang_rx_treated_as_negated(self):
        f = rx_rule_to_smt(make_rule(operator="!@rx", negated=False))
        assert f.assertion.startswith("(not ")

    def test_non_rx_operator_raises(self):
        rule = make_rule()
        rule.operator = "@pm"
        with pytest.raises(ValueError, match="not @rx"):
            rx_rule_to_smt(rule)

    def test_backslash_in_pattern_escaped(self):
        f = rx_rule_to_smt(make_rule(pattern=r"[a-z]:\inetpub"))
        assert "\\\\" in f.assertion

    def test_multiple_variables_uses_or(self):
        rule = SecRule(
            rule_id="99",
            variables=[SecRuleVariable(name="REQUEST_BODY"), SecRuleVariable(name="RESPONSE_BODY")],
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
            variables=[SecRuleVariable(name="BODY"), SecRuleVariable(name="BODY")],
            operator="@rx",
            operator_argument="x",
            negated=False,
            actions=[],
            chained=False,
            lineno=1,
        )
        assert len(rx_rule_to_smt(rule).declarations) == 1

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
        assert "REQUEST_HEADERS__User_Agent" in rx_rule_to_smt(rule).declarations[0]

    def test_rule_id_preserved(self):
        assert rx_rule_to_smt(make_rule(rule_id="954100")).rule_id == "954100"

    # --- transform integration ---

    def test_no_transform_var_used_directly(self):
        f = rx_rule_to_smt(make_rule(var_name="BODY", pattern="x"))
        assert "str.in_re BODY" in f.assertion

    def test_t_none_only_no_wrapping(self):
        f = rx_rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["none"]))
        assert "str.in_re BODY" in f.assertion

    def test_lowercase_transform_applied(self):
        f = rx_rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["lowercase"]))
        assert "(str.lower BODY)" in f.assertion

    def test_uppercase_transform_applied(self):
        f = rx_rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["uppercase"]))
        assert "(str.upper BODY)" in f.assertion

    def test_none_then_lowercase(self):
        f = rx_rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["none", "lowercase"]))
        assert "(str.lower BODY)" in f.assertion

    def test_lowercase_then_none_resets(self):
        f = rx_rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["lowercase", "none"]))
        assert "str.in_re BODY" in f.assertion
        assert "str.lower" not in f.assertion

    def test_stacked_transforms_nested(self):
        f = rx_rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["lowercase", "uppercase"]))
        assert "(str.upper (str.lower BODY))" in f.assertion

    def test_unsupported_transform_raises(self):
        with pytest.raises(UnsupportedTransformError):
            rx_rule_to_smt(make_rule(transforms=["urlDecode"]))

    def test_transform_applied_to_all_variables(self):
        rule = SecRule(
            rule_id="5",
            variables=[SecRuleVariable(name="A"), SecRuleVariable(name="B")],
            operator="@rx",
            operator_argument="x",
            negated=False,
            actions=[make_action("t", "lowercase")],
            chained=False,
            lineno=1,
        )
        f = rx_rule_to_smt(rule)
        assert "(str.lower A)" in f.assertion
        assert "(str.lower B)" in f.assertion

    def test_conf_file_rules_with_t_none(self):
        # All rules in the test conf use t:none; they should produce no wrapping
        rules = parse_rx_rules(CONF)
        for rule in rules:
            f = rx_rule_to_smt(rule)
            assert "str.lower" not in f.assertion
            assert "str.upper" not in f.assertion


# ---------------------------------------------------------------------------
# rules_to_smt
# ---------------------------------------------------------------------------

class TestRulesToSmt:
    def test_skips_non_rx_rules(self):
        formulas = rules_to_smt(parse_file(CONF))
        assert all("str.in_re" in f.assertion for f in formulas)

    def test_count_matches_rx_only(self):
        assert len(rules_to_smt(parse_file(CONF))) == len(parse_rx_rules(CONF))

    def test_full_smt2_output_well_formed(self):
        for f in rules_to_smt(parse_rx_rules(CONF)):
            smt2 = f.to_smt2()
            assert "(set-logic" in smt2
            assert "(declare-const" in smt2
            assert "(assert" in smt2
            assert "(check-sat)" in smt2
