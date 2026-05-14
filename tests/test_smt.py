"""Tests for wafan.smt – SMT-LIB2 formula generation."""

import pytest
from pathlib import Path

from wafan.parser import parse_file, parse_rx_rules, SecRule, SecRuleVariable, SecRuleAction
from wafan.smt import (
    rx_rule_to_smt,
    rules_to_smt,
    extract_transforms,
    apply_transforms_smt,
    transform_preamble,
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
        with pytest.raises(UnsupportedTransformError):
            apply_transforms_smt("BODY", ["__unknown__"])

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

    def test_truly_unknown_transform_raises(self):
        with pytest.raises(UnsupportedTransformError):
            rx_rule_to_smt(make_rule(transforms=["__unknown_transform__"]))

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

# ---------------------------------------------------------------------------
# Uninterpreted transforms – apply_transforms_smt
# ---------------------------------------------------------------------------

UNINTERPRETED = [
    "urlDecode", "urlDecodeUni", "htmlEntityDecode",
    "removeWhitespace", "compressWhitespace", "removeNulls",
    "trim", "trimLeft", "trimRight",
    "normalizePath", "normalizePathWin",
]

SMT_NAMES = {
    "urlDecode": "t_urlDecode",
    "urlDecodeUni": "t_urlDecodeUni",
    "htmlEntityDecode": "t_htmlEntityDecode",
    "removeWhitespace": "t_removeWhitespace",
    "compressWhitespace": "t_compressWhitespace",
    "removeNulls": "t_removeNulls",
    "trim": "t_trim",
    "trimLeft": "t_trimLeft",
    "trimRight": "t_trimRight",
    "normalizePath": "t_normalizePath",
    "normalizePathWin": "t_normalizePathWin",
}


class TestUninterpretedTransformExpression:
    @pytest.mark.parametrize("t", UNINTERPRETED)
    def test_wraps_with_smt_function(self, t):
        result = apply_transforms_smt("VAR", [t])
        assert f"({SMT_NAMES[t]} VAR)" == result

    @pytest.mark.parametrize("t", UNINTERPRETED)
    def test_case_insensitive_lookup(self, t):
        result = apply_transforms_smt("VAR", [t.lower()])
        assert SMT_NAMES[t] in result

    def test_stacked_with_direct(self):
        result = apply_transforms_smt("VAR", ["urlDecode", "lowercase"])
        assert result == "(str.lower (t_urlDecode VAR))"

    def test_unknown_still_raises(self):
        with pytest.raises(UnsupportedTransformError):
            apply_transforms_smt("VAR", ["__no_such_transform__"])


class TestTransformPreamble:
    @pytest.mark.parametrize("t", UNINTERPRETED)
    def test_returns_fun_decl(self, t):
        fun_decls, _ = transform_preamble([t])
        assert len(fun_decls) == 1
        assert f"(declare-fun {SMT_NAMES[t]}" in fun_decls[0]

    @pytest.mark.parametrize("t", UNINTERPRETED)
    def test_returns_axioms(self, t):
        _, axioms = transform_preamble([t])
        assert len(axioms) > 0

    @pytest.mark.parametrize("t", UNINTERPRETED)
    def test_axioms_are_assertions(self, t):
        _, axioms = transform_preamble([t])
        assert all(a.startswith("(assert ") for a in axioms)

    def test_direct_transform_no_decl(self):
        fun_decls, axioms = transform_preamble(["lowercase"])
        assert fun_decls == []
        assert axioms == []

    def test_empty_transforms_empty_preamble(self):
        assert transform_preamble([]) == ([], [])

    def test_duplicate_transform_deduped(self):
        fd1, ax1 = transform_preamble(["urlDecode"])
        fd2, ax2 = transform_preamble(["urlDecode", "urlDecode"])
        assert fd1 == fd2
        assert ax1 == ax2

    def test_two_different_transforms_two_decls(self):
        fun_decls, _ = transform_preamble(["urlDecode", "htmlEntityDecode"])
        assert len(fun_decls) == 2

    def test_unknown_raises(self):
        with pytest.raises(UnsupportedTransformError):
            transform_preamble(["__unknown__"])

    # Specific axiom content checks
    def test_urldecode_idempotent_axiom(self):
        _, axioms = transform_preamble(["urlDecode"])
        assert any("t_urlDecode (t_urlDecode" in a for a in axioms)

    def test_urldecode_length_axiom(self):
        _, axioms = transform_preamble(["urlDecode"])
        assert any("str.len" in a for a in axioms)

    def test_urldecode_empty_axiom(self):
        _, axioms = transform_preamble(["urlDecode"])
        assert any('""' in a for a in axioms)

    def test_removewhitespace_no_space_axiom(self):
        _, axioms = transform_preamble(["removeWhitespace"])
        combined = " ".join(axioms)
        assert "str.contains" in combined
        assert "not" in combined

    def test_compresswhitespace_no_double_space_axiom(self):
        _, axioms = transform_preamble(["compressWhitespace"])
        assert any("  " in a for a in axioms)

    def test_normalizepath_no_dotdot_axiom(self):
        _, axioms = transform_preamble(["normalizePath"])
        assert any("/../" in a for a in axioms)

    def test_normalizepathwin_no_dotdot_axiom(self):
        _, axioms = transform_preamble(["normalizePathWin"])
        assert any("\\\\..\\\\" in a or "\\..\\".encode() in a.encode() for a in axioms)


class TestSmtFormulaWithPreamble:
    def test_fun_declarations_in_to_smt2(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["urlDecode"])
        f = rx_rule_to_smt(rule)
        smt2 = f.to_smt2()
        assert "(declare-fun t_urlDecode" in smt2

    def test_axioms_in_to_smt2(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["urlDecode"])
        f = rx_rule_to_smt(rule)
        smt2 = f.to_smt2()
        assert "(assert (forall" in smt2

    def test_fun_decl_before_declare_const(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["urlDecode"])
        smt2 = rx_rule_to_smt(rule).to_smt2()
        assert smt2.index("declare-fun") < smt2.index("declare-const")

    def test_axioms_before_assert(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["urlDecode"])
        smt2 = rx_rule_to_smt(rule).to_smt2()
        # All forall axioms must appear before the final (assert (str.in_re
        forall_pos = smt2.rfind("(assert (forall")
        main_pos   = smt2.index("(assert (str.in_re")
        assert forall_pos < main_pos

    def test_uninterpreted_fn_in_assertion(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["urlDecode"])
        f = rx_rule_to_smt(rule)
        assert "t_urlDecode BODY" in f.assertion

    def test_no_preamble_for_direct_transforms(self):
        rule = make_rule(transforms=["lowercase"])
        f = rx_rule_to_smt(rule)
        assert f.fun_declarations == []
        assert f.axioms == []

    def test_stacked_uninterpreted_and_direct(self):
        rule = make_rule(var_name="V", pattern="p", transforms=["urlDecode", "lowercase"])
        f = rx_rule_to_smt(rule)
        assert "str.lower (t_urlDecode V)" in f.assertion
        assert len(f.fun_declarations) == 1

    def test_htmlentitydecode_produces_preamble(self):
        rule = make_rule(transforms=["htmlEntityDecode"])
        f = rx_rule_to_smt(rule)
        assert any("htmlEntityDecode" in d for d in f.fun_declarations)

    @pytest.mark.parametrize("t", UNINTERPRETED)
    def test_all_uninterpreted_produce_well_formed_smt2(self, t):
        rule = make_rule(var_name="BODY", pattern="test", transforms=[t])
        smt2 = rx_rule_to_smt(rule).to_smt2()
        assert "(set-logic" in smt2
        assert "(declare-fun" in smt2
        assert "(declare-const" in smt2
        assert "(assert (forall" in smt2
        assert "(check-sat)" in smt2


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
