"""Tests for wafan.smt – SMT-LIB2 formula generation."""

import pytest
from pathlib import Path

from wafan.parser import parse_file, parse_rx_rules, SecRule, SecRuleVariable, SecRuleAction
from wafan.smt import (
    rule_to_smt,
    rules_to_smt,
    extract_transforms,
    apply_transforms_smt,
    transform_preamble,
    SmtFormula,
    SMT_LOGIC,
    UnsupportedOperatorError,
    UnsupportedTransformError,
)

CONF = Path(__file__).parent / "data" / "subsumption.conf"


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
        assert apply_transforms_smt("BODY", ["lowercase"]) == "(str.to_lower BODY)"

    def test_uppercase_wraps_with_str_upper(self):
        assert apply_transforms_smt("BODY", ["uppercase"]) == "(str.to_upper BODY)"

    def test_lowerCase_alias(self):
        assert apply_transforms_smt("BODY", ["lowerCase"]) == "(str.to_lower BODY)"

    def test_upperCase_alias(self):
        assert apply_transforms_smt("BODY", ["upperCase"]) == "(str.to_upper BODY)"

    def test_stacking_order_innermost_first(self):
        # lowercase applied first (innermost), then uppercase wraps it
        result = apply_transforms_smt("BODY", ["lowercase", "uppercase"])
        assert result == "(str.to_upper (str.to_lower BODY))"

    def test_unsupported_transform_raises(self):
        with pytest.raises(UnsupportedTransformError):
            apply_transforms_smt("BODY", ["__unknown__"])

    def test_unsupported_transform_message_contains_name(self):
        with pytest.raises(UnsupportedTransformError) as exc_info:
            apply_transforms_smt("BODY", ["base64Decode"])
        assert "base64Decode" in str(exc_info.value)


# ---------------------------------------------------------------------------
# rule_to_smt (transform integration)
# ---------------------------------------------------------------------------

class TestRxRuleToSmt:
    def test_returns_smt_formula(self):
        assert isinstance(rule_to_smt(make_rule()), SmtFormula)

    def test_declares_variable(self):
        f = rule_to_smt(make_rule(var_name="RESPONSE_BODY"))
        assert any("RESPONSE_BODY" in d for d in f.declarations)

    def test_declaration_is_string_sort(self):
        f = rule_to_smt(make_rule(var_name="REQUEST_URI"))
        assert any("String" in d for d in f.declarations)

    def test_assertion_uses_str_in_re(self):
        f = rule_to_smt(make_rule(pattern="foo.*bar"))
        assert "str.in_re" in f.assertion

    def test_assertion_uses_from_ecma2020(self):
        f = rule_to_smt(make_rule(pattern="foo.*bar"))
        assert "re.from_ecma2020" in f.assertion

    def test_pattern_embedded_in_assertion(self):
        # (?i) is expanded in-place: letters become [xX] classes
        f = rule_to_smt(make_rule(pattern="(?i)[a-z]+inetpub"))
        assert "re.from_ecma2020" in f.assertion
        assert "re.from_ecma2020_flags" not in f.assertion
        # [a-z] expanded to [a-zA-Z], literal letters wrapped
        assert "[a-zA-Z]" in f.assertion
        assert "[iI]" in f.assertion

    def test_positive_assertion_no_not(self):
        f = rule_to_smt(make_rule(negated=False))
        assert not f.assertion.startswith("(not ")

    def test_negated_rule_wraps_with_not(self):
        f = rule_to_smt(make_rule(negated=True))
        assert f.assertion.startswith("(not ")

    def test_operator_bang_rx_treated_as_negated(self):
        f = rule_to_smt(make_rule(operator="!@rx", negated=False))
        assert f.assertion.startswith("(not ")

    def test_non_rx_operator_raises(self):
        rule = make_rule()
        rule.operator = "@geoLookup"
        with pytest.raises(UnsupportedOperatorError, match="not supported"):
            rule_to_smt(rule)

    def test_backslash_in_pattern_escaped(self):
        f = rule_to_smt(make_rule(pattern=r"[a-z]:\inetpub"))
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
        f = rule_to_smt(rule)
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
        assert len(rule_to_smt(rule).declarations) == 1

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
        assert "REQUEST_HEADERS__User_Agent" in rule_to_smt(rule).declarations[0]

    def test_rule_id_preserved(self):
        assert rule_to_smt(make_rule(rule_id="954100")).rule_id == "954100"

    # --- transform integration ---

    def test_no_transform_var_used_directly(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="x"))
        assert "str.in_re BODY" in f.assertion

    def test_t_none_only_no_wrapping(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["none"]))
        assert "str.in_re BODY" in f.assertion

    def test_lowercase_transform_applied(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["lowercase"]))
        assert "(str.to_lower BODY)" in f.assertion

    def test_uppercase_transform_applied(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["uppercase"]))
        assert "(str.to_upper BODY)" in f.assertion

    def test_none_then_lowercase(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["none", "lowercase"]))
        assert "(str.to_lower BODY)" in f.assertion

    def test_lowercase_then_none_resets(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["lowercase", "none"]))
        assert "str.in_re BODY" in f.assertion
        assert "str.to_lower" not in f.assertion

    def test_stacked_transforms_nested(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="x", transforms=["lowercase", "uppercase"]))
        assert "(str.to_upper (str.to_lower BODY))" in f.assertion

    def test_truly_unknown_transform_raises(self):
        with pytest.raises(UnsupportedTransformError):
            rule_to_smt(make_rule(transforms=["__unknown_transform__"]))

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
        f = rule_to_smt(rule)
        assert "(str.to_lower A)" in f.assertion
        assert "(str.to_lower B)" in f.assertion

    def test_conf_file_rules_translate_with_expected_transforms(self):
        rules = parse_rx_rules(CONF)
        for rule in rules:
            f = rule_to_smt(rule)
            if rule.rule_id == "500":
                assert "str.to_lower" in f.assertion
            else:
                assert "str.to_lower" not in f.assertion
            assert "str.to_upper" not in f.assertion


# ---------------------------------------------------------------------------
# Additional operators (@streq, @contains, @beginsWith, @endsWith, @within,
# @pm, @eq/@ge/@gt/@le/@lt)
# ---------------------------------------------------------------------------

class TestStreqOperator:
    def test_assertion_uses_equality(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="foo", operator="@streq"))
        assert f.assertion == '(= BODY "foo")'

    def test_negated(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="foo", operator="@streq", negated=True))
        assert f.assertion == '(not (= BODY "foo"))'

    def test_bang_operator_negates(self):
        f = rule_to_smt(make_rule(var_name="BODY", pattern="foo", operator="!@streq"))
        assert f.assertion == '(not (= BODY "foo"))'


class TestContainsOperator:
    def test_assertion_uses_str_contains(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="evil", operator="@contains"))
        assert f.assertion == '(str.contains ARGS "evil")'

    def test_negated(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="evil", operator="!@contains"))
        assert f.assertion == '(not (str.contains ARGS "evil"))'


class TestBeginsWithOperator:
    def test_assertion_uses_str_prefixof(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="/admin", operator="@beginsWith"))
        assert f.assertion == '(str.prefixof "/admin" ARGS)'


class TestEndsWithOperator:
    def test_assertion_uses_str_suffixof(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern=".php", operator="@endsWith"))
        assert f.assertion == '(str.suffixof ".php" ARGS)'


class TestWithinOperator:
    def test_single_value(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="GET", operator="@within"))
        assert f.assertion == '(str.contains "GET" ARGS)'

    def test_multiple_values_uses_or(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="GET POST", operator="@within"))
        assert f.assertion == '(or (str.contains "GET" ARGS) (str.contains "POST" ARGS))'


class TestPmOperator:
    def test_single_value(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="evil", operator="@pm"))
        assert f.assertion == '(str.contains ARGS "evil")'

    def test_multiple_values_uses_or(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="foo bar", operator="@pm"))
        assert f.assertion == '(or (str.contains ARGS "foo") (str.contains ARGS "bar"))'


class TestNumericOperators:
    @pytest.mark.parametrize(
        "operator,smt_op",
        [("@eq", "="), ("@ge", ">="), ("@gt", ">"), ("@le", "<="), ("@lt", "<")],
    )
    def test_assertion_uses_str_to_int(self, operator, smt_op):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="5", operator=operator))
        digits = '(str.in_re ARGS (re.+ (re.range "0" "9")))'
        assert f.assertion == f"(and {digits} ({smt_op} (str.to_int ARGS) 5))"

    def test_negated(self):
        f = rule_to_smt(make_rule(var_name="ARGS", pattern="0", operator="@eq", negated=True))
        digits = '(str.in_re ARGS (re.+ (re.range "0" "9")))'
        assert f.assertion == f"(not (and {digits} (= (str.to_int ARGS) 0)))"

    def test_non_integer_argument_raises(self):
        with pytest.raises(UnsupportedOperatorError):
            rule_to_smt(make_rule(var_name="ARGS", pattern="not-a-number", operator="@eq"))


# ---------------------------------------------------------------------------
# rules_to_smt
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Uninterpreted transforms – apply_transforms_smt
# ---------------------------------------------------------------------------

UNINTERPRETED = [
    "urlDecodeUni",
    "removeWhitespace", "compressWhitespace", "removeNulls",
    "trim", "trimLeft", "trimRight",
    "normalizePath", "normalizePathWin",
]

# All transforms that use a named SMT function (both define-fun and declare-fun)
SMT_NAMES = {
    "urlDecode": "t_urlDecode",
    "urlDecodeUni": "t_urlDecodeUni",
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
        assert result == "(str.to_lower (t_urlDecode VAR))"

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
        fun_decls, _ = transform_preamble(["urlDecode", "removeWhitespace"])
        assert len(fun_decls) == 2

    def test_htmlentitydecode_define_fun_no_axioms(self):
        fun_decls, axioms = transform_preamble(["htmlEntityDecode"])
        assert len(fun_decls) == 1
        assert fun_decls[0].startswith("(define-fun t_htmlEntityDecode ((s String)) String")
        assert fun_decls[0].count("str.replace_all") > 100
        assert axioms == []

    def test_urldecode_define_fun_no_axioms(self):
        fun_decls, axioms = transform_preamble(["urlDecode"])
        assert len(fun_decls) == 1
        assert fun_decls[0].startswith("(define-fun t_urlDecode ((s String)) String")
        # 1 str.replace_all ('+') + 256 str.replace_re_all ('%XX')
        assert fun_decls[0].count("str.replace_re_all") == 256
        assert fun_decls[0].count("str.replace_all ") == 1
        assert axioms == []

    def test_urldecode_define_fun_contains_plus_to_space(self):
        fun_decls, _ = transform_preamble(["urlDecode"])
        decl = fun_decls[0]
        # '+' → space must appear as a literal str.replace_all (pass 1)
        assert '"+" "\\u{20}"' in decl

    def test_urldecode_define_fun_contains_percent_encoding(self):
        fun_decls, _ = transform_preamble(["urlDecode"])
        decl = fun_decls[0]
        # regex terms for representative byte values must be present
        assert '"\\u{41}"' in decl   # 0x41 = A
        assert '"\\u{61}"' in decl   # 0x61 = a
        assert '"\\u{00}"' in decl   # 0x00 = NUL
        # case-variant union terms appear for hex-letter nibbles
        assert 're.union' in decl

    def test_urldecode_define_fun_percent25_last(self):
        fun_decls, _ = transform_preamble(["urlDecode"])
        decl = fun_decls[0]
        # the regex for %25 must appear and must come after other %XX regexes
        pct25_re = '(str.to_re "2") (str.to_re "5")'
        assert pct25_re in decl
        pos_25 = decl.rfind(pct25_re)
        # 0x41 ('A') regex should appear before %25
        pct41_re = '(str.to_re "4") (str.to_re "1")'
        assert decl.index(pct41_re) < pos_25

    def test_unknown_raises(self):
        with pytest.raises(UnsupportedTransformError):
            transform_preamble(["__unknown__"])

    # Specific axiom content checks
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
        f = rule_to_smt(rule)
        smt2 = f.to_smt2()
        assert "(define-fun t_urlDecode" in smt2

    def test_axioms_in_to_smt2(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["removeWhitespace"])
        f = rule_to_smt(rule)
        smt2 = f.to_smt2()
        assert "(assert (forall" in smt2

    def test_fun_decl_before_declare_const(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["removeWhitespace"])
        smt2 = rule_to_smt(rule).to_smt2()
        assert smt2.index("declare-fun") < smt2.index("declare-const")

    def test_axioms_before_assert(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["removeWhitespace"])
        smt2 = rule_to_smt(rule).to_smt2()
        # All forall axioms must appear before the final (assert (str.in_re
        forall_pos = smt2.rfind("(assert (forall")
        main_pos   = smt2.index("(assert (str.in_re")
        assert forall_pos >= 0
        assert forall_pos < main_pos

    def test_uninterpreted_fn_in_assertion(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["urlDecode"])
        f = rule_to_smt(rule)
        assert "t_urlDecode BODY" in f.assertion

    def test_no_preamble_for_direct_transforms(self):
        rule = make_rule(transforms=["lowercase"])
        f = rule_to_smt(rule)
        assert f.fun_declarations == []
        assert f.axioms == []

    def test_stacked_uninterpreted_and_direct(self):
        rule = make_rule(var_name="V", pattern="p", transforms=["urlDecode", "lowercase"])
        f = rule_to_smt(rule)
        assert "str.to_lower (t_urlDecode V)" in f.assertion
        assert len(f.fun_declarations) == 1

    def test_htmlentitydecode_define_fun_call_in_assertion(self):
        rule = make_rule(var_name="BODY", pattern="x", transforms=["htmlEntityDecode"])
        f = rule_to_smt(rule)
        assert len(f.fun_declarations) == 1
        assert f.fun_declarations[0].startswith("(define-fun t_htmlEntityDecode")
        assert f.axioms == []
        assert "(t_htmlEntityDecode BODY)" in f.assertion

    @pytest.mark.parametrize("t", UNINTERPRETED)
    def test_all_uninterpreted_produce_well_formed_smt2(self, t):
        rule = make_rule(var_name="BODY", pattern="test", transforms=[t])
        smt2 = rule_to_smt(rule).to_smt2()
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
