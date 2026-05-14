"""Tests for wafan.parser – SecRule parsing."""

import pytest
from pathlib import Path

from wafan.parser import parse_file, parse_rx_rules, SecRule, SecRuleVariable

CONF = Path(__file__).parent.parent / "RESPONSE-954-DATA-LEAKAGES-IIS.conf"


@pytest.fixture(scope="module")
def all_rules():
    return parse_file(CONF)


@pytest.fixture(scope="module")
def rx_rules():
    return parse_rx_rules(CONF)


class TestParseFile:
    def test_returns_list_of_secrule(self, all_rules):
        assert all(isinstance(r, SecRule) for r in all_rules)

    def test_non_empty(self, all_rules):
        assert len(all_rules) > 0

    def test_rule_ids_are_strings(self, all_rules):
        for rule in all_rules:
            assert isinstance(rule.rule_id, str)

    def test_known_rule_id_present(self, all_rules):
        ids = {r.rule_id for r in all_rules}
        assert "954100" in ids

    def test_variables_are_secrule_variable(self, all_rules):
        for rule in all_rules:
            assert all(isinstance(v, SecRuleVariable) for v in rule.variables)

    def test_lineno_positive(self, all_rules):
        for rule in all_rules:
            assert rule.lineno > 0


class TestParseRxRules:
    def test_only_rx_operators(self, rx_rules):
        for rule in rx_rules:
            assert rule.operator in ("@rx", "!@rx")

    def test_rule_954100_parsed(self, rx_rules):
        rule = next((r for r in rx_rules if r.rule_id == "954100"), None)
        assert rule is not None

    def test_rule_954100_variable(self, rx_rules):
        rule = next(r for r in rx_rules if r.rule_id == "954100")
        assert any(v.name == "RESPONSE_BODY" for v in rule.variables)

    def test_rule_954100_pattern(self, rx_rules):
        rule = next(r for r in rx_rules if r.rule_id == "954100")
        assert "inetpub" in rule.operator_argument

    def test_negated_flag_false_for_rx(self, rx_rules):
        rule = next(r for r in rx_rules if r.rule_id == "954100")
        assert rule.negated is False

    def test_negated_rule_detected(self):
        # Rule 954130 uses !@rx
        rules = parse_file(CONF)
        neg = [r for r in rules if r.operator == "!@rx" or r.negated]
        # At least one negated rule exists in the file
        assert len(neg) >= 1
