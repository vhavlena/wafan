"""Tests for SecDefaultAction / SecRuleUpdateTargetById handling."""

from pathlib import Path

from wafan.parser import parse_file
from wafan.smt import effective_transforms

CONF = Path(__file__).parent / "data" / "default_action.conf"


def _rule(rules, rule_id):
    return next(r for r in rules if r.rule_id == rule_id)


class TestSecDefaultActionInheritance:
    def test_rule_without_own_transforms_inherits_default(self):
        rules = parse_file(CONF)
        rule = _rule(rules, "100")
        assert effective_transforms(rule) == ["lowercase"]

    def test_rule_with_own_transforms_overrides_default(self):
        rules = parse_file(CONF)
        rule = _rule(rules, "101")
        assert effective_transforms(rule) == ["urlDecode"]

    def test_later_default_action_replaces_earlier_one(self):
        rules = parse_file(CONF)
        rule = _rule(rules, "102")
        assert effective_transforms(rule) == ["compressWhitespace"]

    def test_default_action_is_phase_scoped(self):
        rules = parse_file(CONF)
        rule = _rule(rules, "103")
        assert effective_transforms(rule) == []


class TestSecRuleUpdateTargetById:
    def test_target_added(self):
        rules = parse_file(CONF)
        rule = _rule(rules, "100")
        assert any(v.name == "REQUEST_HEADERS" and v.part == "X-Foo" for v in rule.variables)

    def test_target_removed(self):
        rules = parse_file(CONF)
        rule = _rule(rules, "100")
        assert not any(v.name == "ARGS" for v in rule.variables)
