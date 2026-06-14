"""Parse ModSecurity SecRule configuration files into structured Python objects."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

import msc_pyparser


@dataclass
class SecRuleVariable:
    name: str
    part: str = ""
    negated: bool = False
    counter: bool = False


@dataclass
class SecRuleAction:
    name: str
    arg: str = ""


@dataclass
class SecRule:
    rule_id: str
    variables: list[SecRuleVariable]
    operator: str           # e.g. "@rx", "@pm"
    operator_argument: str  # raw operator argument (regex pattern for @rx)
    negated: bool           # True when operator is prefixed with !
    actions: list[SecRuleAction]
    chained: bool
    lineno: int
    phase: str = "2"
    inherited_actions: list[SecRuleAction] = None  # type: ignore[assignment]

    def __post_init__(self) -> None:
        if self.inherited_actions is None:
            self.inherited_actions = []


DEFAULT_PHASE = "2"


def _parse_variable(raw: dict[str, Any]) -> SecRuleVariable:
    return SecRuleVariable(
        name=raw["variable"],
        part=raw.get("variable_part", ""),
        negated=raw.get("negated", False),
        counter=raw.get("counter", False),
    )


def _parse_action(raw: dict[str, Any]) -> SecRuleAction:
    return SecRuleAction(name=raw["act_name"], arg=raw.get("act_arg", ""))


def _extract_rule_id(actions: list[dict[str, Any]]) -> str:
    for a in actions:
        if a["act_name"] == "id":
            return a.get("act_arg", "")
    return ""


def _extract_phase(actions: list[SecRuleAction]) -> str:
    for a in actions:
        if a.name == "phase":
            return a.arg
    return DEFAULT_PHASE


def _parse_action_string(spec: str) -> list[SecRuleAction]:
    """Parse a comma-separated action list, e.g. "phase:2,deny,t:none"."""
    actions: list[SecRuleAction] = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        name, sep, arg = part.partition(":")
        actions.append(SecRuleAction(name=name.strip(), arg=arg.strip() if sep else ""))
    return actions


def _to_secrule(raw: dict[str, Any]) -> SecRule:
    actions = [_parse_action(a) for a in raw.get("actions", [])]
    return SecRule(
        rule_id=_extract_rule_id(raw.get("actions", [])),
        variables=[_parse_variable(v) for v in raw.get("variables", [])],
        operator=raw.get("operator", ""),
        operator_argument=raw.get("operator_argument", ""),
        negated=raw.get("operator_negated", False),
        actions=actions,
        chained=raw.get("chained", False),
        lineno=raw.get("lineno", 0),
        phase=_extract_phase(actions),
    )


def _parse_default_action(raw: dict[str, Any]) -> tuple[str, list[SecRuleAction]]:
    """Parse a SecDefaultAction directive into (phase, actions)."""
    args = raw.get("arguments", [])
    spec = args[0]["argument"] if args else ""
    actions = _parse_action_string(spec)
    phase = _extract_phase(actions)
    return phase, actions


def _parse_target_spec(spec: str) -> tuple[bool, SecRuleVariable]:
    """Parse a single SecRuleUpdateTargetById target, e.g. "!ARGS:foo".

    Returns (remove, variable) where ``remove`` is True if the target is
    prefixed with "!" (i.e. it should be removed from the rule's variables).
    """
    spec = spec.strip()
    remove = spec.startswith("!")
    if remove:
        spec = spec[1:]
    elif spec.startswith("+") or spec.startswith("-"):
        spec = spec[1:]
    name, sep, part = spec.partition(":")
    return remove, SecRuleVariable(name=name.strip(), part=part.strip() if sep else "")


def _parse_update_target(raw: dict[str, Any]) -> tuple[str, list[tuple[bool, SecRuleVariable]]]:
    """Parse a SecRuleUpdateTargetById directive into (rule_id, [(remove, variable), ...])."""
    args = [a["argument"] for a in raw.get("arguments", [])]
    if not args:
        return "", []
    rule_id = args[0]
    targets: list[tuple[bool, SecRuleVariable]] = []
    for arg in args[1:]:
        for spec in arg.split("|"):
            spec = spec.strip()
            if spec:
                targets.append(_parse_target_spec(spec))
    return rule_id, targets


def _apply_update_targets(
    rules: list[SecRule], updates: list[tuple[str, list[tuple[bool, SecRuleVariable]]]]
) -> None:
    """Apply SecRuleUpdateTargetById directives to the parsed rules in-place."""
    for rule_id, targets in updates:
        for rule in rules:
            if rule.rule_id != rule_id:
                continue
            for remove, variable in targets:
                if remove:
                    rule.variables = [
                        v
                        for v in rule.variables
                        if not (v.name == variable.name and v.part == variable.part)
                    ]
                else:
                    rule.variables.append(variable)


def parse_file(path: str | Path) -> list[SecRule]:
    """Parse a ModSecurity conf file and return all SecRule entries.

    ``SecDefaultAction`` directives set per-phase default actions (most
    notably default transformations) that are inherited by subsequent
    ``SecRule`` directives in the same phase, unless a rule defines its own
    ``t:`` actions. ``SecRuleUpdateTargetById`` directives are applied to the
    matching rules after parsing.
    """
    source = Path(path).read_text()
    parser = msc_pyparser.MSCParser()
    parser.parser.parse(source, lexer=msc_pyparser.MSCLexer().lexer)

    default_actions: dict[str, list[SecRuleAction]] = {}
    rules: list[SecRule] = []
    updates: list[tuple[str, list[tuple[bool, SecRuleVariable]]]] = []

    for entry in parser.configlines:
        entry_type = entry.get("type")
        if entry_type == "SecRule":
            rule = _to_secrule(entry)
            rule.inherited_actions = list(default_actions.get(rule.phase, []))
            rules.append(rule)
        elif entry_type == "SecDefaultAction":
            phase, actions = _parse_default_action(entry)
            default_actions[phase] = actions
        elif entry_type == "SecRuleUpdateTargetById":
            updates.append(_parse_update_target(entry))

    _apply_update_targets(rules, updates)
    return rules


def parse_rx_rules(path: str | Path) -> list[SecRule]:
    """Return only @rx (regex-matching) rules from a conf file."""
    return [r for r in parse_file(path) if r.operator in ("@rx", "!@rx")]


def group_chains(rules: list[SecRule]) -> list[list[SecRule]]:
    """Group consecutive rules into chains based on the ``chain`` action.

    A rule whose ``chained`` flag is set continues into the next rule, which
    becomes the next link of the same chain; the chain ends at (and includes)
    the first subsequent rule whose ``chained`` flag is not set. Rules
    without ``chain`` form a chain of length one.
    """
    chains: list[list[SecRule]] = []
    current: list[SecRule] = []
    for rule in rules:
        current.append(rule)
        if not rule.chained:
            chains.append(current)
            current = []
    if current:
        chains.append(current)
    return chains
