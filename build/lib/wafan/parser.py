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


def _to_secrule(raw: dict[str, Any]) -> SecRule:
    return SecRule(
        rule_id=_extract_rule_id(raw.get("actions", [])),
        variables=[_parse_variable(v) for v in raw.get("variables", [])],
        operator=raw.get("operator", ""),
        operator_argument=raw.get("operator_argument", ""),
        negated=raw.get("operator_negated", False),
        actions=[_parse_action(a) for a in raw.get("actions", [])],
        chained=raw.get("chained", False),
        lineno=raw.get("lineno", 0),
    )


def parse_file(path: str | Path) -> list[SecRule]:
    """Parse a ModSecurity conf file and return all SecRule entries."""
    source = Path(path).read_text()
    parser = msc_pyparser.MSCParser()
    parser.parser.parse(source, lexer=msc_pyparser.MSCLexer().lexer)
    return [
        _to_secrule(entry)
        for entry in parser.configlines
        if entry.get("type") == "SecRule"
    ]


def parse_rx_rules(path: str | Path) -> list[SecRule]:
    """Return only @rx (regex-matching) rules from a conf file."""
    return [r for r in parse_file(path) if r.operator in ("@rx", "!@rx")]
