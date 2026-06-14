"""Shared helpers used across the subsumption, intersection and witness analyses."""

from __future__ import annotations

from typing import Sequence

from ..parser import SecRule
from ..smt import _escape_smt_string

_SMT_SEP = "  " + "-" * 62


def _print_smt_block(smt2: str) -> None:
    print(f"  SMT-LIB2:\n{_SMT_SEP}\n{smt2}\n{_SMT_SEP}", flush=True)


def _rule_label(rule: SecRule, pat_width: int = 35) -> str:
    """Return a compact human-readable identifier for *rule*.

    Format: ``#ID [VAR1,VAR2 OP "PATTERN"]``

    Variable list is capped at three names; pattern is truncated to
    *pat_width* characters so the label fits on one terminal line.
    """
    var_names = [v.name for v in rule.variables]
    if len(var_names) > 3:
        vars_str = ",".join(var_names[:3]) + ",..."
    else:
        vars_str = ",".join(var_names)
    pat = rule.operator_argument
    if len(pat) > pat_width:
        pat = pat[:pat_width - 3] + "..."
    op = rule.operator
    return f"#{rule.rule_id} [{vars_str} {op} \"{pat}\"]"


def _chain_label(chain: Sequence[SecRule], pat_width: int = 35) -> str:
    """Return a compact human-readable identifier for a chained rule.

    Single-link chains are labelled like a plain rule; multi-link chains are
    labelled after their first link, annotated with the number of additional
    chained links.
    """
    label = _rule_label(chain[0], pat_width=pat_width)
    if len(chain) > 1:
        label += f" +{len(chain) - 1} chained"
    return label


def _all_rx(chain: Sequence[SecRule]) -> bool:
    """True if every link of *chain* uses the @rx / !@rx operator."""
    return all(r.operator in ("@rx", "!@rx") for r in chain)


def _match_assertion(var_expr: str, pattern: str, negated: bool) -> str:
    escaped = _escape_smt_string(pattern)
    atom = f'(str.in_re {var_expr} (re.from_ecma2020 "{escaped}"))'
    return f"(not {atom})" if negated else atom


def _variable_names(rule: SecRule) -> frozenset[str]:
    return frozenset(v.name for v in rule.variables)


def rules_share_variable(rule1: SecRule, rule2: SecRule) -> bool:
    """True if both rules target at least one common ModSecurity variable."""
    return bool(_variable_names(rule1) & _variable_names(rule2))


def _chain_variable_names(chain: Sequence[SecRule]) -> frozenset[str]:
    names: set[str] = set()
    for rule in chain:
        names.update(v.name for v in rule.variables)
    return frozenset(names)


def chains_share_variable(chain1: Sequence[SecRule], chain2: Sequence[SecRule]) -> bool:
    """True if any link of chain1 and any link of chain2 target a common variable."""
    return bool(_chain_variable_names(chain1) & _chain_variable_names(chain2))
