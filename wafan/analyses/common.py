"""Shared helpers used across the subsumption, intersection and witness analyses."""

from __future__ import annotations

from typing import Sequence

from ..parser import SecRule
from ..smt import (
    _merge_unique,
    _normalize_operator,
    _OPERATORS,
    _restrictable_transform_keys,
    _rules_relevant_codepoints,
    effective_transforms,
    is_supported_operator,
    transform_preamble,
    UnsupportedOperatorError,
)

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


def _all_supported(chain: Sequence[SecRule]) -> bool:
    """True if every link of *chain* uses an SMT-convertible operator."""
    return all(is_supported_operator(r.operator) for r in chain)


def chain_support_status(chain: Sequence[SecRule]) -> str:
    """Classify why a chain can or cannot be turned into an SMT query.

    Returns one of ``"ok"``, ``"unsupported_operator"``,
    ``"unsupported_transform"`` or ``"unsupported_pattern"``. Used for
    reporting/statistics purposes (e.g. the ``--json`` summary), independent
    of any particular pairwise analysis.
    """
    if not _all_supported(chain):
        return "unsupported_operator"
    from ..regex_conv import UnsupportedPatternError
    from ..smt import UnsupportedOperatorError, UnsupportedTransformError, chain_to_smt

    try:
        chain_to_smt(chain)
    except UnsupportedTransformError:
        return "unsupported_transform"
    except UnsupportedPatternError:
        return "unsupported_pattern"
    except UnsupportedOperatorError:
        # is_supported_operator() only checks the operator *name*; numeric
        # operators (@eq/@ge/...) can still fail deep in chain_to_smt() if
        # their argument isn't a literal integer (e.g. a ModSecurity
        # macro like %{tx.sampling_percentage}).
        return "unsupported_operator"
    return "ok"


def _operator_assertion(rule: SecRule, var_expr: str) -> str:
    """Return the SMT-LIB2 assertion for *rule*'s operator applied to *var_expr*.

    Raises UnsupportedOperatorError if the rule's operator is not supported
    (or, for numeric operators, its argument is not an integer).
    """
    op_name, op_negated = _normalize_operator(rule.operator)
    builder = _OPERATORS.get(op_name)
    if builder is None:
        raise UnsupportedOperatorError(
            f"Rule {rule.rule_id}: operator '{rule.operator}' is not supported"
        )
    negated = rule.negated or op_negated
    return builder(var_expr, rule.operator_argument, negated)


def _joint_transform_preamble(
    rules_a: Sequence[SecRule], rules_b: Sequence[SecRule]
) -> tuple[list[str], list[str]]:
    """Return ``(fun_declarations, axioms)`` for two rule/chain sides being
    merged into one pairwise SMT-LIB2 script (intersection or subsumption).

    A transform shared by both sides (e.g. ``t_urlDecode``) is one global SMT
    symbol, so it must get exactly one declaration across the merged script.
    Restricting that declaration to a codepoint set is only sound if it
    covers what *either* side needs, so *rules_a* and *rules_b* are analysed
    together: the relevant-codepoint set is the union of both sides' own sets
    (or None/unrestricted as soon as either side's is unknown), and a
    transform is only restricted if it is safe to restrict across every rule
    of both sides combined (see ``wafan.smt._restrictable_transform_keys``).
    """
    relevant_a = _rules_relevant_codepoints(rules_a)
    relevant_b = _rules_relevant_codepoints(rules_b)
    joint_relevant = (
        None if relevant_a is None or relevant_b is None else relevant_a | relevant_b
    )

    transform_lists = [effective_transforms(r) for r in (*rules_a, *rules_b)]
    joint_restrictable = _restrictable_transform_keys(transform_lists)

    fun_decls: list[str] = []
    axioms: list[str] = []
    for transforms in transform_lists:
        fd, ax = transform_preamble(transforms, joint_relevant, joint_restrictable)
        fun_decls = _merge_unique(fun_decls, fd)
        axioms = _merge_unique(axioms, ax)
    return fun_decls, axioms


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
