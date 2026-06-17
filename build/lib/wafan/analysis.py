"""SMT-based analysis of ModSecurity SecRule rulesets.

Implemented analyses:

  SubsumptionChecker – detects pairs where one rule's match condition is a
  subset of another's (rule1 subsumed by rule2 means every input triggering
  rule1 also triggers rule2).

  IntersectionChecker – detects pairs with a non-empty intersection, i.e.
  there exists at least one input that triggers both rules simultaneously.

The module is solver-agnostic: any object implementing SolverBackend can be
supplied.  SubprocessSolver calls an external binary (default: z3-noodler)
via stdin/stdout using the SMT-LIB2 format produced by wafan.smt.
"""

from __future__ import annotations

import re as _re
import subprocess
from dataclasses import dataclass
from enum import Enum
from typing import Protocol, Sequence

from .parser import SecRule, group_chains
from .regex_conv import pcre_to_ecma2020
from .smt import (
    SMT_LOGIC,
    SmtFormula,
    UnsupportedTransformError,
    _escape_smt_string,
    _merge_unique,
    apply_transforms_smt,
    chain_to_smt,
    effective_transforms,
    rx_rule_to_smt,
    transform_preamble,
)


# ---------------------------------------------------------------------------
# Solver abstraction
# ---------------------------------------------------------------------------

class SolverResult(Enum):
    SAT = "sat"        # counterexample found → not subsumed
    UNSAT = "unsat"    # no counterexample   → subsumed
    UNKNOWN = "unknown"


class SolverBackend(Protocol):
    """Minimal interface for an SMT solver backend."""

    def solve(self, smt2: str) -> SolverResult: ...


class SubprocessSolver:
    """Call an external SMT solver (e.g. z3-noodler) via stdin/stdout."""

    def __init__(self, argv: list[str] | None = None, timeout: int = 30) -> None:
        self.argv = argv or ["z3", "-in"]
        self.timeout = timeout

    def solve(self, smt2: str) -> SolverResult:
        try:
            proc = subprocess.run(
                self.argv,
                input=smt2,
                capture_output=True,
                text=True,
                timeout=self.timeout,
            )
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return SolverResult.UNKNOWN

        first = proc.stdout.strip().splitlines()[0] if proc.stdout.strip() else ""
        try:
            return SolverResult(first)
        except ValueError:
            return SolverResult.UNKNOWN

    def solve_with_model(self, smt2: str) -> tuple[SolverResult, dict[str, str] | None]:
        """Run solver and return (result, model).

        The model is a dict mapping variable names to their string values, or
        None if the result is not SAT or the model could not be parsed.

        The formula must include a (get-value ...) command after (check-sat),
        and the solver must be invoked with model generation enabled.  This is
        handled automatically by the witness analysis: the solver argv is
        extended with 'model=true' when needed.
        """
        model_argv = _argv_with_model(self.argv)
        try:
            proc = subprocess.run(
                model_argv,
                input=smt2,
                capture_output=True,
                text=True,
                timeout=self.timeout,
            )
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return SolverResult.UNKNOWN, None

        output = proc.stdout.strip()
        lines = output.splitlines()
        first = lines[0] if lines else ""
        try:
            result = SolverResult(first)
        except ValueError:
            return SolverResult.UNKNOWN, None

        if result != SolverResult.SAT:
            return result, None

        model = _parse_get_value_output("\n".join(lines[1:]))
        return result, model


def _argv_with_model(argv: list[str]) -> list[str]:
    """Return argv extended with model=true unless already present."""
    if any(a.startswith("model") for a in argv):
        return argv
    return argv + ["model=true"]


def _parse_get_value_output(text: str) -> dict[str, str] | None:
    """Parse z3's (get-value ...) response into {name: value} dict.

    Expected format (one or more bindings):
        ((VAR1 "value1")
         (VAR2 "value2"))

    Returns None if parsing fails.
    """
    result: dict[str, str] = {}
    for m in _re.finditer(r'\((\w+)\s+"((?:[^"\\]|\\.)*)"\)', text):
        name = m.group(1)
        value = m.group(2).replace('\\"', '"').replace("\\\\", "\\")
        result[name] = value
    return result if result else None


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# Subsumption query generation
# ---------------------------------------------------------------------------

def _match_assertion(var_expr: str, pattern: str, negated: bool) -> str:
    escaped = _escape_smt_string(pattern)
    atom = f'(str.in_re {var_expr} (re.from_ecma2020 "{escaped}"))'
    return f"(not {atom})" if negated else atom


def subsumption_smt2(rule1: SecRule, rule2: SecRule) -> str:
    """Return an SMT-LIB2 string that is UNSAT iff rule1 is subsumed by rule2.

    The query asks: does there exist an input x that triggers rule1 but NOT
    rule2?  If UNSAT, no such x exists, so rule1 ⊆ rule2.

    Both rules' transformation chains are applied to the same free variable x.
    Uninterpreted transforms are declared and axiomatised in the preamble.

    Raises UnsupportedTransformError if either rule uses an unknown transform.
    """
    transforms1 = effective_transforms(rule1)
    transforms2 = effective_transforms(rule2)

    fd1, ax1 = transform_preamble(transforms1)
    fd2, ax2 = transform_preamble(transforms2)
    fun_decls = _merge_unique(fd1, fd2)
    axioms    = _merge_unique(ax1, ax2)

    negated1 = rule1.negated or rule1.operator == "!@rx"
    negated2 = rule2.negated or rule2.operator == "!@rx"

    conv1 = pcre_to_ecma2020(rule1.operator_argument)
    conv2 = pcre_to_ecma2020(rule2.operator_argument)

    var_expr1 = apply_transforms_smt("x", transforms1)
    var_expr2 = apply_transforms_smt("x", transforms2)

    assert1 = _match_assertion(var_expr1, conv1.pattern, negated1)
    assert2 = f"(not {_match_assertion(var_expr2, conv2.pattern, negated2)})"

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; subsumption check: rule {rule1.rule_id} subsumed by rule {rule2.rule_id}?",
        "; UNSAT => subsumed  |  SAT => not subsumed (witness exists)",
        *fun_decls,
        *axioms,
        "(declare-const x String)",
        f"(assert {assert1})",
        f"(assert {assert2})",
        "(check-sat)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Intersection query generation
# ---------------------------------------------------------------------------

def intersection_smt2(rule1: SecRule, rule2: SecRule) -> str:
    """Return an SMT-LIB2 string that is SAT iff rule1 and rule2 have a
    non-empty intersection (some input triggers both rules simultaneously).

    Both rules' transformation chains are applied to the same free variable x.
    Uninterpreted transforms are declared and axiomatised in the preamble.

    Raises UnsupportedTransformError if either rule uses an unknown transform.
    """
    transforms1 = effective_transforms(rule1)
    transforms2 = effective_transforms(rule2)

    fd1, ax1 = transform_preamble(transforms1)
    fd2, ax2 = transform_preamble(transforms2)
    fun_decls = _merge_unique(fd1, fd2)
    axioms    = _merge_unique(ax1, ax2)

    negated1 = rule1.negated or rule1.operator == "!@rx"
    negated2 = rule2.negated or rule2.operator == "!@rx"

    conv1 = pcre_to_ecma2020(rule1.operator_argument)
    conv2 = pcre_to_ecma2020(rule2.operator_argument)

    var_expr1 = apply_transforms_smt("x", transforms1)
    var_expr2 = apply_transforms_smt("x", transforms2)

    assert1 = _match_assertion(var_expr1, conv1.pattern, negated1)
    assert2 = _match_assertion(var_expr2, conv2.pattern, negated2)

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; intersection check: rule {rule1.rule_id} ∩ rule {rule2.rule_id} ≠ ∅?",
        "; SAT => non-empty intersection  |  UNSAT => disjoint",
        *fun_decls,
        *axioms,
        "(declare-const x String)",
        f"(assert {assert1})",
        f"(assert {assert2})",
        "(check-sat)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Chained-rule query generation
# ---------------------------------------------------------------------------

def chain_subsumption_smt2(chain1: Sequence[SecRule], chain2: Sequence[SecRule]) -> str:
    """Return an SMT-LIB2 string that is UNSAT iff chain1 is subsumed by chain2.

    Each chain matches only if all of its links match (logical AND, see
    chain_to_smt). The query asks: does there exist an input that satisfies
    chain1's conjunction but not chain2's?  If UNSAT, chain1 ⊆ chain2.

    Declarations for ModSecurity variables shared by name between the two
    chains are merged, so both chains' conditions are evaluated against the
    same request.

    Raises UnsupportedTransformError if any link uses an unknown transform.
    """
    f1 = chain_to_smt(chain1)
    f2 = chain_to_smt(chain2)

    declarations = _merge_unique(f1.declarations, f2.declarations)
    fun_decls = _merge_unique(f1.fun_declarations, f2.fun_declarations)
    axioms = _merge_unique(f1.axioms, f2.axioms)

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; chain subsumption check: chain {chain1[0].rule_id} subsumed by chain {chain2[0].rule_id}?",
        "; UNSAT => subsumed  |  SAT => not subsumed (witness exists)",
        *fun_decls,
        *axioms,
        *declarations,
        f"(assert {f1.assertion})",
        f"(assert (not {f2.assertion}))",
        "(check-sat)",
    ]
    return "\n".join(lines)


def chain_intersection_smt2(chain1: Sequence[SecRule], chain2: Sequence[SecRule]) -> str:
    """Return an SMT-LIB2 string that is SAT iff chain1 and chain2 have a
    non-empty intersection (some input triggers both chains simultaneously).

    Each chain matches only if all of its links match (logical AND, see
    chain_to_smt). Declarations for ModSecurity variables shared by name
    between the two chains are merged, so both chains' conditions are
    evaluated against the same request.

    Raises UnsupportedTransformError if any link uses an unknown transform.
    """
    f1 = chain_to_smt(chain1)
    f2 = chain_to_smt(chain2)

    declarations = _merge_unique(f1.declarations, f2.declarations)
    fun_decls = _merge_unique(f1.fun_declarations, f2.fun_declarations)
    axioms = _merge_unique(f1.axioms, f2.axioms)

    lines = [
        f"(set-logic {SMT_LOGIC})",
        f"; chain intersection check: chain {chain1[0].rule_id} ∩ chain {chain2[0].rule_id} ≠ ∅?",
        "; SAT => non-empty intersection  |  UNSAT => disjoint",
        *fun_decls,
        *axioms,
        *declarations,
        f"(assert {f1.assertion})",
        f"(assert {f2.assertion})",
        "(check-sat)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Variable compatibility
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# Subsumption checker
# ---------------------------------------------------------------------------

@dataclass
class SubsumptionResult:
    """Outcome of checking whether rule1 is subsumed by rule2."""

    rule1: SecRule
    rule2: SecRule
    result: SolverResult

    @property
    def is_subsumed(self) -> bool:
        return self.result == SolverResult.UNSAT


@dataclass
class IntersectionResult:
    """Outcome of checking whether rule1 and rule2 have a non-empty intersection."""

    rule1: SecRule
    rule2: SecRule
    result: SolverResult

    @property
    def has_intersection(self) -> bool:
        return self.result == SolverResult.SAT


@dataclass
class ChainSubsumptionResult:
    """Outcome of checking whether chain1 is subsumed by chain2."""

    chain1: list[SecRule]
    chain2: list[SecRule]
    result: SolverResult

    @property
    def is_subsumed(self) -> bool:
        return self.result == SolverResult.UNSAT


@dataclass
class ChainIntersectionResult:
    """Outcome of checking whether chain1 and chain2 have a non-empty intersection."""

    chain1: list[SecRule]
    chain2: list[SecRule]
    result: SolverResult

    @property
    def has_intersection(self) -> bool:
        return self.result == SolverResult.SAT


class IntersectionChecker:
    """Check whether pairs of @rx SecRules share a non-empty intersection."""

    def __init__(self, solver: SolverBackend, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check_pair(self, rule1: SecRule, rule2: SecRule) -> IntersectionResult:
        """Check if there is an input that triggers both rule1 and rule2.

        Returns UNKNOWN if either rule uses an unsupported transform or if the
        rules target disjoint sets of variables.
        """
        lhs = _rule_label(rule1)
        rhs = _rule_label(rule2)
        prefix = f"  {lhs}  ∩  {rhs}"

        if not rules_share_variable(rule1, rule2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return IntersectionResult(rule1, rule2, SolverResult.UNKNOWN)

        try:
            smt2 = intersection_smt2(rule1, rule2)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return IntersectionResult(rule1, rule2, SolverResult.UNKNOWN)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "INTERSECTING",
                SolverResult.UNSAT: "disjoint",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return IntersectionResult(rule1, rule2, result)

    def find_intersecting(self, rules: Sequence[SecRule]) -> list[IntersectionResult]:
        """Return all unordered pairs (R1, R2) whose intersection is non-empty.

        Only @rx / !@rx rules are considered.  Each unordered pair is checked
        once; pairs where the solver returns UNKNOWN are excluded.
        """
        rx_rules = [r for r in rules if r.operator in ("@rx", "!@rx")]
        n = len(rx_rules)
        if self._verbosity >= 1:
            print(f"Intersection analysis: {n} rules, {n * (n - 1) // 2} unordered pairs\n")
        results: list[IntersectionResult] = []

        for i, r1 in enumerate(rx_rules):
            for r2 in rx_rules[i + 1:]:
                res = self.check_pair(r1, r2)
                if res.result != SolverResult.UNKNOWN:
                    results.append(res)

        return results

    def check_chain_pair(
        self, chain1: Sequence[SecRule], chain2: Sequence[SecRule]
    ) -> ChainIntersectionResult:
        """Check if there is an input that triggers both chain1 and chain2.

        Returns UNKNOWN if either chain contains a non-@rx link, uses an
        unsupported transform, or the chains target disjoint sets of
        variables.
        """
        chain1, chain2 = list(chain1), list(chain2)
        lhs = _chain_label(chain1)
        rhs = _chain_label(chain2)
        prefix = f"  {lhs}  ∩  {rhs}"

        if not _all_rx(chain1) or not _all_rx(chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (not @rx)")
            return ChainIntersectionResult(chain1, chain2, SolverResult.UNKNOWN)

        if not chains_share_variable(chain1, chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return ChainIntersectionResult(chain1, chain2, SolverResult.UNKNOWN)

        try:
            smt2 = chain_intersection_smt2(chain1, chain2)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return ChainIntersectionResult(chain1, chain2, SolverResult.UNKNOWN)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "INTERSECTING",
                SolverResult.UNSAT: "disjoint",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return ChainIntersectionResult(chain1, chain2, result)

    def find_intersecting_chains(self, rules: Sequence[SecRule]) -> list[ChainIntersectionResult]:
        """Return all unordered pairs of chains whose intersection is non-empty.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own); only chains whose every link is @rx /
        !@rx are considered. Each unordered pair is checked once; pairs
        where the solver returns UNKNOWN are excluded.
        """
        chains = group_chains(list(rules))
        n = len(chains)
        if self._verbosity >= 1:
            print(f"Chain intersection analysis: {n} chains, {n * (n - 1) // 2} unordered pairs\n")
        results: list[ChainIntersectionResult] = []

        for i, c1 in enumerate(chains):
            for c2 in chains[i + 1:]:
                res = self.check_chain_pair(c1, c2)
                if res.result != SolverResult.UNKNOWN:
                    results.append(res)

        return results


class SubsumptionChecker:
    """Check subsumption between pairs of @rx SecRules using an SMT solver."""

    def __init__(self, solver: SolverBackend, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check_pair(self, rule1: SecRule, rule2: SecRule) -> SubsumptionResult:
        """Check if rule1 is subsumed by rule2.

        Returns UNKNOWN if either rule uses an unsupported transform or if the
        rules target disjoint sets of variables.
        """
        lhs = _rule_label(rule1)
        rhs = _rule_label(rule2)
        prefix = f"  {lhs}  ⊆  {rhs}"

        if not rules_share_variable(rule1, rule2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN)

        try:
            smt2 = subsumption_smt2(rule1, rule2)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.UNSAT: "SUBSUMED",
                SolverResult.SAT: "not subsumed",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return SubsumptionResult(rule1, rule2, result)

    def find_subsumed(self, rules: Sequence[SecRule]) -> list[SubsumptionResult]:
        """Return all ordered pairs (R1, R2) where R1 is subsumed by R2.

        Only @rx / !@rx rules are considered.  All ordered pairs with distinct
        rule ids are checked; pairs where the solver returns UNKNOWN are
        excluded from the result.
        """
        rx_rules = [r for r in rules if r.operator in ("@rx", "!@rx")]
        n = len(rx_rules)
        if self._verbosity >= 1:
            print(f"Subsumption analysis: {n} rules, {n * (n - 1)} ordered pairs\n")
        results: list[SubsumptionResult] = []

        for i, r1 in enumerate(rx_rules):
            for j, r2 in enumerate(rx_rules):
                if i == j:
                    continue
                res = self.check_pair(r1, r2)
                if res.result != SolverResult.UNKNOWN:
                    results.append(res)

        return results

    def check_chain_pair(
        self, chain1: Sequence[SecRule], chain2: Sequence[SecRule]
    ) -> ChainSubsumptionResult:
        """Check if chain1 is subsumed by chain2.

        Returns UNKNOWN if either chain contains a non-@rx link, uses an
        unsupported transform, or the chains target disjoint sets of
        variables.
        """
        chain1, chain2 = list(chain1), list(chain2)
        lhs = _chain_label(chain1)
        rhs = _chain_label(chain2)
        prefix = f"  {lhs}  ⊆  {rhs}"

        if not _all_rx(chain1) or not _all_rx(chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (not @rx)")
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN)

        if not chains_share_variable(chain1, chain2):
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (no shared variable)")
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN)

        try:
            smt2 = chain_subsumption_smt2(chain1, chain2)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  [{'skipped':<12}]  (unsupported transform: {exc})")
            return ChainSubsumptionResult(chain1, chain2, SolverResult.UNKNOWN)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.UNSAT: "SUBSUMED",
                SolverResult.SAT: "not subsumed",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  [{outcome:<12}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)
        return ChainSubsumptionResult(chain1, chain2, result)

    def find_subsumed_chains(self, rules: Sequence[SecRule]) -> list[ChainSubsumptionResult]:
        """Return all ordered pairs of chains where chain1 is subsumed by chain2.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own); only chains whose every link is @rx /
        !@rx are considered. All ordered pairs of distinct chains are
        checked; pairs where the solver returns UNKNOWN are excluded.
        """
        chains = group_chains(list(rules))
        n = len(chains)
        if self._verbosity >= 1:
            print(f"Chain subsumption analysis: {n} chains, {n * (n - 1)} ordered pairs\n")
        results: list[ChainSubsumptionResult] = []

        for i, c1 in enumerate(chains):
            for j, c2 in enumerate(chains):
                if i == j:
                    continue
                res = self.check_chain_pair(c1, c2)
                if res.result != SolverResult.UNKNOWN:
                    results.append(res)

        return results


# ---------------------------------------------------------------------------
# Witness (concrete model) query generation
# ---------------------------------------------------------------------------

def witness_smt2(rule: SecRule) -> str:
    """Return an SMT-LIB2 string that, when SAT, yields a concrete input
    triggering *rule*.

    The formula asserts the rule's match condition for each of its variables.
    A (get-value ...) command is appended so the solver can return concrete
    string values.  The solver must be invoked with model generation enabled
    (e.g. z3 model=true -in).

    Raises:
        ValueError: if the operator is not @rx / !@rx.
        UnsupportedTransformError: if a t: action is unknown.
    """
    formula: SmtFormula = rx_rule_to_smt(rule)
    return formula.to_smt2_with_model()


def chain_witness_smt2(chain: Sequence[SecRule]) -> str:
    """Return an SMT-LIB2 string that, when SAT, yields a concrete input
    triggering every link of *chain* simultaneously.

    The formula asserts the conjunction of each link's match condition (see
    chain_to_smt). A (get-value ...) command is appended so the solver can
    return concrete string values. The solver must be invoked with model
    generation enabled (e.g. z3 model=true -in).

    Raises:
        ValueError: if any link's operator is not @rx / !@rx.
        UnsupportedTransformError: if any link uses an unknown transform.
    """
    formula: SmtFormula = chain_to_smt(chain)
    return formula.to_smt2_with_model()


# ---------------------------------------------------------------------------
# Witness checker
# ---------------------------------------------------------------------------

@dataclass
class WitnessResult:
    """Outcome of finding a concrete input that triggers *rule*.

    If *result* is SAT, *model* maps each ModSecurity variable name (as used
    in the SMT formula) to a concrete string value that satisfies the rule.
    For unsupported rules the result is UNKNOWN and model is None.
    """

    rule: SecRule
    result: SolverResult
    model: dict[str, str] | None = None

    @property
    def has_witness(self) -> bool:
        return self.result == SolverResult.SAT

    def format_model(self) -> str:
        """Return a human-readable representation of the model."""
        if not self.model:
            return "    (no model)"
        return "\n".join(f"    {k} = {v!r}" for k, v in self.model.items())


@dataclass
class ChainWitnessResult:
    """Outcome of finding a concrete input that triggers every link of *chain*.

    If *result* is SAT, *model* maps each ModSecurity variable name (as used
    in the SMT formula) to a concrete string value that satisfies all links
    of the chain simultaneously. For unsupported chains the result is
    UNKNOWN and model is None.
    """

    chain: list[SecRule]
    result: SolverResult
    model: dict[str, str] | None = None

    @property
    def has_witness(self) -> bool:
        return self.result == SolverResult.SAT

    def format_model(self) -> str:
        """Return a human-readable representation of the model."""
        if not self.model:
            return "    (no model)"
        return "\n".join(f"    {k} = {v!r}" for k, v in self.model.items())


class WitnessChecker:
    """Find concrete inputs (witnesses/models) that trigger @rx SecRules.

    Requires a SubprocessSolver (or any object with a solve_with_model
    method) so that the SMT model can be extracted from the solver output.
    """

    def __init__(self, solver: SubprocessSolver, verbosity: int = 0) -> None:
        self._solver = solver
        self._verbosity = verbosity

    def check_rule(self, rule: SecRule) -> WitnessResult:
        """Find a concrete input that triggers *rule*, if one exists.

        Returns UNKNOWN if the rule uses an unsupported transform or a
        non-@rx operator.
        """
        label = _rule_label(rule)

        if rule.operator not in ("@rx", "!@rx"):
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (not @rx)")
            return WitnessResult(rule, SolverResult.UNKNOWN)

        try:
            smt2 = witness_smt2(rule)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (unsupported transform: {exc})")
            return WitnessResult(rule, SolverResult.UNKNOWN)

        result, model = self._solver.solve_with_model(smt2)

        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "SAT",
                SolverResult.UNSAT: "never matches",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"  {label}  [{outcome:<13}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)

        return WitnessResult(rule, result, model)

    def find_witnesses(self, rules: Sequence[SecRule]) -> list[WitnessResult]:
        """Return WitnessResults for all @rx / !@rx rules.

        Rules where the solver returns UNKNOWN are included so callers can
        distinguish unsatisfiable rules from solver failures.
        """
        rx_rules = [r for r in rules if r.operator in ("@rx", "!@rx")]
        if self._verbosity >= 1:
            print(f"Witness analysis: {len(rx_rules)} rules\n")
        return [self.check_rule(r) for r in rx_rules]

    def check_chain(self, chain: Sequence[SecRule]) -> ChainWitnessResult:
        """Find a concrete input that triggers every link of *chain*, if one exists.

        Returns UNKNOWN if any link uses an unsupported transform or a
        non-@rx operator.
        """
        chain = list(chain)
        label = _chain_label(chain)

        if not _all_rx(chain):
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (not @rx)")
            return ChainWitnessResult(chain, SolverResult.UNKNOWN)

        try:
            smt2 = chain_witness_smt2(chain)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"  {label}  [{'skipped':<13}]  (unsupported transform: {exc})")
            return ChainWitnessResult(chain, SolverResult.UNKNOWN)

        result, model = self._solver.solve_with_model(smt2)

        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "SAT",
                SolverResult.UNSAT: "never matches",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"  {label}  [{outcome:<13}]")
        if self._verbosity >= 2:
            _print_smt_block(smt2)

        return ChainWitnessResult(chain, result, model)

    def find_chain_witnesses(self, rules: Sequence[SecRule]) -> list[ChainWitnessResult]:
        """Return ChainWitnessResults for all chains of @rx / !@rx rules.

        Rules are grouped into chains via group_chains() (a non-chained rule
        forms a chain of its own). Chains where the solver returns UNKNOWN
        are included so callers can distinguish unsatisfiable chains from
        solver failures.
        """
        chains = group_chains(list(rules))
        if self._verbosity >= 1:
            print(f"Chain witness analysis: {len(chains)} chains\n")
        return [self.check_chain(c) for c in chains]
