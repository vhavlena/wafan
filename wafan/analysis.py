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

from .parser import SecRule
from .regex_conv import pcre_to_ecma2020
from .smt import (
    SMT_LOGIC,
    SmtFormula,
    UnsupportedTransformError,
    _escape_smt_string,
    apply_transforms_smt,
    extract_transforms,
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

def _merge_unique(a: list[str], b: list[str]) -> list[str]:
    """Concatenate two lists, dropping duplicates from b that already appear in a."""
    seen = set(a)
    return a + [x for x in b if x not in seen]


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
    transforms1 = extract_transforms(rule1.actions)
    transforms2 = extract_transforms(rule2.actions)

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
    transforms1 = extract_transforms(rule1.actions)
    transforms2 = extract_transforms(rule2.actions)

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
# Variable compatibility
# ---------------------------------------------------------------------------

def _variable_names(rule: SecRule) -> frozenset[str]:
    return frozenset(v.name for v in rule.variables)


def rules_share_variable(rule1: SecRule, rule2: SecRule) -> bool:
    """True if both rules target at least one common ModSecurity variable."""
    return bool(_variable_names(rule1) & _variable_names(rule2))


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
                print(f"{prefix}  →  skipped (no shared variable)")
            return IntersectionResult(rule1, rule2, SolverResult.UNKNOWN)

        try:
            smt2 = intersection_smt2(rule1, rule2)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  →  skipped (unsupported transform: {exc})")
            return IntersectionResult(rule1, rule2, SolverResult.UNKNOWN)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "INTERSECTING",
                SolverResult.UNSAT: "disjoint",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  →  {outcome}")
        if self._verbosity >= 2:
            print(f"[smt2]\n{smt2}\n[/smt2]", flush=True)
        return IntersectionResult(rule1, rule2, result)

    def find_intersecting(self, rules: Sequence[SecRule]) -> list[IntersectionResult]:
        """Return all unordered pairs (R1, R2) whose intersection is non-empty.

        Only @rx / !@rx rules are considered.  Each unordered pair is checked
        once; pairs where the solver returns UNKNOWN are excluded.
        """
        rx_rules = [r for r in rules if r.operator in ("@rx", "!@rx")]
        n = len(rx_rules)
        if self._verbosity >= 1:
            print(f"[intersection] {n} rules, {n * (n - 1) // 2} unordered pairs to check")
        results: list[IntersectionResult] = []

        for i, r1 in enumerate(rx_rules):
            for r2 in rx_rules[i + 1:]:
                res = self.check_pair(r1, r2)
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
                print(f"{prefix}  →  skipped (no shared variable)")
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN)

        try:
            smt2 = subsumption_smt2(rule1, rule2)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"{prefix}  →  skipped (unsupported transform: {exc})")
            return SubsumptionResult(rule1, rule2, SolverResult.UNKNOWN)

        result = self._solver.solve(smt2)
        if self._verbosity >= 1:
            outcome = {
                SolverResult.UNSAT: "SUBSUMED",
                SolverResult.SAT: "not subsumed",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"{prefix}  →  {outcome}")
        if self._verbosity >= 2:
            print(f"[smt2]\n{smt2}\n[/smt2]", flush=True)
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
            print(f"[subsumption] {n} rules, {n * (n - 1)} ordered pairs to check")
        results: list[SubsumptionResult] = []

        for i, r1 in enumerate(rx_rules):
            for j, r2 in enumerate(rx_rules):
                if i == j:
                    continue
                res = self.check_pair(r1, r2)
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
            return "(no model)"
        return "  " + "\n  ".join(f"{k} = {v!r}" for k, v in self.model.items())


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
                print(f"  {label}  →  skipped (not @rx)")
            return WitnessResult(rule, SolverResult.UNKNOWN)

        try:
            smt2 = witness_smt2(rule)
        except UnsupportedTransformError as exc:
            if self._verbosity >= 1:
                print(f"  {label}  →  skipped (unsupported transform: {exc})")
            return WitnessResult(rule, SolverResult.UNKNOWN)

        result, model = self._solver.solve_with_model(smt2)

        if self._verbosity >= 1:
            outcome = {
                SolverResult.SAT: "SAT",
                SolverResult.UNSAT: "UNSAT (rule never matches)",
                SolverResult.UNKNOWN: "unknown",
            }[result]
            print(f"  {label}  →  {outcome}")
        if self._verbosity >= 2:
            print(f"[smt2]\n{smt2}\n[/smt2]", flush=True)

        return WitnessResult(rule, result, model)

    def find_witnesses(self, rules: Sequence[SecRule]) -> list[WitnessResult]:
        """Return WitnessResults for all @rx / !@rx rules.

        Rules where the solver returns UNKNOWN are included so callers can
        distinguish unsatisfiable rules from solver failures.
        """
        rx_rules = [r for r in rules if r.operator in ("@rx", "!@rx")]
        if self._verbosity >= 1:
            print(f"[witness] {len(rx_rules)} rules to check")
        return [self.check_rule(r) for r in rx_rules]
