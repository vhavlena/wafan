"""SMT-based analyses of ModSecurity SecRule rulesets.

Implemented analyses:

  SubsumptionChecker – detects pairs where one rule's (or chain's) match
  condition is a subset of another's (rule1 subsumed by rule2 means every
  input triggering rule1 also triggers rule2).

  IntersectionChecker – detects pairs with a non-empty intersection, i.e.
  there exists at least one input that triggers both rules (or chains)
  simultaneously.

  ContradictionChecker – like IntersectionChecker, but additionally requires
  the two rules (or chains) to disagree on the disruptive action taken for
  that shared input (one accepts it, the other denies it).

  WitnessChecker – finds concrete inputs (models) that trigger a rule or
  chain of rules.

  ReachabilityChecker – finds rules that can never fire, using the order-aware
  whole-ruleset state model in wafan.state: control flow (skipAfter,
  ctl:ruleRemoveById, disruptive actions) and TX state written by
  SecAction/setvar are both modelled, so a rule guarded by state nothing
  produces is reported as dead code.

  StatefulPairChecker – intersection / subsumption / shadowing over the same
  model, comparing whether two rules can actually both *fire* rather than
  merely both match.

Each analysis is solver-agnostic: any object implementing SolverBackend can
be supplied. SubprocessSolver calls an external binary (default: z3-noodler)
via stdin/stdout using the SMT-LIB2 format produced by wafan.smt.
"""

from .common import (
    _all_supported,
    _chain_label,
    _chain_variable_names,
    _operator_assertion,
    _print_smt_block,
    _rule_label,
    _SMT_SEP,
    _variable_names,
    chain_common_witness,
    chain_disposition,
    chain_escaping_witness,
    chain_support_detail,
    chain_support_status,
    chain_value_families,
    chains_share_target,
    chains_share_variable,
    intersection_outcome_label,
    rule_disposition,
    rules_share_variable,
)
from .solver import (
    SolverBackend,
    SolverResult,
    SubprocessSolver,
    _argv_with_model,
    _parse_get_value_output,
)
from .subsumption import (
    ChainSubsumptionResult,
    SubsumptionChecker,
    SubsumptionResult,
    chain_subsumption_smt2,
    subsumption_smt2,
)
from .intersection import (
    ChainIntersectionResult,
    IntersectionChecker,
    IntersectionResult,
    chain_intersection_smt2,
    intersection_smt2,
)
from .contradiction import (
    ChainContradictionResult,
    ContradictionChecker,
    ContradictionResult,
    chain_contradiction_smt2,
    contradiction_smt2,
)
from .reachability import (
    IMPOSSIBLE_MATCH,
    OK,
    UNREACHABLE,
    ReachabilityChecker,
    ReachabilityResult,
    analyse_reachability,
)
from .stateful import (
    INTERSECTION,
    SHADOWING,
    SUBSUMPTION,
    StatefulPairChecker,
    StatefulPairResult,
)
from .witness import (
    ChainWitnessResult,
    WitnessChecker,
    WitnessResult,
    chain_witness_smt2,
    witness_smt2,
)

__all__ = [
    "SolverResult",
    "SolverBackend",
    "SubprocessSolver",
    "SubsumptionResult",
    "ChainSubsumptionResult",
    "SubsumptionChecker",
    "subsumption_smt2",
    "chain_subsumption_smt2",
    "IntersectionResult",
    "ChainIntersectionResult",
    "IntersectionChecker",
    "intersection_smt2",
    "chain_intersection_smt2",
    "ContradictionResult",
    "ChainContradictionResult",
    "ContradictionChecker",
    "contradiction_smt2",
    "chain_contradiction_smt2",
    "WitnessResult",
    "ChainWitnessResult",
    "WitnessChecker",
    "witness_smt2",
    "chain_witness_smt2",
    "rules_share_variable",
    "chains_share_variable",
    "chains_share_target",
    "chain_value_families",
    "chain_common_witness",
    "chain_escaping_witness",
    "chain_support_status",
    "chain_support_detail",
    "rule_disposition",
    "chain_disposition",
    "intersection_outcome_label",
    "ReachabilityChecker",
    "ReachabilityResult",
    "analyse_reachability",
    "OK",
    "UNREACHABLE",
    "IMPOSSIBLE_MATCH",
    "StatefulPairChecker",
    "StatefulPairResult",
    "INTERSECTION",
    "SUBSUMPTION",
    "SHADOWING",
]
