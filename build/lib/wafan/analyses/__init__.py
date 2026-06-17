"""SMT-based analyses of ModSecurity SecRule rulesets.

Implemented analyses:

  SubsumptionChecker – detects pairs where one rule's (or chain's) match
  condition is a subset of another's (rule1 subsumed by rule2 means every
  input triggering rule1 also triggers rule2).

  IntersectionChecker – detects pairs with a non-empty intersection, i.e.
  there exists at least one input that triggers both rules (or chains)
  simultaneously.

  WitnessChecker – finds concrete inputs (models) that trigger a rule or
  chain of rules.

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
    chains_share_variable,
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
    "WitnessResult",
    "ChainWitnessResult",
    "WitnessChecker",
    "witness_smt2",
    "chain_witness_smt2",
    "rules_share_variable",
    "chains_share_variable",
]
