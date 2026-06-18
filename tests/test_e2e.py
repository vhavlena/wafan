"""End-to-end tests for wafan analyses.

Each E2ECase bundles inline ModSecurity rules with the expected results for
all three analyses (intersection, subsumption, witness).  Adding a new
scenario means appending one more E2ECase to the CASES list — no new test
functions needed.

Tests require a z3 build with re.from_ecma2020 support.
Set WAFAN_Z3_PATH to the binary path to enable them.
"""

from __future__ import annotations

import os
import textwrap
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from wafan.analyses import (
    IntersectionChecker,
    SolverResult,
    SubprocessSolver,
    SubsumptionChecker,
    WitnessChecker,
)
from wafan.parser import parse_rx_rules

Z3_PATH = os.environ.get("WAFAN_Z3_PATH")
_Z3_AVAILABLE = Z3_PATH is not None and os.path.exists(Z3_PATH)

pytestmark = pytest.mark.skipif(
    not _Z3_AVAILABLE,
    reason="WAFAN_Z3_PATH not set or binary not found",
)


# ---------------------------------------------------------------------------
# Test-case descriptor
# ---------------------------------------------------------------------------

@dataclass
class E2ECase:
    """One self-contained e2e scenario.

    Rules are written inline as a ModSecurity conf string.  Expected results
    are declared as sets of rule-ID pairs so assertions read like the docs.

    Fields:
        name:          Short label used in pytest output.
        rules:         Inline ModSecurity SecRule configuration.
        intersecting:  Unordered pairs that must be SAT under intersection.
        disjoint:      Unordered pairs that must be UNSAT under intersection.
        subsumed:      Ordered (rule1_id, rule2_id) pairs where rule1 ⊆ rule2.
        not_subsumed:  Ordered pairs that must NOT be subsumed.
        has_witness:   Rule IDs that must have a satisfying witness.
        no_witness:    Rule IDs that must NOT have a witness (UNSAT or UNKNOWN).
    """
    name: str
    rules: str
    intersecting:  set[frozenset[str]]  = field(default_factory=set)
    disjoint:      set[frozenset[str]]  = field(default_factory=set)
    subsumed:      set[tuple[str, str]] = field(default_factory=set)
    not_subsumed:  set[tuple[str, str]] = field(default_factory=set)
    has_witness:   set[str]             = field(default_factory=set)
    no_witness:    set[str]             = field(default_factory=set)


def _fs(*ids: str) -> frozenset[str]:
    """Shorthand for an unordered rule-ID pair."""
    return frozenset(ids)


# ---------------------------------------------------------------------------
# Test cases  — add new scenarios here
# ---------------------------------------------------------------------------

CASES: list[E2ECase] = [

    # ------------------------------------------------------------------
    # Basic SQL keyword patterns: narrow ⊆ broad, some pairs disjoint
    # ------------------------------------------------------------------
    E2ECase(
        name="sql_keywords_basic",
        rules=textwrap.dedent("""\
            SecRule ARGS "@rx select" \
                "id:1100,phase:2,deny,msg:'SQL: select'"
            SecRule ARGS "@rx select|insert|delete" \
                "id:1200,phase:2,deny,msg:'SQL: select/insert/delete'"
            SecRule ARGS "@rx union" \
                "id:1300,phase:2,deny,msg:'SQL: union'"
            SecRule ARGS "@rx .+" \
                "id:1400,phase:2,deny,msg:'any non-empty ARGS'"
        """),
        intersecting={
            _fs("1100", "1200"),  # "select" matches both
            _fs("1100", "1400"),
            _fs("1200", "1400"),
            _fs("1300", "1400"),
        },
        disjoint={
            _fs("1100", "1300"),  # "select" ≠ "union" under full-match
            _fs("1200", "1300"),
        },
        subsumed={
            ("1100", "1200"),  # select ⊆ select|insert|delete
            ("1100", "1400"),
            ("1200", "1400"),
            ("1300", "1400"),
        },
        not_subsumed={
            ("1200", "1100"),  # "insert" triggers 1200 but not 1100
            ("1400", "1100"),
            ("1300", "1200"),
        },
        has_witness={"1100", "1200", "1300", "1400"},
    ),

    # ------------------------------------------------------------------
    # t:lowercase transform: same hierarchy but case-folded
    # ------------------------------------------------------------------
    E2ECase(
        name="lowercase_transform",
        rules=textwrap.dedent("""\
            SecRule ARGS "@rx admin" \
                "id:2100,phase:2,deny,t:lowercase,msg:'admin keyword'"
            SecRule ARGS "@rx admin|root" \
                "id:2200,phase:2,deny,t:lowercase,msg:'admin or root'"
            SecRule ARGS "@rx .+" \
                "id:2300,phase:2,deny,t:lowercase,msg:'any non-empty (after lower)'"
        """),
        intersecting={
            _fs("2100", "2200"),
            _fs("2100", "2300"),
            _fs("2200", "2300"),
        },
        subsumed={
            ("2100", "2200"),  # "admin" ⊆ "admin|root"
            ("2100", "2300"),
            ("2200", "2300"),
        },
        not_subsumed={
            ("2200", "2100"),  # "root" triggers 2200 but not 2100
            ("2300", "2100"),
            ("2300", "2200"),
        },
        has_witness={"2100", "2200", "2300"},
    ),

    # ------------------------------------------------------------------
    # Genuinely disjoint character classes (anchored patterns)
    # ------------------------------------------------------------------
    E2ECase(
        name="disjoint_character_classes",
        rules=textwrap.dedent("""\
            SecRule ARGS "@rx ^[0-9]+$" \
                "id:3100,phase:2,deny,msg:'digits only'"
            SecRule ARGS "@rx ^[a-z]+$" \
                "id:3200,phase:2,deny,msg:'lowercase letters only'"
            SecRule ARGS "@rx ^[A-Z]+$" \
                "id:3300,phase:2,deny,msg:'uppercase letters only'"
        """),
        disjoint={
            _fs("3100", "3200"),
            _fs("3100", "3300"),
            _fs("3200", "3300"),
        },
        has_witness={"3100", "3200", "3300"},
    ),

    # ------------------------------------------------------------------
    # Mixed variables: cross-variable pairs skipped, same-variable checked
    # ------------------------------------------------------------------
    E2ECase(
        name="mixed_variables",
        rules=textwrap.dedent("""\
            SecRule ARGS "@rx login" \
                "id:4100,phase:2,deny,msg:'login in ARGS'"
            SecRule REQUEST_URI "@rx login" \
                "id:4200,phase:2,deny,msg:'login in URI'"
            SecRule REQUEST_URI "@rx login|logout" \
                "id:4300,phase:2,deny,msg:'login/logout in URI'"
        """),
        intersecting={
            _fs("4200", "4300"),  # same variable, "login" matches both
        },
        subsumed={
            ("4200", "4300"),  # "login" ⊆ "login|logout"
        },
        has_witness={"4100", "4200", "4300"},
    ),

    # ------------------------------------------------------------------
    # Negated operators: !@rx patterns and their interactions
    # ------------------------------------------------------------------
    E2ECase(
        name="negated_operators",
        rules=textwrap.dedent("""\
            SecRule ARGS "!@rx safe" \
                "id:5100,phase:2,deny,msg:'anything except safe'"
            SecRule ARGS "!@rx safe|ok" \
                "id:5200,phase:2,deny,msg:'anything except safe or ok'"
            SecRule ARGS "@rx .+" \
                "id:5300,phase:2,deny,msg:'any non-empty ARGS'"
        """),
        intersecting={
            _fs("5100", "5200"),  # e.g. "" satisfies both negated rules
            _fs("5100", "5300"),
            _fs("5200", "5300"),
        },
        has_witness={"5100", "5200", "5300"},
    ),

    # ------------------------------------------------------------------
    # OS command injection: nested enumeration hierarchy
    # ------------------------------------------------------------------
    E2ECase(
        name="os_command_injection",
        rules=textwrap.dedent("""\
            SecRule ARGS "@rx ^(?:cat|ls|pwd|id)$" \
                "id:7100,phase:2,deny,msg:'basic recon commands'"
            SecRule ARGS "@rx ^(?:cat|ls|pwd|id|whoami|hostname|uname)$" \
                "id:7200,phase:2,deny,msg:'extended recon commands'"
            SecRule ARGS "@rx ^(?:cat|ls|pwd|id|whoami|hostname|uname|rm|mv|cp|chmod|chown)$" \
                "id:7300,phase:2,deny,msg:'all suspicious commands'"
            SecRule ARGS "@rx ^(?:cat|ls|pwd|id|whoami|hostname|uname|rm|mv|cp|chmod|chown)(?:\\s+-\\w+)*$" \
                "id:7400,phase:2,deny,msg:'commands with optional flags'"
            SecRule ARGS "@rx ^[a-z][a-z0-9_-]{1,15}$" \
                "id:7500,phase:2,deny,msg:'short lowercase identifier'"
        """),
        intersecting={
            _fs("7100", "7200"),  # "cat" matches both
            _fs("7100", "7300"),
            _fs("7200", "7300"),
            _fs("7300", "7400"),
            _fs("7100", "7400"),
            _fs("7300", "7500"),
        },
        has_witness={"7100", "7200", "7300", "7400", "7500"},
    ),

    # ------------------------------------------------------------------
    # Sensitive file-path disclosure (REQUEST_URI)
    # ------------------------------------------------------------------
    E2ECase(
        name="sensitive_file_paths",
        rules=textwrap.dedent("""\
            SecRule REQUEST_URI "@rx ^/etc/passwd$" \
                "id:7600,phase:1,deny,msg:'/etc/passwd'"
            SecRule REQUEST_URI "@rx ^/etc/shadow$" \
                "id:7610,phase:1,deny,msg:'/etc/shadow'"
            SecRule REQUEST_URI "@rx ^/etc/(?:passwd|shadow|hosts|sudoers|group|crontab)$" \
                "id:7700,phase:1,deny,msg:'sensitive /etc/ file'"
            SecRule REQUEST_URI "@rx ^/etc/[a-z][a-z0-9_./-]*$" \
                "id:7800,phase:1,deny,msg:'any /etc/ path'"
            SecRule REQUEST_URI "@rx ^/(?:etc|proc|sys|var)/.*$" \
                "id:7900,phase:1,deny,msg:'sensitive system directory'"
            SecRule REQUEST_URI "@rx ^/proc/self/environ$" \
                "id:7950,phase:1,deny,msg:'/proc/self/environ'"
        """),
        intersecting={
            _fs("7600", "7700"),  # /etc/passwd matches both
            _fs("7610", "7700"),
            _fs("7600", "7800"),
            _fs("7700", "7800"),
            _fs("7700", "7900"),
            _fs("7800", "7900"),
        },
        disjoint={
            _fs("7600", "7610"),  # /etc/passwd ≠ /etc/shadow under full-match
            _fs("7600", "7950"),  # /etc/passwd ∉ /proc/… family
        },
        has_witness={"7600", "7610", "7700", "7800", "7900", "7950"},
    ),

    # ------------------------------------------------------------------
    # Hex and numeric encoding detection
    # ------------------------------------------------------------------
    E2ECase(
        name="hex_numeric_encoding",
        rules=textwrap.dedent("""\
            SecRule ARGS "@rx ^[0-9]+$" \
                "id:8000,phase:2,deny,msg:'decimal integer'"
            SecRule ARGS "@rx ^[0-9a-f]+$" \
                "id:8100,phase:2,deny,msg:'lowercase hex'"
            SecRule ARGS "@rx ^[0-9a-fA-F]+$" \
                "id:8200,phase:2,deny,msg:'any-case hex'"
            SecRule ARGS "@rx ^0x[0-9a-fA-F]+$" \
                "id:8300,phase:2,deny,msg:'0x-prefixed hex'"
            SecRule ARGS "@rx ^[0-9a-fA-F]{2,}$" \
                "id:8400,phase:2,deny,msg:'multi-byte hex (>=2 chars)'"
        """),
        intersecting={
            _fs("8000", "8100"),  # "9" matches both
            _fs("8000", "8200"),
            _fs("8100", "8200"),
            _fs("8200", "8400"),  # "ff" matches both
        },
        disjoint={
            _fs("8000", "8300"),  # decimal ∩ 0x-prefix = ∅
            _fs("8100", "8300"),
            _fs("8200", "8300"),
            _fs("8400", "8300"),
        },
        has_witness={"8000", "8100", "8200", "8300", "8400"},
    ),

    # ------------------------------------------------------------------
    # htmlEntityDecode: uninterpreted transform → solver returns UNKNOWN
    # ------------------------------------------------------------------
    E2ECase(
        name="html_entity_decode",
        rules=textwrap.dedent("""\
            SecRule ARGS "@rx <script" \
                "id:700,phase:2,deny,t:htmlEntityDecode,msg:'script tag after decoding'"
            SecRule ARGS "@rx <script" \
                "id:701,phase:2,deny,msg:'script tag literal'"
        """),
        # Rule 701 (no transform) has a concrete witness; rule 700 is UNKNOWN
        has_witness={"701"},
        no_witness={"700"},
        # htmlEntityDecode is uninterpreted → subsumption check returns UNKNOWN
        not_subsumed={("701", "700"), ("700", "701")},
    ),

]


# ---------------------------------------------------------------------------
# Solver fixture and result cache
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def solver() -> SubprocessSolver:
    return SubprocessSolver(argv=[Z3_PATH, "-in"], timeout=30)


def _parse_inline(conf_text: str):
    tmp = Path("/tmp/_wafan_e2e_case.conf")
    tmp.write_text(conf_text)
    return parse_rx_rules(tmp)


# Module-level cache so the solver runs once per case across all test functions.
_cache: dict[str, dict] = {}


def _results(case: E2ECase, solver: SubprocessSolver) -> dict:
    if case.name not in _cache:
        rules = _parse_inline(case.rules)
        _cache[case.name] = {
            "intersection": IntersectionChecker(solver).find_intersecting_chains(rules),
            "subsumption":  SubsumptionChecker(solver).find_subsumed_chains(rules),
            "witness":      WitnessChecker(solver).find_chain_witnesses(rules),
        }
    return _cache[case.name]


# ---------------------------------------------------------------------------
# Parametrized tests — one function per analysis aspect
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("case", [c for c in CASES if c.intersecting], ids=[c.name for c in CASES if c.intersecting])
def test_intersecting_pairs(case, solver):
    actual = {
        frozenset([r.chain1[0].rule_id, r.chain2[0].rule_id])
        for r in _results(case, solver)["intersection"]
        if r.has_intersection
    }
    for pair in case.intersecting:
        assert pair in actual, f"[{case.name}] expected intersecting pair {set(pair)} not found"


@pytest.mark.parametrize("case", [c for c in CASES if c.disjoint], ids=[c.name for c in CASES if c.disjoint])
def test_disjoint_pairs(case, solver):
    actual_intersecting = {
        frozenset([r.chain1[0].rule_id, r.chain2[0].rule_id])
        for r in _results(case, solver)["intersection"]
        if r.has_intersection
    }
    for pair in case.disjoint:
        assert pair not in actual_intersecting, f"[{case.name}] pair {set(pair)} should be disjoint but found intersecting"


@pytest.mark.parametrize("case", [c for c in CASES if c.subsumed], ids=[c.name for c in CASES if c.subsumed])
def test_subsumed_pairs(case, solver):
    actual = {
        (r.chain1[0].rule_id, r.chain2[0].rule_id)
        for r in _results(case, solver)["subsumption"]
        if r.is_subsumed
    }
    for pair in case.subsumed:
        assert pair in actual, f"[{case.name}] expected {pair[0]} ⊆ {pair[1]} but not found"


@pytest.mark.parametrize("case", [c for c in CASES if c.not_subsumed], ids=[c.name for c in CASES if c.not_subsumed])
def test_not_subsumed_pairs(case, solver):
    actual = {
        (r.chain1[0].rule_id, r.chain2[0].rule_id)
        for r in _results(case, solver)["subsumption"]
        if r.is_subsumed
    }
    for pair in case.not_subsumed:
        assert pair not in actual, f"[{case.name}] pair {pair[0]} ⊆ {pair[1]} should not be subsumed"


@pytest.mark.parametrize("case", [c for c in CASES if c.has_witness], ids=[c.name for c in CASES if c.has_witness])
def test_rules_with_witness(case, solver):
    actual = {r.chain[0].rule_id for r in _results(case, solver)["witness"] if r.has_witness}
    for rule_id in case.has_witness:
        assert rule_id in actual, f"[{case.name}] expected a witness for rule {rule_id}"


@pytest.mark.parametrize("case", [c for c in CASES if c.no_witness], ids=[c.name for c in CASES if c.no_witness])
def test_rules_without_witness(case, solver):
    actual_with_witness = {r.chain[0].rule_id for r in _results(case, solver)["witness"] if r.has_witness}
    for rule_id in case.no_witness:
        assert rule_id not in actual_with_witness, f"[{case.name}] rule {rule_id} should not have a witness"
