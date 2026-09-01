"""End-to-end tests for the order-aware analyses (reachability + stateful pairs).

Each ReachCase bundles an inline ruleset with the expected verdict for every
rule id, so adding a scenario means appending one case.

Requires a z3 build with re.from_ecma2020 support; set WAFAN_Z3_PATH.
"""

from __future__ import annotations

import os
import textwrap
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from wafan.analyses import SubprocessSolver
from wafan.analyses.reachability import (
    IMPOSSIBLE_MATCH,
    OK,
    UNREACHABLE,
    ReachabilityChecker,
)
from wafan.analyses.stateful import (
    INTERSECTION,
    SHADOWING,
    SUBSUMPTION,
    StatefulPairChecker,
)
from wafan.state import encode_ruleset

Z3_PATH = os.environ.get("WAFAN_Z3_PATH")
_Z3_AVAILABLE = Z3_PATH is not None and os.path.exists(Z3_PATH)

pytestmark = pytest.mark.skipif(
    not _Z3_AVAILABLE,
    reason="WAFAN_Z3_PATH not set or binary not found",
)


def make_solver() -> SubprocessSolver:
    return SubprocessSolver(argv=[Z3_PATH, "-in"], timeout=30)


def write(tmp_path: Path, text: str, name: str = "rules.conf") -> Path:
    path = tmp_path / name
    path.write_text(textwrap.dedent(text).lstrip())
    return path


# ---------------------------------------------------------------------------
# Reachability
# ---------------------------------------------------------------------------

@dataclass
class ReachCase:
    name: str
    rules: str
    expected: dict[str, str] = field(default_factory=dict)


CASES = [
    ReachCase(
        name="tx_guard_never_set",
        rules="""
            SecRule &TX:never_set "@eq 0"  "id:100,phase:1,pass,nolog"
            SecRule &TX:never_set "!@eq 0" "id:101,phase:1,pass,nolog"
        """,
        # Nothing writes tx.never_set, so its count is 0: the "@eq 0" arm is a
        # tautology and its negation is dead code.
        expected={"100": OK, "101": IMPOSSIBLE_MATCH},
    ),
    ReachCase(
        name="tx_guard_is_set_by_secaction",
        rules="""
            SecAction "id:199,phase:1,pass,nolog,setvar:tx.flag=1"
            SecRule &TX:flag "@eq 0"  "id:200,phase:1,pass,nolog"
            SecRule &TX:flag "!@eq 0" "id:201,phase:1,pass,nolog"
        """,
        # …and the verdicts invert once an initialiser is present.
        expected={"200": IMPOSSIBLE_MATCH, "201": OK},
    ),
    ReachCase(
        name="value_threshold",
        rules="""
            SecAction "id:299,phase:1,pass,nolog,setvar:tx.level=1"
            SecRule TX:level "@ge 1" "id:300,phase:1,pass,nolog"
            SecRule TX:level "@ge 5" "id:301,phase:1,pass,nolog"
        """,
        expected={"300": OK, "301": IMPOSSIBLE_MATCH},
    ),
    ReachCase(
        name="skip_after_jumps_over_rules",
        rules="""
            SecAction "id:399,phase:2,pass,nolog,skipAfter:END"
            SecRule ARGS "@streq skipped" "id:400,phase:2,pass,nolog"
            SecMarker "END"
            SecRule ARGS "@streq reached" "id:401,phase:2,pass,nolog"
        """,
        expected={"400": UNREACHABLE, "401": OK},
    ),
    ReachCase(
        name="conditional_skip_leaves_target_reachable",
        rules="""
            SecRule ARGS "@streq trigger" "id:499,phase:2,pass,nolog,skipAfter:END2"
            SecRule ARGS "@streq other" "id:500,phase:2,pass,nolog"
            SecMarker "END2"
        """,
        # The skip only fires for ARGS="trigger", so 500 is still reachable
        # via any other request.
        expected={"499": OK, "500": OK},
    ),
    ReachCase(
        name="accumulated_score_reaches_threshold",
        rules="""
            SecRule ARGS "@streq attack" "id:599,phase:2,pass,nolog,setvar:tx.score=+5"
            SecRule TX:score "@ge 5"  "id:600,phase:2,pass,nolog"
            SecRule TX:score "@ge 50" "id:601,phase:2,pass,nolog"
        """,
        expected={"599": OK, "600": OK, "601": IMPOSSIBLE_MATCH},
    ),
    ReachCase(
        name="terminating_rule_cuts_off_successors",
        rules="""
            SecRule &TX:absent "@eq 0" "id:699,phase:1,deny,status:500"
            SecRule ARGS "@streq anything" "id:700,phase:2,pass,nolog"
        """,
        # 699's guard is a tautology and it denies, so phase 2 never runs.
        expected={"699": OK, "700": UNREACHABLE},
    ),
    ReachCase(
        name="pass_rule_does_not_cut_off_successors",
        rules="""
            SecRule &TX:absent "@eq 0" "id:799,phase:1,pass,nolog"
            SecRule ARGS "@streq anything" "id:800,phase:2,pass,nolog"
        """,
        expected={"799": OK, "800": OK},
    ),
    ReachCase(
        name="ctl_rule_remove_by_id_kills_target",
        rules="""
            SecAction "id:899,phase:2,pass,nolog,ctl:ruleRemoveById=900"
            SecRule ARGS "@streq x" "id:900,phase:2,pass,nolog"
            SecRule ARGS "@streq y" "id:901,phase:2,pass,nolog"
        """,
        expected={"900": UNREACHABLE, "901": OK},
    ),
    ReachCase(
        name="macro_threshold_resolves",
        rules="""
            SecAction "id:999,phase:1,pass,nolog,setvar:tx.threshold=5"
            SecAction "id:1000,phase:1,pass,nolog,setvar:tx.score=3"
            SecRule TX:score "@ge %{tx.threshold}" "id:1001,phase:1,pass,nolog"
            SecRule TX:score "@lt %{tx.threshold}" "id:1002,phase:1,pass,nolog"
        """,
        # score=3, threshold=5 — both fixed, so one arm is dead.
        expected={"1001": IMPOSSIBLE_MATCH, "1002": OK},
    ),
    ReachCase(
        name="phase_order_beats_file_order",
        rules="""
            SecRule TX:early "@eq 1" "id:1100,phase:2,pass,nolog"
            SecAction "id:1101,phase:1,pass,nolog,setvar:tx.early=1"
        """,
        # 1101 appears later in the file but runs first (phase 1), so 1100's
        # read sees the written value.
        expected={"1100": OK},
    ),
    ReachCase(
        name="persistent_collection_guard_stays_live",
        rules="""
            SecRule &IP:blocked "!@eq 0" "id:1150,phase:2,pass,nolog"
            SecRule &TX:blocked "!@eq 0" "id:1151,phase:2,pass,nolog"
        """,
        # IP persists across requests, so an earlier transaction may have set
        # it; TX is fresh every request, so its guard is dead.
        expected={"1150": OK, "1151": IMPOSSIBLE_MATCH},
    ),
    ReachCase(
        name="chain_links_may_match_different_members",
        rules="""
            SecRule ARGS "@streq a" "id:1300,phase:2,pass,nolog,chain"
                SecRule ARGS "@streq b"
        """,
        # ARGS is multi-valued: ?x=a&y=b satisfies the two links with two
        # different members. Modelling the collection by a single value made
        # this look dead.
        expected={"1300": OK},
    ),
    ReachCase(
        name="scalar_target_cannot_hold_two_values",
        rules="""
            SecRule REQUEST_METHOD "@streq GET" "id:1310,phase:2,pass,nolog,chain"
                SecRule REQUEST_METHOD "@streq POST"
        """,
        # ...but a scalar really does have one value, so this stays dead.
        expected={"1310": IMPOSSIBLE_MATCH},
    ),
    ReachCase(
        name="large_cardinality_bound_stays_satisfiable",
        rules="""
            SecRule &ARGS "@gt 200" "id:1320,phase:2,pass,nolog"
        """,
        # The count is a free Int, so a big bound costs no unrolling.
        expected={"1320": OK},
    ),
    ReachCase(
        name="scalar_cardinality_is_not_closed_against_another_target",
        rules="""
            SecRule ARGS "@streq a" "id:1330,phase:2,pass,nolog,chain"
                SecRule ARGS "@streq b"
            SecRule &REQUEST_FILENAME "@eq 2" "id:1331,phase:2,pass,nolog"
        """,
        # The ARGS chain needs two slots. With a single global bound that also
        # "closed" REQUEST_FILENAME at 2, contradicting its one slot and making
        # 1331 falsely dead. Bounds are per target, so it stays live.
        expected={"1330": OK, "1331": OK},
    ),
    ReachCase(
        name="modest_cardinality_demand_is_representable",
        rules="""
            SecRule &ARGS "@eq 3" "id:1340,phase:2,pass,nolog"
        """,
        expected={"1340": OK},
    ),
    ReachCase(
        name="unsupported_operator_stays_reachable",
        rules="""
            SecRule ARGS "@detectSQLi" "id:1200,phase:2,pass,nolog"
        """,
        # Abstracted to a free Boolean: over-approximated, so never reported dead.
        expected={"1200": OK},
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_reachability_verdicts(tmp_path, case):
    conf = write(tmp_path, case.rules)
    encoding = encode_ruleset(conf)
    results = ReachabilityChecker(make_solver()).find_dead(
        encoding, include_actions=True
    )
    got = {r.rule_id: r.verdict for r in results}
    for rule_id, expected in case.expected.items():
        assert rule_id in got, f"rule {rule_id} not checked"
        assert got[rule_id] == expected, (
            f"rule {rule_id}: expected {expected}, got {got[rule_id]}"
        )


def test_include_order_changes_verdicts(tmp_path):
    """Loading an initialiser file first is what makes TX state correct."""
    setup = write(tmp_path, """
        SecAction "id:1,phase:1,pass,nolog,setvar:tx.configured=1"
    """, "setup.conf")
    rules = write(tmp_path, """
        SecRule &TX:configured "@eq 0" "id:2,phase:1,pass,nolog"
    """, "rules.conf")

    alone = ReachabilityChecker(make_solver()).find_dead(encode_ruleset(rules))
    assert alone[0].verdict == OK  # nothing sets it -> the guard always holds

    both = ReachabilityChecker(make_solver()).find_dead(encode_ruleset([setup, rules]))
    verdicts = {r.rule_id: r.verdict for r in both}
    assert verdicts["2"] == IMPOSSIBLE_MATCH


def test_dead_rules_are_reported_as_dead(tmp_path):
    conf = write(tmp_path, """
        SecRule &TX:absent "!@eq 0" "id:1,phase:1,pass,nolog"
        SecRule ARGS "@streq a" "id:2,phase:2,pass,nolog"
    """)
    results = ReachabilityChecker(make_solver()).find_dead(encode_ruleset(conf))
    dead = {r.rule_id for r in results if r.is_dead}
    assert dead == {"1"}


def test_sec_actions_skipped_by_default(tmp_path):
    conf = write(tmp_path, """
        SecAction "id:1,phase:1,pass,nolog,setvar:tx.a=1"
        SecRule ARGS "@streq a" "id:2,phase:2,pass,nolog"
    """)
    encoding = encode_ruleset(conf)
    checker = ReachabilityChecker(make_solver())
    assert {r.rule_id for r in checker.find_dead(encoding)} == {"2"}
    assert {r.rule_id for r in checker.find_dead(encoding, include_actions=True)} == {"1", "2"}


# ---------------------------------------------------------------------------
# Stateful pairwise analyses
# ---------------------------------------------------------------------------

STATE_GUARDED_PAIR = """
    SecRule ARGS "@streq payload" "id:10,phase:2,pass,nolog,skipAfter:PAST"
    SecAction "id:11,phase:2,pass,nolog,setvar:tx.flag=1"
    SecMarker "PAST"
    SecRule ARGS "@streq payload" "id:20,phase:2,pass,nolog"
    SecRule ARGS "@streq payload" "id:21,phase:2,pass,nolog,chain"
        SecRule TX:flag "@eq 1"
"""


def _pairs(conf, mode):
    encoding = encode_ruleset(conf)
    results = StatefulPairChecker(make_solver(), mode).find_pairs(encoding)
    return {r.rule_ids: r for r in results}


def test_stateful_intersection_rules_out_state_impossible_pairs(tmp_path):
    """Identical patterns are not an overlap when state makes them exclusive.

    Rule 10 fires on ARGS="payload" and skips past the setter, so tx.flag is
    never set on that path — 21's chain can never complete. The stateless
    analysis reports all three pairs as intersecting.
    """
    conf = write(tmp_path, STATE_GUARDED_PAIR)
    pairs = _pairs(conf, INTERSECTION)
    assert pairs[("10", "20")].holds is True
    assert pairs[("10", "21")].holds is False
    assert pairs[("20", "21")].holds is False


def test_stateful_subsumption_uses_firing_not_matching(tmp_path):
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,pass,nolog"
        SecRule ARGS "@rx ^a$" "id:2,phase:2,pass,nolog"
    """)
    pairs = _pairs(conf, SUBSUMPTION)
    assert pairs[("1", "2")].holds is True
    assert pairs[("2", "1")].holds is True


def test_stateful_subsumption_false_when_guard_differs(tmp_path):
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,pass,nolog"
        SecRule ARGS "@streq a" "id:2,phase:2,pass,nolog,chain"
            SecRule &TX:absent "!@eq 0"
    """)
    # 2 can never fire, so 1 ⊆ 2 must be false while 2 ⊆ 1 holds vacuously.
    pairs = _pairs(conf, SUBSUMPTION)
    assert pairs[("1", "2")].holds is False
    assert pairs[("2", "1")].holds is True


def test_disruptive_rules_can_never_both_fire(tmp_path):
    """The reason stateful "contradiction" has to be shadowing instead.

    `allow` terminates the transaction, so a later rule never executes:
    `fire_A ∧ fire_B` is unsatisfiable for any two disruptive rules, however
    much their patterns overlap.
    """
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,allow"
        SecRule ARGS "@streq a" "id:2,phase:2,deny"
    """)
    pairs = _pairs(conf, INTERSECTION)
    assert pairs[("1", "2")].result.value == "unsat"


def test_shadowing_finds_order_decided_conflict(tmp_path):
    """An earlier `allow` pre-empts a later `deny` that would also have matched."""
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,allow"
        SecRule ARGS "@streq a" "id:2,phase:2,deny"
    """)
    pairs = _pairs(conf, SHADOWING)
    result = pairs[("1", "2")]
    assert result.result.value == "sat"
    assert result.dispositions == ("allow", "deny")
    assert result.holds is True
    assert result.outcome == "shadowing"


def test_shadowing_requires_a_disposition_conflict(tmp_path):
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,allow"
        SecRule ARGS "@streq a" "id:2,phase:2,pass,nolog"
    """)
    pairs = _pairs(conf, SHADOWING)
    result = pairs[("1", "2")]
    # `pass` is not an explicit accept-or-deny, so overlap is not a conflict.
    assert result.result.value == "sat"
    assert result.holds is False
    assert result.outcome == "overlap_no_conflict"


def test_shadowing_is_directional(tmp_path):
    """Only an earlier rule can shadow a later one, so only p<q is queried."""
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,allow"
        SecRule ARGS "@streq a" "id:2,phase:2,deny"
    """)
    pairs = _pairs(conf, SHADOWING)
    assert ("1", "2") in pairs
    assert ("2", "1") not in pairs


def test_shadowing_absent_when_patterns_are_disjoint(tmp_path):
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,allow"
        SecRule ARGS "@streq b" "id:2,phase:2,deny"
    """)
    pairs = _pairs(conf, SHADOWING)
    assert pairs[("1", "2")].result.value == "unsat"
    assert pairs[("1", "2")].holds is False


def test_approximate_flag_set_when_a_side_is_abstracted(tmp_path):
    conf = write(tmp_path, """
        SecRule ARGS "@detectSQLi" "id:1,phase:2,pass,nolog"
        SecRule ARGS "@streq a" "id:2,phase:2,pass,nolog"
    """)
    pairs = _pairs(conf, INTERSECTION)
    result = pairs[("1", "2")]
    assert result.approximate is True
    assert any("#1" in r for r in result.approximate_reasons)


def test_member_bound_is_visible_on_the_encoding(tmp_path):
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,pass,nolog,chain"
            SecRule ARGS "@streq b"
    """)
    encoding = encode_ruleset(conf)
    assert encoding.members == 2
    assert encoding.closed is True


def test_pairwise_encoding_doubles_the_bound(tmp_path):
    """Two rules' conditions are asserted at once, so both need witnesses."""
    conf = write(tmp_path, """
        SecRule ARGS "@streq a" "id:1,phase:2,pass,nolog"
        SecRule ARGS "@streq b" "id:2,phase:2,pass,nolog"
    """)
    single = encode_ruleset(conf)
    both = encode_ruleset(conf, pairwise=True)
    assert (single.members, both.members) == (1, 2)
    # With one member the two rules look mutually exclusive; with two they
    # can both fire on ?x=a&y=b.
    def holds(enc):
        pairs = StatefulPairChecker(make_solver(), INTERSECTION).find_pairs(enc)
        return {r.rule_ids: r.holds for r in pairs}
    assert holds(single)[("1", "2")] is False
    assert holds(both)[("1", "2")] is True


def test_selector_is_a_subset_of_its_collection(tmp_path):
    """ARGS:id's members ARE ARGS members, so these cannot both fire."""
    conf = write(tmp_path, """
        SecRule ARGS:id "@streq 42" "id:1,phase:2,pass,nolog"
        SecRule &ARGS   "@eq 0"     "id:2,phase:2,pass,nolog"
    """)
    pairs = _pairs(conf, INTERSECTION)
    assert pairs[("1", "2")].holds is False


def test_names_view_shares_the_base_collection(tmp_path):
    """A parameter named "x" means ARGS is non-empty."""
    conf = write(tmp_path, """
        SecRule ARGS_NAMES "@streq x" "id:1,phase:2,pass,nolog"
        SecRule &ARGS      "@eq 0"    "id:2,phase:2,pass,nolog"
    """)
    pairs = _pairs(conf, INTERSECTION)
    assert pairs[("1", "2")].holds is False


def test_exclusion_removes_the_only_candidate_member(tmp_path):
    """With exactly one cookie, the exclusion and the name test conflict.

    Rule 1 requires a cookie *not* named "s" to hold "v", while its second
    link requires a cookie named "s" -- satisfiable in general with two
    members, but `&REQUEST_COOKIES "@eq 1"` forces them to be the same one.
    Rule 2 drops the exclusion and stays live, showing the exclusion is what
    kills rule 1 rather than the cardinality alone.
    """
    conf = write(tmp_path, """
        SecRule REQUEST_COOKIES|!REQUEST_COOKIES:s "@streq v" "id:1,phase:2,pass,nolog,chain"
            SecRule &REQUEST_COOKIES "@eq 1" "chain"
            SecRule REQUEST_COOKIES_NAMES "@streq s"
        SecRule REQUEST_COOKIES "@streq v" "id:2,phase:2,pass,nolog,chain"
            SecRule &REQUEST_COOKIES "@eq 1" "chain"
            SecRule REQUEST_COOKIES_NAMES "@streq s"
    """)
    results = ReachabilityChecker(make_solver()).find_dead(encode_ruleset(conf))
    verdicts = {r.rule_id: r.verdict for r in results}
    assert verdicts["1"] == IMPOSSIBLE_MATCH
    assert verdicts["2"] == OK


def test_unknown_mode_rejected():
    with pytest.raises(ValueError):
        StatefulPairChecker(make_solver(), "nonsense")
