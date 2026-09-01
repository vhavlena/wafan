"""Tests for the ordered, control-flow-aware ruleset view (wafan.ruleset).

These are solver-free: they check that ModSecurity's execution model is read
out of a conf file correctly — directive kinds, phase ordering, setvar
decoding, and the skip/removal/termination relations that wafan.state turns
into reachability conditions.
"""

from __future__ import annotations

import textwrap

import pytest

from wafan.ruleset import (
    Ruleset,
    execution_order,
    parse_directives,
    parse_setvar,
)


def write_conf(tmp_path, text: str, name: str = "rules.conf"):
    path = tmp_path / name
    path.write_text(textwrap.dedent(text).lstrip())
    return path


def by_id(directives, rule_id):
    for d in directives:
        if d.kind != "marker" and d.rule_id == rule_id:
            return d
    raise AssertionError(f"no directive with id {rule_id}")


# ---------------------------------------------------------------------------
# setvar decoding
# ---------------------------------------------------------------------------

class TestParseSetvar:
    @pytest.mark.parametrize("spec,expected", [
        ("tx.foo=5", ("tx", "foo", "set", "5")),
        ("tx.foo=+5", ("tx", "foo", "inc", "5")),
        ("tx.foo=-3", ("tx", "foo", "dec", "3")),
        ("tx.foo=+%{tx.bar}", ("tx", "foo", "inc", "%{tx.bar}")),
        ("tx.foo", ("tx", "foo", "set", "1")),
        ("!tx.foo", ("tx", "foo", "unset", "")),
        ("ip.count=+1", ("ip", "count", "inc", "1")),
        ("'tx.foo=+1'", ("tx", "foo", "inc", "1")),
    ])
    def test_forms(self, spec, expected):
        op = parse_setvar(spec)
        assert (op.collection, op.name, op.op, op.rhs) == expected

    def test_name_is_lowercased(self):
        # CRS writes tx.paranoia_level but reads %{TX.PARANOIA_LEVEL}.
        assert parse_setvar("TX.Paranoia_Level=1").name == "paranoia_level"

    def test_unparseable_returns_none(self):
        assert parse_setvar("no_dot_here") is None


class TestSetvarOnDirective:
    def test_quoted_and_unquoted_increments_agree(self, tmp_path):
        """msc_pyparser splits an unquoted `setvar:a=b` across two fields.

        Regression test: before the two halves were rejoined, an unquoted
        increment silently decayed into "set to 1".
        """
        conf = write_conf(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.a=+5"
            SecAction "id:2,phase:1,pass,setvar:'tx.b=+5'"
        """)
        directives = parse_directives(conf)
        for rule_id, name in (("1", "a"), ("2", "b")):
            ops = by_id(directives, rule_id).setvars
            assert len(ops) == 1
            assert (ops[0].name, ops[0].op, ops[0].rhs) == (name, "inc", "5")


# ---------------------------------------------------------------------------
# Directive parsing
# ---------------------------------------------------------------------------

class TestParseDirectives:
    def test_kinds_and_order(self, tmp_path):
        conf = write_conf(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass"
            SecAction "id:2,phase:2,pass,setvar:tx.x=1"
            SecMarker "HERE"
        """)
        directives = parse_directives(conf)
        assert [d.kind for d in directives] == ["rule", "action", "marker"]
        assert directives[2].marker == "HERE"

    def test_chain_is_one_directive(self, tmp_path):
        conf = write_conf(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,chain"
                SecRule REQUEST_METHOD "@streq POST"
            SecRule ARGS "@streq b" "id:2,phase:2,pass"
        """)
        directives = parse_directives(conf)
        assert len(directives) == 2
        assert len(directives[0].chain) == 2
        assert directives[0].rule_id == "1"

    def test_chain_actions_visible_on_directive(self, tmp_path):
        """A chain's actions live on its first link; the Directive exposes them."""
        conf = write_conf(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,setvar:tx.hit=1,chain"
                SecRule REQUEST_METHOD "@streq POST"
        """)
        d = parse_directives(conf)[0]
        assert [op.name for op in d.setvars] == ["hit"]

    def test_multiple_files_concatenate_in_order(self, tmp_path):
        a = write_conf(tmp_path, 'SecAction "id:1,phase:1,pass"\n', "a.conf")
        b = write_conf(tmp_path, 'SecAction "id:2,phase:1,pass"\n', "b.conf")
        assert [d.rule_id for d in parse_directives([a, b])] == ["1", "2"]
        assert [d.rule_id for d in parse_directives([b, a])] == ["2", "1"]

    def test_ctl_rule_remove_by_id(self, tmp_path):
        conf = write_conf(tmp_path, """
            SecAction "id:1,phase:2,pass,ctl:ruleRemoveById=942100"
            SecAction "id:2,phase:2,pass,ctl:ruleRemoveById=100-102"
        """)
        directives = parse_directives(conf)
        assert by_id(directives, "1").removes_rule_ids == ["942100"]
        assert by_id(directives, "2").removes_rule_ids == ["100", "101", "102"]

    def test_ctl_rule_remove_target_flagged(self, tmp_path):
        conf = write_conf(tmp_path, """
            SecAction "id:1,phase:2,pass,ctl:ruleRemoveTargetById=942100;ARGS:x"
        """)
        assert parse_directives(conf)[0].removes_targets is True


# ---------------------------------------------------------------------------
# Termination
# ---------------------------------------------------------------------------

class TestTerminates:
    @pytest.mark.parametrize("action,expected", [
        ("deny", True),
        ("drop", True),
        ("allow", True),
        ("pass", False),
        ("block", False),   # defers to SecDefaultAction, which defaults to pass
    ])
    def test_own_actions(self, tmp_path, action, expected):
        conf = write_conf(tmp_path, f"""
            SecRule ARGS "@streq a" "id:1,phase:2,{action}"
        """)
        assert parse_directives(conf)[0].terminates is expected

    def test_block_follows_default_action(self, tmp_path):
        conf = write_conf(tmp_path, """
            SecDefaultAction "phase:2,log,deny"
            SecRule ARGS "@streq a" "id:1,phase:2,block"
        """)
        assert parse_directives(conf)[0].terminates is True

    def test_no_disruptive_action_does_not_terminate(self, tmp_path):
        """ModSecurity's built-in default is `pass`, so silence means no."""
        conf = write_conf(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,log"
        """)
        assert parse_directives(conf)[0].terminates is False


# ---------------------------------------------------------------------------
# Execution order
# ---------------------------------------------------------------------------

class TestExecutionOrder:
    def test_phases_run_in_order_not_file_order(self, tmp_path):
        conf = write_conf(tmp_path, """
            SecRule ARGS "@streq a" "id:20,phase:2,pass"
            SecRule ARGS "@streq b" "id:10,phase:1,pass"
            SecRule ARGS "@streq c" "id:21,phase:2,pass"
        """)
        order = execution_order(parse_directives(conf))
        assert [d.rule_id for d in order] == ["10", "20", "21"]

    def test_marker_appears_in_every_phase(self, tmp_path):
        """SecMarker has no phase: a phase-2 skipAfter must be able to reach a
        marker written between phase-1 rules."""
        conf = write_conf(tmp_path, """
            SecRule ARGS "@streq a" "id:10,phase:1,pass"
            SecMarker "M"
            SecRule ARGS "@streq b" "id:20,phase:2,pass"
        """)
        order = execution_order(parse_directives(conf))
        markers = [i for i, d in enumerate(order) if d.kind == "marker"]
        assert len(markers) == len(("1", "2", "3", "4", "5"))

    def test_default_phase_is_2(self, tmp_path):
        conf = write_conf(tmp_path, 'SecRule ARGS "@streq a" "id:1,pass"\n')
        assert parse_directives(conf)[0].phase == "2"


# ---------------------------------------------------------------------------
# Control flow resolution
# ---------------------------------------------------------------------------

class TestControlFlow:
    def _cf(self, tmp_path, text):
        rs = Ruleset.from_paths(write_conf(tmp_path, text))
        return rs, rs.control_flow

    def test_skip_after_covers_range_up_to_marker(self, tmp_path):
        rs, cf = self._cf(tmp_path, """
            SecAction "id:1,phase:2,pass,skipAfter:M"
            SecRule ARGS "@streq a" "id:2,phase:2,pass"
            SecRule ARGS "@streq b" "id:3,phase:2,pass"
            SecMarker "M"
            SecRule ARGS "@streq c" "id:4,phase:2,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["2"]] == [pos["1"]]
        assert cf.blocked_by[pos["3"]] == [pos["1"]]
        assert cf.blocked_by[pos["4"]] == []   # past the marker

    def test_skip_after_unknown_marker_covers_nothing(self, tmp_path):
        rs, cf = self._cf(tmp_path, """
            SecAction "id:1,phase:2,pass,skipAfter:NOPE"
            SecRule ARGS "@streq a" "id:2,phase:2,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["2"]] == []
        assert rs.unresolved_markers() == ["NOPE"]

    def test_skip_n_covers_next_n_rules(self, tmp_path):
        rs, cf = self._cf(tmp_path, """
            SecAction "id:1,phase:2,pass,skip:2"
            SecRule ARGS "@streq a" "id:2,phase:2,pass"
            SecRule ARGS "@streq b" "id:3,phase:2,pass"
            SecRule ARGS "@streq c" "id:4,phase:2,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["2"]] == [pos["1"]]
        assert cf.blocked_by[pos["3"]] == [pos["1"]]
        assert cf.blocked_by[pos["4"]] == []

    def test_ctl_remove_by_id_crosses_phases(self, tmp_path):
        """Unlike a skip, a removal holds for the rest of the transaction."""
        rs, cf = self._cf(tmp_path, """
            SecAction "id:1,phase:1,pass,ctl:ruleRemoveById=900"
            SecRule ARGS "@streq a" "id:900,phase:2,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["900"]] == [pos["1"]]

    def test_ctl_remove_by_id_blocks_that_rule(self, tmp_path):
        rs, cf = self._cf(tmp_path, """
            SecAction "id:1,phase:2,pass,ctl:ruleRemoveById=900"
            SecRule ARGS "@streq a" "id:900,phase:2,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["900"]] == [pos["1"]]

    def test_ctl_remove_by_id_does_not_block_earlier_rule(self, tmp_path):
        """ruleRemoveById only affects rules that have not run yet."""
        rs, cf = self._cf(tmp_path, """
            SecRule ARGS "@streq a" "id:900,phase:2,pass"
            SecAction "id:1,phase:2,pass,ctl:ruleRemoveById=900"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["900"]] == []

    def test_skip_after_does_not_cross_phase_boundary(self, tmp_path):
        """A marker behind the skipping rule is not a valid forward target.

        ModSecurity searches forward within the current phase only. The
        phase-2 skip below must not latch onto the phase-3 copy of the marker
        and swallow the rest of the transaction.
        """
        rs, cf = self._cf(tmp_path, """
            SecMarker "M"
            SecRule ARGS "@streq a" "id:1,phase:2,pass,skipAfter:M"
            SecRule ARGS "@streq b" "id:2,phase:2,pass"
            SecRule ARGS "@streq c" "id:3,phase:3,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["2"]] == []
        assert cf.blocked_by[pos["3"]] == []

    def test_skip_n_stops_at_end_of_phase(self, tmp_path):
        rs, cf = self._cf(tmp_path, """
            SecAction "id:1,phase:2,pass,skip:2"
            SecRule ARGS "@streq a" "id:2,phase:2,pass"
            SecRule ARGS "@streq b" "id:3,phase:3,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.blocked_by[pos["2"]] == [pos["1"]]
        assert cf.blocked_by[pos["3"]] == []   # different phase

    def test_terminators_recorded(self, tmp_path):
        rs, cf = self._cf(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,deny"
            SecRule ARGS "@streq b" "id:2,phase:2,pass"
        """)
        pos = {d.rule_id: i for i, d in enumerate(rs.order) if d.kind != "marker"}
        assert cf.terminators == [pos["1"]]


class TestSetvarWriters:
    def test_writers_indexed_by_key(self, tmp_path):
        conf = write_conf(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.score=0"
            SecRule ARGS "@streq a" "id:2,phase:2,pass,setvar:tx.score=+5"
            SecRule ARGS "@streq b" "id:3,phase:2,pass,setvar:tx.other=1"
        """)
        writers = Ruleset.from_paths(conf).setvar_writers()
        assert sorted(k[1] for k in writers) == ["other", "score"]
        assert [d.rule_id for d in writers[("tx", "score")]] == ["1", "2"]
