"""Tests for the stateful SMT encoding (wafan.state).

Solver-free: these check the *shape* of the generated encoding — sort
inference, SSA versioning, initial state, slicing, and which constructs get
abstracted. End-to-end verdicts are covered in test_reachability.py.
"""

from __future__ import annotations

import textwrap

import pytest

from wafan.ruleset import Ruleset
from wafan.state import (
    INT,
    STRING,
    member_bounds,
    encode_ruleset,
    capture_writes,
    name_is_dynamic,
    infer_tx_sorts,
    is_multi_valued,
    resolve_target,
    macro_key,
    required_members,
)
from wafan.parser import SecRuleVariable


def encode(tmp_path, text: str, name: str = "rules.conf"):
    path = tmp_path / name
    path.write_text(textwrap.dedent(text).lstrip())
    return encode_ruleset(path)


def defs_of(encoding) -> str:
    """All definition lines, joined — for substring assertions."""
    return "\n".join(line for b in encoding.blocks for line in b.definitions)


def decls_of(encoding) -> str:
    return "\n".join(
        line for b in encoding.blocks for line in b.declarations
    ) + "\n" + "\n".join(encoding.globals)


class TestMacroKey:
    @pytest.mark.parametrize("text,expected", [
        ("%{tx.foo}", ("tx", "foo")),
        ("%{TX.FOO}", ("tx", "foo")),
        (" %{tx.a_b} ", ("tx", "a_b")),
    ])
    def test_parses(self, text, expected):
        assert macro_key(text) == expected

    @pytest.mark.parametrize("text", ["5", "%{tx.foo}bar", "tx.foo", "%{MATCHED_VAR}"])
    def test_rejects(self, text):
        assert macro_key(text) is None


# ---------------------------------------------------------------------------
# Sort inference
# ---------------------------------------------------------------------------

class TestSortInference:
    def _sorts(self, tmp_path, text):
        path = tmp_path / "r.conf"
        path.write_text(textwrap.dedent(text).lstrip())
        return infer_tx_sorts(Ruleset.from_paths(path))

    def test_integer_literal_is_int(self, tmp_path):
        sorts = self._sorts(tmp_path, 'SecAction "id:1,phase:1,pass,setvar:tx.a=5"\n')
        assert sorts[("tx", "a")] == INT

    def test_increment_is_int(self, tmp_path):
        sorts = self._sorts(tmp_path, 'SecAction "id:1,phase:1,pass,setvar:tx.a=+5"\n')
        assert sorts[("tx", "a")] == INT

    def test_text_value_is_string(self, tmp_path):
        sorts = self._sorts(tmp_path, 'SecAction "id:1,phase:1,pass,setvar:\'tx.a=GET POST\'"\n')
        assert sorts[("tx", "a")] == STRING

    def test_copy_inherits_source_sort(self, tmp_path):
        sorts = self._sorts(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.src=5"
            SecAction "id:2,phase:1,pass,setvar:'tx.dst=%{tx.src}'"
        """)
        assert sorts[("tx", "dst")] == INT

    def test_string_propagates_through_copy_chain(self, tmp_path):
        sorts = self._sorts(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:'tx.a=some text'"
            SecAction "id:2,phase:1,pass,setvar:'tx.b=%{tx.a}'"
            SecAction "id:3,phase:1,pass,setvar:'tx.c=%{tx.b}'"
        """)
        assert sorts[("tx", "b")] == STRING
        assert sorts[("tx", "c")] == STRING

    def test_mixed_writes_demote_to_string(self, tmp_path):
        sorts = self._sorts(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.a=5"
            SecAction "id:2,phase:1,pass,setvar:'tx.a=text'"
        """)
        assert sorts[("tx", "a")] == STRING


# ---------------------------------------------------------------------------
# SSA structure
# ---------------------------------------------------------------------------

class TestSSA:
    def test_persistent_write_builds_on_unknown_initial_value(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,setvar:ip.count=+1"
        """)
        body = defs_of(enc)
        assert "(+ unknown_" in body

    def test_write_is_guarded_by_its_directive_firing(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,setvar:tx.hit=1"
        """)
        assert "(ite fire_0 1 0)" in defs_of(enc)

    def test_increment_accumulates_from_previous_version(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,setvar:tx.s=+5"
            SecRule ARGS "@streq b" "id:2,phase:2,pass,setvar:tx.s=+3"
        """)
        body = defs_of(enc)
        assert "(+ 0 5)" in body               # first write starts from the initial 0
        assert "(+ v_tx_s_1 3)" in body        # second builds on the first version

    def test_unset_zeroes_the_count(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.a=1"
            SecAction "id:2,phase:1,pass,setvar:!tx.a"
        """)
        assert "(assert (= cnt_tx_a_2 (ite fire_1 0 cnt_tx_a_1)))" in defs_of(enc)

    def test_unwritten_state_reads_as_absent(self, tmp_path):
        """The core tier-3 property: TX starts empty, so a counter read of a
        variable nothing writes is a literal 0, not a free variable."""
        enc = encode(tmp_path, """
            SecRule &TX:nobody_sets_this "@eq 0" "id:1,phase:2,pass"
        """)
        assert "(= 0 0)" in defs_of(enc)
        assert ("tx", "nobody_sets_this") in enc.reads_before_write
        assert ("tx", "nobody_sets_this") in enc.never_written()

    def test_persistent_collection_does_not_start_empty(self, tmp_path):
        """IP/SESSION/GLOBAL survive across requests, so their initial state is
        unknown — assuming 0 would let wafan call a live rule dead."""
        enc = encode(tmp_path, """
            SecRule &IP:blocked "@eq 0" "id:1,phase:2,pass"
        """)
        body = defs_of(enc)
        assert "(= 0 0)" not in body          # not pinned to the empty state
        assert "unknown_" in body             # a free constant instead
        assert any("(>= unknown_" in d for d in enc.global_definitions)

    def test_transaction_collection_starts_empty(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule &TX:blocked "@eq 0" "id:1,phase:2,pass"
        """)
        assert "(= 0 0)" in defs_of(enc)

    def test_reader_sees_the_version_current_at_its_position(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.a=1"
            SecRule TX:a "@eq 1" "id:2,phase:1,pass"
            SecAction "id:3,phase:1,pass,setvar:tx.a=2"
            SecRule TX:a "@eq 2" "id:4,phase:1,pass"
        """)
        body = defs_of(enc)
        # Each read is guarded by the name being set: an unset TX variable has
        # no member, so `@eq 0` must not match its initial zero.
        assert "(assert (= match_1 (and (> cnt_tx_a_1 0) (= v_tx_a_1 1))))" in body
        assert "(assert (= match_3 (and (> cnt_tx_a_2 0) (= v_tx_a_2 2))))" in body

    def test_rule_reads_pre_state_of_its_own_setvar(self, tmp_path):
        """A rule's operator sees the value *before* its own setvar runs."""
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.a=1"
            SecRule TX:a "@eq 1" "id:2,phase:1,pass,setvar:tx.a=99"
        """)
        assert "(assert (= match_1 (and (> cnt_tx_a_1 0) (= v_tx_a_1 1))))" in defs_of(enc)


class TestStateSelectors:
    """`TX:/re/` selects state variables by name. The writable namespace is
    statically known, so a selector resolves exactly -- except where a name is
    itself computed at run time."""

    def test_static_scan_covers_matching_names_only(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,t:none,setvar:'tx.hdr_a=1'"
            SecAction "id:2,phase:1,pass,t:none,setvar:'tx.hdr_b=2'"
            SecAction "id:3,phase:1,pass,t:none,setvar:'tx.other=3'"
            SecRule TX:/^hdr_/ "@eq 1" "id:4,phase:2,pass,t:none"
        """)
        body = defs_of(enc)
        assert "v_tx_hdr_a_1" in body and "v_tx_hdr_b_1" in body
        assert "v_tx_other_1" not in body.split("match_3")[-1]

    def test_scan_disjunct_is_guarded_by_the_name_being_set(self, tmp_path):
        """The static set is names that *could* exist; the count guard turns
        that into names that *do* exist at this position."""
        enc = encode(tmp_path, """
            SecRule ARGS "@streq x" "id:1,phase:1,pass,t:none,setvar:'tx.hdr_a=1'"
            SecRule TX:/^hdr_/ "@eq 1" "id:2,phase:2,pass,t:none"
        """)
        assert "(> cnt_tx_hdr_a_1 0)" in defs_of(enc)

    def test_scan_matching_nothing_is_false(self, tmp_path):
        enc = encode(tmp_path, 'SecRule TX:/^nope_/ "@eq 1" "id:1,phase:2,pass,t:none"\n')
        assert "(= match_0 false)" in defs_of(enc)

    def test_counter_scan_sums_the_matching_names(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,t:none,setvar:'tx.hdr_a=1'"
            SecAction "id:2,phase:1,pass,t:none,setvar:'tx.hdr_b=1'"
            SecRule &TX:/^hdr_/ "@ge 2" "id:3,phase:2,pass,t:none"
        """)
        body = defs_of(enc)
        assert "(ite (> cnt_tx_hdr_a_1 0) 1 0)" in body
        assert "(ite (> cnt_tx_hdr_b_1 0) 1 0)" in body


class TestDynamicStateNames:
    """A setvar whose name contains a macro writes a key known only at run
    time, so the key must be an SMT term and reads must test it symbolically."""

    def test_name_is_dynamic(self):
        assert name_is_dynamic("hdr_%{tx.1}")
        assert not name_is_dynamic("hdr_host")

    def test_key_becomes_a_concatenation_term(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@rx ^(.*)$" "id:1,phase:1,pass,capture,t:none,setvar:'tx.hdr_%{tx.1}=1'"
        """)
        assert len(enc.dynamic_slots) == 1
        slot = enc.dynamic_slots[0]
        assert slot.source == "hdr_%{tx.1}"
        assert f'(assert (= {slot.key} (str.++ "hdr_" v_tx_1_1)))' in defs_of(enc)

    def test_selector_tests_the_key_symbolically(self, tmp_path):
        """Regression: matching the selector against the literal name
        `hdr_%{tx.1}` in Python reported the reader dead, though the capture
        could well be "host"."""
        enc = encode(tmp_path, """
            SecRule ARGS "@rx ^(.*)$" "id:1,phase:1,pass,capture,t:none,setvar:'tx.hdr_%{tx.1}=1'"
            SecRule &TX:/^hdr_host$/ "!@eq 0" "id:2,phase:2,pass,t:none"
        """)
        body = defs_of(enc)
        assert "str.in_re k_tx_dyn0" in body
        assert "(= match_1 false)" not in body

    def test_exact_name_read_also_considers_dynamic_keys(self, tmp_path):
        """A run-time name may be exactly the one a later rule asks for."""
        enc = encode(tmp_path, """
            SecRule ARGS "@rx ^(.*)$" "id:1,phase:1,pass,capture,t:none,setvar:'tx.hdr_%{tx.1}=1'"
            SecRule TX:hdr_host "@eq 1" "id:2,phase:2,pass,t:none"
        """)
        assert '(= k_tx_dyn0 "hdr_host")' in defs_of(enc)

    def test_read_of_a_name_nothing_writes_is_false(self, tmp_path):
        """With no dynamic writer either, the variable cannot exist."""
        enc = encode(tmp_path, 'SecRule TX:absent "@eq 1" "id:1,phase:2,pass,t:none"\n')
        assert "(= match_0 false)" in defs_of(enc)

    def test_dynamic_names_excluded_from_static_matching(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@rx ^(.*)$" "id:1,phase:1,pass,capture,t:none,setvar:'tx.hdr_%{tx.1}=1'"
            SecRule TX:/^hdr_/ "@streq 1" "id:2,phase:2,pass,t:none"
        """)
        # handled as a dynamic slot, not as a literal key named "hdr_%{tx.1}"
        assert "v_tx_hdr__x25__x7b_" not in defs_of(enc)


class TestCaptureWrites:
    """`capture` is the second way a rule writes state, alongside `setvar`."""

    def _rule(self, tmp_path, text):
        from wafan.parser import parse_file
        path = tmp_path / "c.conf"
        path.write_text(textwrap.dedent(text).lstrip())
        return parse_file(path)[0]

    def test_slot_per_group_plus_whole_match(self, tmp_path):
        r = self._rule(tmp_path, 'SecRule ARGS "@rx (a)(b)" "id:1,phase:2,pass,capture"\n')
        assert capture_writes(r) == ["0", "1", "2"]

    def test_no_groups_still_writes_slot_zero(self, tmp_path):
        r = self._rule(tmp_path, 'SecRule ARGS "@rx abc" "id:1,phase:2,pass,capture"\n')
        assert capture_writes(r) == ["0"]

    def test_without_the_action_nothing_is_written(self, tmp_path):
        r = self._rule(tmp_path, 'SecRule ARGS "@rx (a)" "id:1,phase:2,pass"\n')
        assert capture_writes(r) == []

    def test_only_regex_operators_capture(self, tmp_path):
        r = self._rule(tmp_path, 'SecRule ARGS "@streq a" "id:1,phase:2,pass,capture"\n')
        assert capture_writes(r) == []

    def test_slots_are_string_sorted(self, tmp_path):
        """Captured text is arbitrary, so a numeric read of it is abstracted
        rather than given a bogus integer reading."""
        enc = encode(tmp_path, 'SecRule ARGS "@rx (a)" "id:1,phase:2,pass,capture"\n')
        assert enc.tx_sorts[("tx", "1")] == STRING

    def test_write_is_guarded_and_holds_an_unknown(self, tmp_path):
        enc = encode(tmp_path, 'SecRule ARGS "@rx (a)" "id:1,phase:2,pass,capture"\n')
        body = defs_of(enc)
        assert "(assert (= cnt_tx_1_1 (ite fire_0 1 0)))" in body
        assert "(ite fire_0 unknown_" in body      # value is a fresh constant

    def test_later_chain_link_sees_the_captured_value(self, tmp_path):
        """capture fills the slots when the matching link's operator runs, so
        the rest of the chain reads them -- not the state the chain began in.
        CRS rule 920190 captures two numbers and compares them in link two."""
        enc = encode(tmp_path, """
            SecRule ARGS "@rx (a)(b)" "id:1,phase:2,pass,capture,chain"
                SecRule TX:2 "@streq x"
        """)
        body = defs_of(enc)
        # the second link compares against the fresh capture, not the initial ""
        assert '(= unknown_3 "x")' in body
        assert '(= "" "x")' not in body

    def test_commit_guards_the_slot_for_later_directives(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@rx (a)" "id:1,phase:2,pass,capture"
            SecRule TX:1 "@streq y" "id:2,phase:2,pass"
        """)
        body = defs_of(enc)
        assert "(assert (= v_tx_1_1 (ite fire_0 unknown_" in body
        assert "(= v_tx_1_1 \"y\")" in body      # rule 2 reads the published version

    def test_reader_of_a_slot_is_not_reported_unwritten(self, tmp_path):
        """Regression: with capture unmodelled, TX:1 resolved to the empty
        initial state and a rule reading it was reported dead."""
        enc = encode(tmp_path, """
            SecRule ARGS "@rx (a)(b)" "id:1,phase:2,pass,capture,chain"
                SecRule TX:2 "@streq x"
        """)
        assert ("tx", "2") not in enc.never_written()


class TestMacroResolution:
    def test_macro_operator_argument_resolves_to_state(self, tmp_path):
        """The stateless encoder gives up here ("not an integer")."""
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.threshold=5"
            SecRule TX:score "@ge %{tx.threshold}" "id:2,phase:1,pass"
        """)
        assert "v_tx_threshold_1" in defs_of(enc)
        assert 1 not in enc.abstracted

    def test_setvar_rhs_macro_resolves_to_state(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.src=7"
            SecAction "id:2,phase:1,pass,setvar:'tx.dst=%{tx.src}'"
        """)
        assert "(ite fire_1 v_tx_src_1 0)" in defs_of(enc)

    def test_unresolvable_macro_becomes_a_free_constant(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:'tx.a=%{MATCHED_VAR}'"
        """)
        assert any("unknown_" in d for d in enc.globals)


# ---------------------------------------------------------------------------
# Abstraction
# ---------------------------------------------------------------------------

class TestAbstraction:
    def test_unsupported_operator_is_abstracted_not_dropped(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@detectSQLi" "id:1,phase:2,pass"
        """)
        assert 0 in enc.abstracted
        # The match term is declared but left free — never asserted equal to a
        # condition — so the rule may still fire.
        assert "(declare-const match_0 Bool)" in decls_of(enc)
        assert "(= match_0 " not in defs_of(enc)
        assert "(assert (= fire_0 match_0))" in defs_of(enc)

    def test_abstraction_is_reported_as_a_caveat(self, tmp_path):
        enc = encode(tmp_path, 'SecRule ARGS "@detectXSS" "id:1,phase:2,pass"\n')
        assert any("abstracted" in c for c in enc.caveats())

    def test_target_removal_reported(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:2,pass,ctl:ruleRemoveTargetById=900;ARGS:x"
        """)
        assert enc.target_removals == [0]
        assert any("ruleRemoveTarget" in c for c in enc.caveats())

    def test_negated_target_is_dropped_not_added(self, tmp_path):
        """`!ARGS:x` excludes a member. With a single-representative model
        there is nothing to subtract, so it must contribute no disjunct —
        the stateless encoder wrongly adds one."""
        enc = encode(tmp_path, """
            SecRule ARGS|!ARGS:x "@streq a" "id:1,phase:2,pass"
        """)
        body = defs_of(enc)
        assert "ARGS__x" not in body


# ---------------------------------------------------------------------------
# Script rendering / slicing
# ---------------------------------------------------------------------------

class TestBoundedArrays:
    """Multi-valued collections are modelled as bounded arrays of members."""

    def test_multi_valued_classification(self):
        assert is_multi_valued(SecRuleVariable("ARGS"))
        assert is_multi_valued(SecRuleVariable("REQUEST_COOKIES", "/re/"))
        assert not is_multi_valued(SecRuleVariable("REQUEST_METHOD"))
        assert not is_multi_valued(SecRuleVariable("REQUEST_FILENAME"))

    def test_bounds_are_per_target_not_global(self, tmp_path):
        """One target's cardinality must not change how others are modelled.

        Regression: a global bound let a large `&ARGS` demand open every
        collection, and --- worse --- closed a scalar against another target's
        larger bound, making the scalar's own count predicate unsatisfiable.
        """
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,chain"
                SecRule ARGS "@streq b"
            SecRule &REQUEST_FILENAME "@eq 2" "id:2,phase:2,pass"
            SecRule &REQUEST_COOKIES "@eq 1" "id:3,phase:2,pass"
        """)
        bounds = {k: (v.slots, v.closed) for k, v in enc.bounds.items()}
        assert bounds["ARGS"] == (2, True)              # two value conditions
        assert bounds["REQUEST_FILENAME"] == (1, False)  # scalar, demands 2 -> open
        assert bounds["REQUEST_COOKIES"] == (1, True)    # unaffected by the others
        assert enc.open_targets == ["REQUEST_FILENAME"]

    def test_count_predicate_raises_the_bound(self, tmp_path):
        """A literal cardinality demand must be representable, or the target
        cannot be closed and the rule would look dead."""
        enc = encode(tmp_path, 'SecRule &ARGS "@eq 3" "id:1,phase:2,pass"\n')
        assert enc.bounds["ARGS"].slots == 3
        assert enc.bounds["ARGS"].closed is True

    def test_huge_count_predicate_does_not_raise_the_bound(self, tmp_path):
        enc = encode(tmp_path, 'SecRule &ARGS "@gt 200" "id:1,phase:2,pass"\n')
        assert enc.bounds["ARGS"].slots == 1     # capped: no 201 slots
        assert enc.bounds["ARGS"].closed is False

    def test_value_and_count_demands_combine(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,chain"
                SecRule ARGS "@streq b"
            SecRule &ARGS "@eq 3" "id:2,phase:2,pass"
        """)
        assert enc.bounds["ARGS"].slots == 3     # max(2 values, 3 members)

    def test_bound_derived_from_the_widest_chain(self, tmp_path):
        """A chain placing two conditions on one collection needs two members."""
        one = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass"
        """, "one.conf")
        two = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,chain"
                SecRule ARGS "@streq b"
        """, "two.conf")
        assert one.members == 1
        assert two.members == 2

    def test_pairwise_bound_doubles(self, tmp_path):
        from wafan.ruleset import Ruleset
        path = tmp_path / "r.conf"
        path.write_text('SecRule ARGS "@streq a" "id:1,phase:2,pass"\n')
        rs = Ruleset.from_paths(path)
        assert required_members(rs) == 1
        assert required_members(rs, pairwise=True) == 2
        assert member_bounds(rs, pairwise=True)["ARGS"].slots == 2

    def test_members_are_a_disjunction_over_live_slots(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,chain"
                SecRule ARGS "@streq b"
        """)
        body = defs_of(enc)
        assert "(or (and live_ARGS_1 (= ARGS_1 \"a\")) (and live_ARGS_2 (= ARGS_2 \"a\")))" in body
        assert "(or (and live_ARGS_1 (= ARGS_1 \"b\")) (and live_ARGS_2 (= ARGS_2 \"b\")))" in body

    def test_liveness_flags_are_prefix_closed(self, tmp_path):
        """Symmetry breaking: live members occupy a prefix of the array."""
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,chain"
                SecRule ARGS "@streq b"
        """)
        assert "(assert (=> live_ARGS_2 live_ARGS_1))" in enc.global_definitions

    def test_scalar_target_is_not_unrolled(self, tmp_path):
        """Unrolling a scalar would let one request have two request methods."""
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass,chain"
                SecRule ARGS "@streq b"
            SecRule REQUEST_METHOD "@streq GET" "id:2,phase:2,pass"
        """)
        assert enc.members == 2
        decls = decls_of(enc)
        assert "(declare-const ARGS_2 String)" in decls
        assert "(declare-const REQUEST_METHOD_2 String)" not in decls
        assert "(declare-const REQUEST_METHOD_1 String)" in decls

    def test_single_member_reproduces_the_old_shape(self, tmp_path):
        enc = encode(tmp_path, 'SecRule ARGS "@streq a" "id:1,phase:2,pass"\n')
        assert enc.members == 1
        assert "(= match_0 (and live_ARGS_1 (= ARGS_1 \"a\")))" in defs_of(enc)


class TestSharedArrays:
    """Specs on one collection read one array, so their relationships hold
    by construction rather than needing axioms."""

    def test_selector_filters_the_shared_array(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS:id "@streq 42" "id:1,phase:2,pass"
            SecRule ARGS    "@streq 42" "id:2,phase:2,pass"
        """)
        assert set(enc.bounds) == {"ARGS"}          # one array, not two
        body = defs_of(enc)
        assert '(and live_ARGS_1 (= ARGS_name_1 "id") (= ARGS_1 "42"))' in body
        assert '(and live_ARGS_1 (= ARGS_1 "42"))' in body

    def test_names_view_reads_the_name_field(self, tmp_path):
        enc = encode(tmp_path, 'SecRule ARGS_NAMES "@streq secret" "id:1,phase:2,pass"\n')
        assert set(enc.bounds) == {"ARGS"}
        assert '(and live_ARGS_1 (= ARGS_name_1 "secret"))' in defs_of(enc)

    def test_count_of_a_names_view_is_the_base_count(self, tmp_path):
        """&ARGS and &ARGS_NAMES count the same members."""
        enc = encode(tmp_path, """
            SecRule &ARGS       "@eq 0" "id:1,phase:2,pass"
            SecRule &ARGS_NAMES "@eq 0" "id:2,phase:2,pass"
        """)
        body = defs_of(enc)
        assert body.count("(= cnt_ARGS 0)") == 2

    def test_selector_count_is_a_filtered_sum(self, tmp_path):
        enc = encode(tmp_path, 'SecRule &ARGS:action "@eq 1" "id:1,phase:2,pass"\n')
        assert '(ite (and live_ARGS_1 (= ARGS_name_1 "action")) 1 0)' in defs_of(enc)

    def test_exclusion_narrows_only_its_own_collection(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS|!ARGS:/__utm/|REQUEST_COOKIES "@streq bad" "id:1,phase:2,pass"
        """)
        body = defs_of(enc)
        assert '(not (str.in_re ARGS_name_1 (re.from_ecma2020 ".*(__utm).*")))' in body
        # the cookie disjunct must not inherit the ARGS exclusion
        assert '(and live_REQUEST_COOKIES_1 (= REQUEST_COOKIES_1 "bad"))' in body

    def test_regex_selector_matches_anywhere_in_the_name(self, tmp_path):
        """ModSecurity searches the name rather than anchoring to it."""
        enc = encode(tmp_path, 'SecRule REQUEST_COOKIES:/SESS/ "@streq x" "id:1,phase:2,pass"\n')
        assert '.*(SESS).*' in defs_of(enc)

    def test_header_names_are_case_insensitive(self, tmp_path):
        """HTTP header names fold case; query-parameter names do not."""
        enc = encode(tmp_path, """
            SecRule REQUEST_HEADERS:User-Agent "@streq curl" "id:1,phase:2,pass"
            SecRule REQUEST_HEADERS:user-agent "@streq curl" "id:2,phase:2,pass"
            SecRule ARGS:id "@streq 1" "id:3,phase:2,pass"
            SecRule ARGS:ID "@streq 1" "id:4,phase:2,pass"
        """)
        body = defs_of(enc)
        assert body.count('(= (str.to_lower REQUEST_HEADERS_name_1) "user-agent")') == 2
        assert '(= ARGS_name_1 "id")' in body and '(= ARGS_name_1 "ID")' in body

    def test_xml_selector_is_xpath_not_a_name(self, tmp_path):
        """XML:/* is an XPath expression, so it keeps an array of its own."""
        enc = encode(tmp_path, 'SecRule XML:/* "@streq x" "id:1,phase:2,pass"\n')
        ref = resolve_target(SecRuleVariable("XML", "/*"))
        assert ref.selector == "" and ref.family in enc.bounds
        assert "_name_" not in defs_of(enc)

    def test_family_slots_are_shared_across_specs(self, tmp_path):
        """Two specs on one collection in a chain compete for the same slots."""
        enc = encode(tmp_path, """
            SecRule ARGS:a "@streq 1" "id:1,phase:2,pass,chain"
                SecRule ARGS:b "@streq 2"
        """)
        assert enc.bounds["ARGS"].slots == 2


class TestCollectionCardinality:
    def test_closed_when_the_bound_covers_every_demand(self, tmp_path):
        enc = encode(tmp_path, 'SecRule &ARGS "@eq 1" "id:1,phase:2,pass"\n')
        assert enc.closed is True
        assert "(assert (= cnt_ARGS (ite live_ARGS_1 1 0)))" in enc.global_definitions

    def test_open_when_a_rule_demands_more_members(self, tmp_path):
        """A large cardinality bound must not force a large unrolling."""
        enc = encode(tmp_path, 'SecRule &ARGS "@gt 200" "id:1,phase:2,pass"\n')
        assert enc.members == 1          # capped rather than unrolled
        assert enc.closed is False
        assert "(assert (>= cnt_ARGS (ite live_ARGS_1 1 0)))" in enc.global_definitions
        assert any("bounded below" in c for c in enc.caveats())

    def test_macro_cardinality_is_treated_as_unknown(self, tmp_path):
        enc = encode(tmp_path, """
            SecAction "id:1,phase:1,pass,setvar:tx.max=5"
            SecRule &ARGS "@gt %{tx.max}" "id:2,phase:2,pass"
        """)
        assert enc.closed is False

    @pytest.mark.parametrize("op,slots,closed", [
        ('"@eq 1"',  1, True),    # needs 1 member
        ('"@ge 1"',  1, True),
        ('"@gt 1"',  2, True),    # ">1" means at least 2
        ('"@lt 9"',  1, True),    # upper bound only, no members demanded
        ('"@eq 0"',  1, True),
        ('"!@lt 9"', 1, False),   # negation gives a lower bound of 9, past the cap
        ('"@eq 20"', 1, False),   # past the cap: not represented, target stays open
    ])
    def test_lower_bound_table(self, tmp_path, op, slots, closed):
        from wafan.ruleset import Ruleset
        path = tmp_path / f"c{abs(hash(op))}.conf"
        path.write_text(f'SecRule &ARGS {op} "id:1,phase:2,pass"\n')
        bound = member_bounds(Ruleset.from_paths(path))["ARGS"]
        assert (bound.slots, bound.closed) == (slots, closed)


class TestAliveChain:
    def test_terminator_extends_the_alive_chain(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,deny"
            SecRule ARGS "@streq b" "id:2,phase:2,pass"
        """)
        body = defs_of(enc)
        assert "(assert (= alive_0 (not fire_0)))" in body
        assert "(assert (= fire_1 (and alive_0 match_1)))" in body

    def test_pass_rule_does_not_extend_the_chain(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass"
            SecRule ARGS "@streq b" "id:2,phase:2,pass"
        """)
        body = defs_of(enc)
        assert "alive_" not in body
        assert "(assert (= fire_1 match_1))" in body

    def test_chain_is_linear_not_quadratic(self, tmp_path):
        """Each terminator adds one link referring to the previous one, rather
        than every later position re-listing all prior terminators."""
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,deny"
            SecRule ARGS "@streq b" "id:2,phase:2,deny"
            SecRule ARGS "@streq c" "id:3,phase:2,deny"
            SecRule ARGS "@streq d" "id:4,phase:2,pass"
        """)
        body = defs_of(enc)
        assert "(assert (= alive_1 (and alive_0 (not fire_1))))" in body
        assert "(assert (= alive_2 (and alive_1 (not fire_2))))" in body
        # The last rule refers only to the newest link.
        assert "(assert (= fire_3 (and alive_2 match_3)))" in body


class TestScript:
    def test_slicing_omits_later_positions(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass"
            SecRule ARGS "@streq b" "id:2,phase:2,pass"
            SecRule ARGS "@streq c" "id:3,phase:2,pass"
        """)
        sliced = enc.script([enc.fire[0]], upto=0)
        assert "fire_0" in sliced
        assert "fire_1" not in sliced
        assert "fire_2" not in sliced

    def test_full_script_has_all_positions(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:1,phase:2,pass"
            SecRule ARGS "@streq b" "id:2,phase:2,pass"
        """)
        full = enc.script([enc.fire[1]])
        assert "fire_0" in full and "fire_1" in full

    def test_script_is_well_formed(self, tmp_path):
        enc = encode(tmp_path, 'SecRule ARGS "@streq a" "id:1,phase:2,pass"\n')
        script = enc.script([enc.fire[0]], upto=0)
        assert script.startswith("(set-logic ")
        assert script.rstrip().endswith("(check-sat)")
        assert script.count("(") == script.count(")")

    def test_collection_count_tracks_the_live_members(self, tmp_path):
        enc = encode(tmp_path, 'SecRule ARGS "@streq a" "id:1,phase:2,pass"\n')
        assert "(declare-const cnt_ARGS Int)" in enc.globals
        # Nothing here needs more members than are modelled, so the count is
        # exact rather than merely bounded below.
        assert enc.closed is True
        assert "(assert (= cnt_ARGS (ite live_ARGS_1 1 0)))" in enc.global_definitions

    def test_value_match_is_guarded_by_member_presence(self, tmp_path):
        enc = encode(tmp_path, 'SecRule ARGS "@streq a" "id:1,phase:2,pass"\n')
        assert "(and live_ARGS_1 (= ARGS_1 \"a\"))" in defs_of(enc)


class TestPositionLookup:
    def test_position_of_rule_id(self, tmp_path):
        enc = encode(tmp_path, """
            SecRule ARGS "@streq a" "id:10,phase:1,pass"
            SecRule ARGS "@streq b" "id:20,phase:2,pass"
        """)
        assert enc.order[enc.position_of_rule_id("10")].rule_id == "10"
        assert enc.order[enc.position_of_rule_id("20")].rule_id == "20"
        assert enc.position_of_rule_id("nope") is None
