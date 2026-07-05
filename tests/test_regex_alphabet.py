"""Tests for wafan.regex_alphabet – relevant Unicode codepoint extraction."""

from pathlib import Path

import pytest

from wafan.parser import parse_file
from wafan.regex_alphabet import extract_relevant_codepoints as ex

CONF = Path(__file__).parent / "data" / "RESPONSE-954-DATA-LEAKAGES-IIS.conf"

_UNICODE_MAX = 0x10FFFF
_ALL_CODEPOINTS = set(range(0, _UNICODE_MAX + 1))


class TestLiterals:
    def test_plain_literals(self):
        assert ex(r"abc") == {97, 98, 99}

    def test_escaped_hex_byte(self):
        assert ex(r"\x41") == {0x41}

    def test_escaped_unicode_bmp(self):
        assert ex("\\u0041") == {0x41}


class TestRanges:
    def test_class_range_fully_expanded(self):
        assert ex(r"[a-c]") == {97, 98, 99}

    def test_class_mixes_literal_and_range(self):
        assert ex(r"[a-cX]") == {97, 98, 99, 88}

    def test_multiple_ranges_in_one_class(self):
        assert ex(r"[a-cA-C0-1]") == {97, 98, 99, 65, 66, 67, 48, 49}


class TestCategories:
    def test_digit_category_boundaries(self):
        assert ex(r"\d") == {0x30, 0x39}

    def test_word_category_boundaries(self):
        assert ex(r"\w") == {0x30, 0x39, 0x41, 0x5A, 0x5F, 0x61, 0x7A}

    def test_space_category_boundaries(self):
        assert ex(r"\s") == {0x09, 0x0A, 0x0D, 0x20}

    def test_category_inside_class(self):
        assert ex(r"[a-c\d]") == {97, 98, 99, 0x30, 0x39}

    def test_negated_category_same_boundaries_as_positive(self):
        # \D is not itself a negated *class*, just a different predefined
        # category — no full-Unicode complement is triggered.
        assert ex(r"\D") == {0x30, 0x39}


class TestNegation:
    def test_negated_class_is_full_complement(self):
        assert ex(r"[^abc]") == _ALL_CODEPOINTS - {97, 98, 99}

    def test_negated_single_char_shorthand(self):
        # `[^b]` compiles to the NOT_LITERAL opcode, not IN+NEGATE.
        assert ex(r"[^b]") == _ALL_CODEPOINTS - {98}

    def test_negated_class_with_range(self):
        assert ex(r"[^a-c]") == _ALL_CODEPOINTS - {97, 98, 99}

    def test_double_negation_cancels_out(self):
        # A non-negated class and its negation must partition the full
        # codepoint space exactly.
        positive = ex(r"[abc]")
        negative = ex(r"[^abc]")
        assert positive == {97, 98, 99}
        assert negative == _ALL_CODEPOINTS - {97, 98, 99}
        assert positive | negative == _ALL_CODEPOINTS


class TestGroupsAndAlternation:
    def test_alternation_collects_both_branches(self):
        assert ex(r"cat|dog") == set(map(ord, "catdog"))

    def test_non_capturing_group(self):
        assert ex(r"(?:abc)") == {97, 98, 99}

    def test_capturing_group(self):
        assert ex(r"(abc)") == {97, 98, 99}

    def test_nested_alternation_in_group(self):
        assert ex(r"a(?:b|c)d") == set(map(ord, "abcd"))


class TestQuantifiers:
    def test_star_quantifier(self):
        assert ex(r"a*") == {97}

    def test_range_quantifier(self):
        assert ex(r"a{2,5}") == {97}

    def test_lazy_quantifier(self):
        # "." inside the quantified group still contributes every codepoint
        # except newline; "a"/"b" are already subsumed by that.
        assert ex(r"a.{0,50}?b") == _ALL_CODEPOINTS - {0x0A}

    def test_optional_group(self):
        assert ex(r"(?:bar)?") == set(map(ord, "bar"))


class TestIgnoredConstructs:
    def test_anchors_contribute_nothing(self):
        assert ex(r"^a$") == {97}

    def test_word_boundary_contributes_nothing(self):
        assert ex(r"\bfoo\b") == set(map(ord, "foo"))


class TestDotAny:
    """`.` (ANY) matches every codepoint except newline, unless DOTALL."""

    def test_dot_is_all_unicode_except_newline(self):
        assert ex(r".") == _ALL_CODEPOINTS - {0x0A}

    def test_dot_star_is_all_unicode_except_newline(self):
        assert ex(r".*") == _ALL_CODEPOINTS - {0x0A}

    def test_dot_excludes_only_newline(self):
        result = ex(r".")
        assert 0x0A not in result
        assert 0x0D in result  # carriage return still matches "."
        assert 0x41 in result
        assert _UNICODE_MAX in result

    def test_dotall_flag_includes_newline(self):
        assert ex(r"(?s).") == _ALL_CODEPOINTS

    def test_dotall_flag_via_flags_argument(self):
        import re

        assert ex(r".", flags=re.DOTALL) == _ALL_CODEPOINTS

    def test_dotall_scoped_group_alone_includes_newline(self):
        assert ex(r"(?s:.)") == _ALL_CODEPOINTS

    def test_dotall_scope_does_not_leak_outside_group(self):
        # The first "." is outside the (?s:...) group, so it must still
        # exclude newline even though a later part of the pattern is DOTALL.
        result = ex(r".(?s:.)")
        assert result == _ALL_CODEPOINTS  # union of both dots includes \n
        only_first_dot = ex(r".")
        assert 0x0A not in only_first_dot


class TestIgnoreCase:
    def test_global_flag_expands_literal(self):
        assert ex(r"(?i)abc") == set(map(ord, "abcABC"))

    def test_global_flag_expands_range(self):
        assert ex(r"(?i)[a-c]") == set(map(ord, "abcABC"))

    def test_global_flag_via_flags_argument(self):
        import re

        assert ex(r"abc", flags=re.IGNORECASE) == set(map(ord, "abcABC"))

    def test_scoped_flag_limited_to_group(self):
        # Only "bc" is inside the (?i:...) group; "a" and "d" stay case-sensitive.
        assert ex(r"a(?i:bc)d") == set(map(ord, "abcdBC"))

    def test_scoped_flag_turned_off(self):
        # (?-i:...) only turns IGNORECASE off *inside* the group; the
        # trailing "d" is still under the outer (?i).
        assert ex(r"(?i)a(?-i:bc)d") == set(map(ord, "abcdAD"))

    def test_ignorecase_negated_class_excludes_both_cases(self):
        assert ex(r"(?i)[^a]") == _ALL_CODEPOINTS - {ord("a"), ord("A")}


class TestRealWorldRules:
    """Regressions extracted from RESPONSE-954-DATA-LEAKAGES-IIS.conf."""

    @pytest.fixture(scope="class")
    def rx_patterns(self):
        rules = parse_file(CONF)
        return [r.operator_argument for r in rules if r.operator == "@rx"]

    def test_five_rx_rules_present(self, rx_patterns):
        assert len(rx_patterns) == 5

    def test_all_patterns_extract_without_error(self, rx_patterns):
        for pattern in rx_patterns:
            ex(pattern)  # must not raise

    def test_iis_inetpub_drive_letter_rule(self):
        # id:954100 — "(?i)[a-z]:[\x5c/]inetpub\b"
        # (?i)[a-z] already spans both cases of the whole alphabet, so the
        # literal "inetpub" letters (also case-folded) add nothing new.
        result = ex(r"(?i)[a-z]:[\x5c/]inetpub\b")
        expected = (
            set(range(ord("a"), ord("z") + 1))
            | set(range(ord("A"), ord("Z") + 1))
            | {ord(":"), ord("\\"), ord("/")}
        )
        assert result == expected

    def test_iis_inetpub_no_drive_letter_rule(self):
        # id:954101 — "(?i)[\x5c/]inetpub\b"
        result = ex(r"(?i)[\x5c/]inetpub\b")
        expected = {ord("\\"), ord("/")} | set(map(ord, "inetpubINETPUB"))
        assert result == expected

    def test_status_code_rule(self):
        # id:954130 — "^404$"
        assert ex(r"^404$") == {ord("4"), ord("0")}

    def test_server_error_chained_rule(self):
        # chained sub-rule of 954130 — "\bServer Error in.{0,50}?\bApplication\b"
        # (case-sensitive; "\b" contributes nothing, but the unescaped "."
        # in ".{0,50}?" contributes every codepoint except newline, which
        # subsumes all the literal characters here.)
        result = ex(r"\bServer Error in.{0,50}?\bApplication\b")
        assert result == _ALL_CODEPOINTS - {0x0A}

    def test_ole_db_availability_rule_alternation(self):
        # id:954110 — large alternation with nested groups and escapes
        pattern = (
            r"(?:Microsoft OLE DB Provider for SQL Server(?:</font>.{1,20}?"
            r"error '800(?:04005|40e31)'.{1,40}?Timeout expired"
            r"| \(0x80040e31\)<br>Timeout expired<br>)"
            r"|<h1>internal server error</h1>.*?<h2>part of the server has "
            r"crashed or it has a configuration error\.</h2>"
            r"|cannot connect to the server: timed out)"
        )
        result = ex(pattern)
        # The unescaped "." in ".{1,20}?" and ".*?" each contribute every
        # codepoint except newline, which subsumes every literal character
        # in the alternation.
        assert result == _ALL_CODEPOINTS - {0x0A}
