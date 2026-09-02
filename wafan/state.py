"""Order-aware symbolic encoding of a whole ruleset ("stateful" encoding).

The pairwise analyses in :mod:`wafan.analyses` encode each rule's *match
condition* in isolation, over free string variables. That is the right model
for request-derived targets like ``ARGS``, which an attacker chooses freely,
but it is wrong for ``TX``: a ``TX`` variable exists only because some earlier
rule executed ``setvar:tx.…``, so both ``&TX:foo`` (its count) and
``%{tx.foo}`` (its value) are functions of *which rules fired*, not of the
request. Treating them as free lets the solver invent state that no rule in
the ruleset can produce.

This module builds the missing model. It walks the ruleset in ModSecurity's
execution order (:func:`wafan.ruleset.execution_order`) and produces, for
every directive, an SMT-LIB2 term ``fire_p`` that holds exactly when that
directive both *is reached* and *matches*:

    fire_p  =  reach_p  ∧  match_p
    reach_p =  ∧ { ¬fire_j : j skips or removes p }  ∧
               ∧ { ¬fire_j : j < p terminates the transaction }

``TX`` state is kept in SSA form: each ``setvar`` introduces a new version of
the variable, guarded by the writing directive's own ``fire`` term::

    tx_anomaly_score_3 = (ite fire_17 (+ tx_anomaly_score_2 5) tx_anomaly_score_2)

Reads resolve to whichever version is current at the reader's position, so
``&TX:foo "@eq 0"`` becomes a statement about the writers that precede it —
which is what makes it possible to conclude that a rule guarded by a ``TX``
flag nothing ever sets is dead code.

Sorts
    ``TX`` values are inferred as ``Int`` or ``String`` from how they are
    *written* (see :func:`infer_tx_sorts`). CRS writes are overwhelmingly
    numeric (432 increments and 57 integer literals in the bundled corpus),
    so ``Int`` is the common case and lets anomaly-score arithmetic be
    encoded directly rather than through ``str.to_int``.

Abstraction, and its direction
    Anything this module cannot encode faithfully — an unsupported operator,
    a macro it can't resolve, an operator/sort mismatch — is abstracted to a
    *free* Boolean constrained only by ``(=> fire_p reach_p)``. That is an
    over-approximation: the directive may or may not fire. Over-approximating
    ``fire`` is the safe direction for the question this encoding is built to
    answer, "can this rule ever fire?", because it can only make a rule look
    *more* reachable, never less. A rule reported unreachable is therefore
    genuinely unreachable (up to the caveats in
    :meth:`StateEncoding.caveats`); a rule reported reachable may not be.
"""

from __future__ import annotations

import re
from collections import Counter
from functools import lru_cache
from dataclasses import dataclass, field
from typing import Optional, Sequence

from .parser import SecRule, SecRuleVariable
from .regex_conv import UnsupportedPatternError
from .ruleset import (
    PERSISTENT_COLLECTIONS,
    STATEFUL_COLLECTIONS,
    Directive,
    Ruleset,
    SetVarOp,
)
from .smt import (
    SMT_LOGIC,
    _cached_pcre_to_ecma2020,
    _escape_smt_string,
    UnsupportedOperatorError,
    UnsupportedTransformError,
    _normalize_operator,
    _operator_builder,
    _smt_var_name,
    _wrap_negated,
    apply_transforms_smt,
    effective_transforms,
    transform_preamble,
)

INT, STRING = "Int", "String"

# Used by StateEncoding._index to slice a query down to the directives it can
# reach: the first captures a declared symbol's name, the second every
# identifier-shaped token in an expression (filtered against the declared set,
# so SMT operators and string literals fall away).
_DECLARE_RE = re.compile(r"^\(declare-(?:const|fun)\s+([A-Za-z_][A-Za-z0-9_]*)")
_SYMBOL_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

# Collections that can hold more than one member in a single transaction, and
# so are modelled as a bounded array (see `members` below). Everything not
# listed here --- REQUEST_METHOD, REQUEST_URI, REQUEST_FILENAME, RESPONSE_BODY,
# … --- holds exactly one value and stays a single constant.
#
# The default matters: unrolling a genuine scalar would let two conditions in
# one chain be satisfied by two different "members" of something that has only
# one, inventing requests that cannot exist (a chain requiring
# REQUEST_METHOD to be both GET and POST would come out satisfiable). Treating
# an unlisted collection as scalar instead merely reproduces the older,
# single-representative behaviour, so an omission from this list costs
# precision rather than soundness.
MULTI_VALUED_COLLECTIONS = frozenset({
    "ARGS", "ARGS_NAMES", "ARGS_GET", "ARGS_GET_NAMES", "ARGS_POST",
    "ARGS_POST_NAMES", "REQUEST_HEADERS", "REQUEST_HEADERS_NAMES",
    "REQUEST_COOKIES", "REQUEST_COOKIES_NAMES", "RESPONSE_HEADERS",
    "RESPONSE_HEADERS_NAMES", "FILES", "FILES_NAMES", "FILES_SIZES",
    "FILES_TMPNAMES", "FILES_TMP_CONTENT", "MULTIPART_FILENAME",
    "MULTIPART_NAME", "MATCHED_VARS", "MATCHED_VARS_NAMES", "XML", "ENV",
})


# A "_NAMES" collection is not a collection of its own: it is a view over the
# member *names* of its base. Mapping it onto the same array is what makes
# `&ARGS` and `&ARGS_NAMES` agree, and lets one chain link match a parameter's
# name while another matches its value.
NAMES_VIEW_OF = {
    "ARGS_NAMES": "ARGS",
    "ARGS_GET_NAMES": "ARGS_GET",
    "ARGS_POST_NAMES": "ARGS_POST",
    "REQUEST_HEADERS_NAMES": "REQUEST_HEADERS",
    "REQUEST_COOKIES_NAMES": "REQUEST_COOKIES",
    "RESPONSE_HEADERS_NAMES": "RESPONSE_HEADERS",
    "FILES_NAMES": "FILES",
    "MATCHED_VARS_NAMES": "MATCHED_VARS",
}

# Collections whose selector is a member *name*, so that `COLL:sel` can be
# encoded as a filter over the shared array. XML is excluded: its selector is
# an XPath expression (`XML:/*`), not a name, so each XML target keeps an array
# of its own.
_NOT_NAME_KEYED = frozenset({"XML"})

# Collections whose member names are compared case-insensitively. HTTP header
# names are, per RFC 7230; query-parameter names are not.
CASE_INSENSITIVE_NAMES = frozenset({"REQUEST_HEADERS", "RESPONSE_HEADERS"})


def is_multi_valued(variable: SecRuleVariable) -> bool:
    """True if *variable*'s collection can hold several members at once."""
    return variable.name.upper() in MULTI_VALUED_COLLECTIONS


@dataclass(frozen=True)
class TargetRef:
    """Where a target spec reads from, and how it filters.

    Several specs share one array: ``ARGS``, ``ARGS:id``, ``ARGS:/re/`` and
    ``ARGS_NAMES`` all read the members of ``ARGS``, differing only in which
    field they inspect and which members they admit. Resolving them onto a
    common *family* is what makes the relationships between them hold by
    construction rather than needing axioms --- ``ARGS:id`` is a subset of
    ``ARGS`` because it is literally the same members, filtered.
    """

    family: str        # SMT-safe name of the backing array
    multi: bool        # array of members, or a lone value
    reads_names: bool  # the operator sees the member name, not its value
    selector: str      # "" for the whole collection
    selector_is_regex: bool
    fold_case: bool    # compare names case-insensitively


def _sanitise_symbol(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", lambda m: f"_x{ord(m.group()):02x}_", text)


def resolve_target(variable: SecRuleVariable) -> TargetRef:
    """Map a target spec onto its backing array and filter."""
    name = variable.name.upper()
    part = variable.part

    if not is_multi_valued(variable) or name in _NOT_NAME_KEYED:
        # Scalars, and collections whose selector is not a member name, keep
        # the selector folded into the symbol: there is nothing to filter.
        return TargetRef(
            family=_smt_var_name(variable),
            multi=is_multi_valued(variable),
            reads_names=False,
            selector="",
            selector_is_regex=False,
            fold_case=False,
        )

    base = NAMES_VIEW_OF.get(name, name)
    is_regex = part.startswith("/") and part.endswith("/") and len(part) > 1
    return TargetRef(
        family=_sanitise_symbol(base),
        multi=True,
        reads_names=name in NAMES_VIEW_OF,
        selector=part[1:-1] if is_regex else part,
        selector_is_regex=is_regex,
        fold_case=base in CASE_INSENSITIVE_NAMES,
    )


_NUMERIC_SMT_OPS = {"eq": "=", "ge": ">=", "gt": ">", "le": "<=", "lt": "<"}

# A macro referencing one collection member in full, e.g. "%{tx.paranoia_level}".
_MACRO_RE = re.compile(r"^%\{([A-Za-z_]+)\.([A-Za-z0-9_.]+)\}$")

TxKey = tuple[str, str]


class Abstracted(Exception):
    """Raised internally when a directive cannot be encoded faithfully."""


def macro_key(text: str) -> Optional[TxKey]:
    """Parse ``"%{tx.foo}"`` into ``("tx", "foo")``; None if not such a macro."""
    m = _MACRO_RE.match(text.strip())
    if m is None:
        return None
    return m.group(1).lower(), m.group(2).lower()


# ---------------------------------------------------------------------------
# Sort inference
# ---------------------------------------------------------------------------

# ModSecurity fills TX:0 through TX:9 from a regex match, TX:0 being the whole
# match and TX:1..TX:9 the capture groups.
CAPTURE_SLOTS = 10


def _rx_group_count(pattern: str) -> int:
    """Number of capture groups in an ``@rx`` pattern.

    Falls back to every slot when the count cannot be determined, which is
    the safe direction: a slot wrongly treated as written holds an unknown
    value, whereas a slot wrongly treated as unwritten is pinned to the empty
    initial state and can make a live rule look dead.
    """
    try:
        return re.compile(_cached_pcre_to_ecma2020(pattern).pattern).groups
    except Exception:
        return CAPTURE_SLOTS - 1


def capture_writes(rule: SecRule) -> list[str]:
    """``TX`` names the ``capture`` action fills when *rule* matches.

    ``capture`` is the second way a rule writes state, alongside ``setvar``:
    it copies the regex match and its groups into ``TX:0``..``TX:9``. Only
    regex operators produce captures.

    The values are not modelled --- the encoder stores a fresh unknown in each
    slot --- but recording that the slots are *written at all* is what matters.
    Without it they resolve to the empty initial state, and a rule reading a
    capture slot is reported dead when it is not.
    """
    if not any(a.name == "capture" for a in rule.actions):
        return []
    if _normalize_operator(rule.operator)[0] != "rx":
        return []
    groups = min(_rx_group_count(rule.operator_argument), CAPTURE_SLOTS - 1)
    return [str(i) for i in range(groups + 1)]


def capture_written_keys(ruleset: Ruleset) -> set[TxKey]:
    """Every ``TX`` key some ``capture`` action in *ruleset* can write."""
    keys: set[TxKey] = set()
    for directive in ruleset.directives:
        for link in directive.chain:
            keys.update(("tx", name) for name in capture_writes(link))
    return keys


_MACRO_PIECE = re.compile(r"%\{([A-Za-z_]+)\.([A-Za-z0-9_.]+)\}")


def name_is_dynamic(name: str) -> bool:
    """True if a ``setvar`` target name is only known at run time."""
    return "%{" in name


def _rhs_is_integer(rhs: str) -> bool:
    return bool(re.fullmatch(r"[+-]?\d+", rhs.strip()))


def infer_tx_sorts(ruleset: Ruleset) -> dict[TxKey, str]:
    """Infer an SMT sort for every stateful variable the ruleset writes.

    A variable is ``Int`` when every write to it is numeric — an increment or
    decrement, an integer literal, or a copy of another variable that is
    itself ``Int`` — and ``String`` otherwise. The copy rule makes this a
    fixpoint computation: CRS has ``setvar:tx.executing_paranoia_level=
    %{tx.paranoia_level}``, whose sort follows its source.

    Unwritten variables never reach this function; readers of them resolve
    against the initial state (count 0), which is the whole point of the
    exercise.
    """
    writers = ruleset.setvar_writers()
    sorts: dict[TxKey, str] = {key: INT for key in writers}
    copies: dict[TxKey, list[TxKey]] = {}

    # Capture slots hold arbitrary text, so they are String regardless of how
    # they are later read; a numeric operator on one is abstracted rather than
    # given a bogus integer reading.
    captured = capture_written_keys(ruleset)

    for key, directives in writers.items():
        for d in directives:
            for op in d.setvars:
                if (op.collection, op.name) != key:
                    continue
                if op.op in ("inc", "dec") or op.op == "unset":
                    continue
                if _rhs_is_integer(op.rhs):
                    continue
                src = macro_key(op.rhs)
                if src is not None:
                    copies.setdefault(key, []).append(src)
                    continue
                sorts[key] = STRING  # a literal string, or unresolvable text

    for key in captured:
        sorts[key] = STRING

    # Propagate String through copy chains until stable.
    changed = True
    while changed:
        changed = False
        for key, sources in copies.items():
            if sorts.get(key) == STRING:
                continue
            for src in sources:
                if sorts.get(src, INT) == STRING:
                    sorts[key] = STRING
                    changed = True
                    break
    return sorts


# Ceiling on a bound derived from a cardinality predicate. A rule may demand
# hundreds of members (CRS compares against `tx.max_num_args`); materialising
# that many slots would be ruinous and buys nothing, since the count is a free
# integer. Past this ceiling the target simply stays open.
MAX_DERIVED_MEMBERS = 8


@dataclass(frozen=True)
class DynamicSlot:
    """A state entry whose *name* is computed at run time.

    ``setvar:'tx.hdr_%{tx.1}=1'`` writes a key that is only known once the
    macro resolves, so the key cannot be a Python string: it becomes an SMT
    term, and a read has to test it symbolically. Statically named entries
    keep their cheaper treatment --- their keys are literals, so a selector can
    be matched against them at encode time.
    """

    collection: str
    key: str      # SMT String term for the name, e.g. (str.++ "hdr_" v_tx_1_1)
    value: str    # SMT term for the value
    live: str     # Bool: this entry was written and not since unset
    sort: str
    source: str   # the literal setvar name, for reporting


@dataclass(frozen=True)
class SpecBound:
    """How one target spec is modelled: how many slots, and whether closed.

    *closed* means the count equals the number of live slots, i.e. the array
    models the whole collection. That is only legitimate when the slots can
    represent every cardinality the ruleset demands of this target; otherwise
    the slots are a prefix and the count is merely bounded below.
    """

    slots: int
    closed: bool


# Lower bound a numeric operator places on a count, keyed by (operator,
# negated). Combinations absent from the table place no lower bound.
_COUNT_LOWER_BOUND = {
    ("eq", False): lambda n: n,
    ("ge", False): lambda n: n,
    ("gt", False): lambda n: n + 1,
    ("lt", True):  lambda n: n,
    ("le", True):  lambda n: n + 1,
}


def _count_lower_bound(rule: SecRule) -> Optional[int]:
    """Lower bound this rule's operator puts on a counter target.

    Returns 0 when it places none, and None when the bound cannot be
    determined statically (a macro argument).
    """
    op_name, op_negated = _normalize_operator(rule.operator)
    if op_name not in _NUMERIC_SMT_OPS:
        return 0
    negated = rule.negated or op_negated
    fn = _COUNT_LOWER_BOUND.get((op_name, negated))
    if fn is None:
        return 0
    arg = rule.operator_argument.strip()
    if not re.fullmatch(r"[+-]?\d+", arg):
        return None  # macro or non-literal: unknown
    return fn(int(arg))


def member_bounds(
    ruleset: Ruleset, pairwise: bool = False, override: Optional[int] = None
) -> dict[str, SpecBound]:
    """Decide slot count and closedness for every request target, per spec.

    Two independent demands set the slot count.

    *Value conditions.* A condition ``∃v ∈ C. P(v)`` is witnessed by a single
    member, so a query imposing *q* simultaneous conditions on one target is
    satisfiable with at most *q* members: keeping one witness per condition
    preserves every existential, and the universal arising from a negated rule
    only becomes easier on a smaller set. *q* is the largest number of links of
    one chain placing a condition on that target; a pairwise analysis asserts
    two rules at once, so it doubles.

    *Cardinality predicates.* ``&C "@eq 3"`` cannot be satisfied by an array the
    model has closed at fewer than three members, so a literal lower bound
    raises the slot count too --- but only up to :data:`MAX_DERIVED_MEMBERS`.
    Beyond that, and whenever a bound is a macro and so unknown, the target
    stays open instead: the count is a free integer, and leaving it merely
    bounded below costs precision on the universal side of a subsumption query
    while a hundred slots would cost the solver dearly.

    Both are computed per *family* --- the array a spec reads from --- rather
    than globally. A single collection with an unbounded cardinality must not
    open every other one, and, the reason this cannot be a global number at
    all, a scalar target always has exactly one slot, so closing it against
    some other target's larger bound would make its own cardinality predicate
    unsatisfiable and the rule falsely dead. Note that ``ARGS`` and
    ``ARGS:id`` share a family and therefore compete for the same slots.
    """
    value_conditions: Counter = Counter()
    lower_bounds: dict[str, list[Optional[int]]] = {}
    multi: dict[str, bool] = {}

    for directive in ruleset.directives:
        if directive.kind != "rule":
            continue
        per_spec: Counter = Counter()
        for link in directive.chain:
            bound = _count_lower_bound(link)
            for v in link.variables:
                if v.negated:
                    continue
                if v.name.lower() in STATEFUL_COLLECTIONS:
                    continue  # TX state comes from the SSA chain, not an array
                ref = resolve_target(v)
                multi[ref.family] = ref.multi
                if v.counter:
                    lower_bounds.setdefault(ref.family, []).append(bound)
                else:
                    # Specs sharing a family share one array, so their
                    # conditions compete for the same slots.
                    per_spec[ref.family] += 1
        for spec, count in per_spec.items():
            value_conditions[spec] = max(value_conditions[spec], count)

    bounds: dict[str, SpecBound] = {}
    for spec in set(value_conditions) | set(lower_bounds) | set(multi):
        demanded = lower_bounds.get(spec, [])
        known = [b for b in demanded if b is not None]

        if not multi.get(spec, False):
            slots = 1                      # scalars are never unrolled
        elif override is not None:
            slots = max(1, override)
        else:
            slots = max(1, value_conditions.get(spec, 1))
            if pairwise:
                slots *= 2
            widest = max(known, default=0)
            if widest <= MAX_DERIVED_MEMBERS:
                slots = max(slots, widest)

        closed = all(b is not None and b <= slots for b in demanded)
        bounds[spec] = SpecBound(slots=slots, closed=closed)
    return bounds


def required_members(ruleset: Ruleset, pairwise: bool = False) -> int:
    """Largest slot count any target in *ruleset* needs (see :func:`member_bounds`)."""
    bounds = member_bounds(ruleset, pairwise=pairwise)
    return max((b.slots for b in bounds.values()), default=1)


# ---------------------------------------------------------------------------
# Encoding result
# ---------------------------------------------------------------------------

@dataclass
class PositionBlock:
    """SMT lines contributed by one position in the execution sequence."""

    position: int
    declarations: list[str] = field(default_factory=list)
    definitions: list[str] = field(default_factory=list)


@dataclass
class StateEncoding:
    """A whole-ruleset state model, sliceable by execution position."""

    order: list[Directive]
    blocks: list[PositionBlock]
    globals: list[str]                      # request variable/counter declarations
    global_definitions: list[str]            # e.g. counter non-negativity
    # Transform declarations, keyed by transform name rather than flattened, so
    # script() can emit only the ones the sliced prefix actually uses. This
    # matters a lot: the unrestricted `urlDecodeUni` definition alone is ~13 MB,
    # and piping it on every query dominates everything else.
    fun_declarations_by_key: dict[str, str]
    axioms_by_key: dict[str, list[str]]
    transform_keys_by_position: dict[int, set[str]]
    fire: dict[int, str]                     # position -> SMT Bool term
    reach: dict[int, str]                    # position -> SMT Bool term ("true" if always)
    match: dict[int, str]                    # position -> SMT Bool term for the
    # match condition alone, with reachability factored out. Asking whether a
    # rule *would* have matched irrespective of whether control flow got there
    # is what makes shadowing detectable (see wafan.analyses.stateful).
    abstracted: dict[int, str]               # position -> reason it was abstracted
    tx_sorts: dict[TxKey, str]
    reads_before_write: dict[TxKey, list[int]]  # key -> positions that read it
    # at a point where no rule had written it yet, so the read resolved to the
    # initial state (0 for TX, free for the persistent collections).
    target_removals: list[int]               # positions using ctl:ruleRemoveTarget*
    unresolved_markers: list[str]
    members: int = 1                         # largest array bound used
    closed: bool = True                      # every target's count is exact
    open_targets: list[str] = field(default_factory=list)  # targets whose count is
    # only bounded below, because a rule demands more members than are modelled
    bounds: dict[str, SpecBound] = field(default_factory=dict)  # per-target model
    dynamic_slots: list[DynamicSlot] = field(default_factory=list)  # run-time-named
    # state entries, whose keys are SMT terms rather than literals
    _dependencies: Optional[tuple] = field(default=None, repr=False, compare=False)

    def never_written(self) -> set[TxKey]:
        """State keys some rule reads that *no* rule in the ruleset writes.

        ``tx_sorts`` is keyed by exactly the variables that have a ``setvar``
        writer, so a read key absent from it has no writer at all. For ``TX``
        these are the interesting ones: the read is pinned to the empty initial
        state, which makes any guard on it decidable — usually revealing a
        vacuous check or its dead complement. Often it just means an include is
        missing (e.g. crs-setup.conf).
        """
        return {key for key in self.reads_before_write if key not in self.tx_sorts}

    def position_of_rule_id(self, rule_id: str) -> Optional[int]:
        for pos, d in enumerate(self.order):
            if d.kind != "marker" and d.rule_id == rule_id:
                return pos
        return None

    def _index(self) -> tuple:
        """Symbol tables for dependency slicing, built once per encoding."""
        if self._dependencies is not None:
            return self._dependencies

        block_declares: list[set[str]] = []
        symbols: set[str] = set()
        for block in self.blocks:
            declared = {
                m.group(1) for line in block.declarations
                if (m := _DECLARE_RE.match(line))
            }
            block_declares.append(declared)
            symbols |= declared

        global_declares: dict[str, str] = {}
        for line in self.globals:
            m = _DECLARE_RE.match(line)
            if m:
                global_declares[m.group(1)] = line
        symbols |= set(global_declares)

        def mentioned(lines: Sequence[str]) -> set[str]:
            return {t for line in lines for t in _SYMBOL_RE.findall(line)} & symbols

        block_uses = [mentioned(b.definitions) for b in self.blocks]
        global_uses = [mentioned([line]) for line in self.global_definitions]

        owner = {sym: i for i, d in enumerate(block_declares) for sym in d}
        constrained_by: dict[str, list[int]] = {}
        for j, used in enumerate(global_uses):
            for sym in used:
                constrained_by.setdefault(sym, []).append(j)

        self._dependencies = (
            block_uses, global_uses, global_declares,
            owner, constrained_by, mentioned,
        )
        return self._dependencies

    def script(self, assertions: Sequence[str], upto: Optional[int] = None,
               slice_dependencies: bool = True) -> str:
        """Render a check-sat-ready SMT-LIB2 script for *assertions*.

        Positions after *upto* are never emitted: state flows strictly
        forward, so nothing ordered later can influence the query.

        With *slice_dependencies* -- the default -- the script is narrowed
        further, to the directives the query can actually reach. Every block
        assertion *defines* symbols that same block declares, so the encoding
        is a DAG of definitions and dropping one the query cannot reach removes
        no information about it. The global constraints (a collection's prefix
        closure and its count link) are not definitions, so one is kept
        whenever any symbol it mentions survives.

        This matters at scale: a whole-corpus query otherwise carries every
        earlier rule's regex machinery, and the solver drowns in it long before
        reaching a contradiction the query itself makes obvious.
        """
        limit = len(self.order) - 1 if upto is None else upto
        in_range = [i for i, b in enumerate(self.blocks) if b.position <= limit]

        if not slice_dependencies:
            keep_blocks = in_range
            keep_globals = list(range(len(self.global_definitions)))
            keep_symbols = None
        else:
            (block_uses, global_uses, _global_declares,
             owner, constrained_by, mentioned) = self._index()
            allowed = set(in_range)
            kept_blocks: set[int] = set()
            kept_globals: set[int] = set()
            needed = mentioned([f"(assert {a})" for a in assertions])
            frontier = list(needed)
            while frontier:
                sym = frontier.pop()
                owning = owner.get(sym)
                if (owning is not None and owning in allowed
                        and owning not in kept_blocks):
                    kept_blocks.add(owning)
                    fresh = block_uses[owning] - needed
                    needed |= fresh
                    frontier.extend(fresh)
                for j in constrained_by.get(sym, ()):
                    if j in kept_globals:
                        continue
                    kept_globals.add(j)
                    fresh = global_uses[j] - needed
                    needed |= fresh
                    frontier.extend(fresh)
            keep_blocks = sorted(kept_blocks)
            keep_globals = sorted(kept_globals)
            keep_symbols = needed

        transforms: list[str] = []
        for i in keep_blocks:
            for key in self.transform_keys_by_position.get(self.blocks[i].position, ()):
                if key not in transforms:
                    transforms.append(key)

        lines = [f"(set-logic {SMT_LOGIC})"]
        for key in transforms:
            decl = self.fun_declarations_by_key.get(key)
            if decl:
                lines.append(decl)
        for key in transforms:
            lines += self.axioms_by_key.get(key, [])

        for line in self.globals:
            m = _DECLARE_RE.match(line)
            if keep_symbols is None or m is None or m.group(1) in keep_symbols:
                lines.append(line)
        lines += [self.global_definitions[j] for j in keep_globals]
        for i in keep_blocks:
            lines += self.blocks[i].declarations
            lines += self.blocks[i].definitions
        lines += [f"(assert {a})" for a in assertions]
        lines.append("(check-sat)")
        return "\n".join(lines)

    def caveats(self) -> list[str]:
        """Human-readable reasons this model may be imprecise."""
        notes: list[str] = []
        if self.abstracted:
            notes.append(
                f"{len(self.abstracted)} directive(s) abstracted to a free "
                "Boolean (unsupported construct); they are assumed able to fire"
            )
        if self.target_removals:
            notes.append(
                f"{len(self.target_removals)} ctl:ruleRemoveTarget* action(s) not "
                "modelled; affected rules keep their full target list"
            )
        if self.open_targets:
            listed = ", ".join(self.open_targets[:4])
            more = "" if len(self.open_targets) <= 4 else f" (+{len(self.open_targets) - 4} more)"
            notes.append(
                f"cardinality of {listed}{more} exceeds the modelled member count, "
                "so those counts are bounded below rather than exact and "
                "subsumption over them may be under-reported"
            )
        if self.unresolved_markers:
            notes.append(
                "skipAfter target(s) with no matching SecMarker in the analysed "
                f"files: {', '.join(self.unresolved_markers)} (skip not modelled)"
            )
        return notes


# ---------------------------------------------------------------------------
# Encoder
# ---------------------------------------------------------------------------

class StatefulEncoder:
    """Build a :class:`StateEncoding` for a :class:`~wafan.ruleset.Ruleset`."""

    def __init__(self, ruleset: Ruleset, members: Optional[int] = None,
                 pairwise: bool = False) -> None:
        self.rs = ruleset
        self.order = ruleset.order
        self.cf = ruleset.control_flow
        self.tx_sorts = infer_tx_sorts(ruleset)
        # Slot count and closedness, decided per target spec (see member_bounds).
        self.bounds = member_bounds(ruleset, pairwise=pairwise, override=members)
        self.members = max((b.slots for b in self.bounds.values()), default=1)
        self.closed = all(b.closed for b in self.bounds.values())

        # Mutable encoding state, populated by encode().
        self._blocks: list[PositionBlock] = []
        self._globals: list[str] = []
        self._global_defs: list[str] = []
        self._fire: dict[int, str] = {}
        self._reach: dict[int, str] = {}
        self._match: dict[int, str] = {}
        self._abstracted: dict[int, str] = {}
        self._cnt_term: dict[TxKey, str] = {}
        self._val_term: dict[TxKey, str] = {}
        self._version: dict[str, int] = {}
        self._request_arrays: dict[str, tuple[list[str], list[str], list[str]]] = {}
        self._request_counters: dict[str, str] = {}
        # Families whose members carry no name (scalars, XPath-selected XML).
        self._unkeyed: set[str] = {
            resolve_target(v).family
            for d in ruleset.directives if d.kind == "rule"
            for link in d.chain for v in link.variables
            if not resolve_target(v).multi or v.name.upper() in _NOT_NAME_KEYED
        }
        self._transform_keys: dict[int, set[str]] = {}
        self._position: int = -1   # position currently being encoded
        # Running "the transaction has not been ended yet" term; see _reach_expr.
        self._alive: str = "true"
        self._reads_before_write: dict[TxKey, list[int]] = {}
        # Capture slots filled during the chain walk of the directive being
        # encoded: key -> (fresh value symbol, value before the directive).
        self._dynamic_slots: list[DynamicSlot] = []
        self._pending_captures: dict[TxKey, tuple[str, str]] = {}
        self._cnt_before_captures: dict[TxKey, str] = {}
        self._fresh = 0

    # -- naming ------------------------------------------------------------

    def _sanitise(self, key: TxKey) -> str:
        raw = f"{key[0]}_{key[1]}"
        return re.sub(r"[^A-Za-z0-9_]", lambda m: f"_x{ord(m.group()):02x}_", raw)

    def _next_version(self, base: str) -> str:
        v = self._version.get(base, 0) + 1
        self._version[base] = v
        return f"{base}_{v}"

    def _fresh_const(self, sort: str) -> str:
        self._fresh += 1
        name = f"unknown_{self._fresh}"
        self._globals.append(f"(declare-const {name} {sort})")
        return name

    # -- state access ------------------------------------------------------

    def _initial_cnt(self, key: TxKey) -> str:
        """Count of *key* before any rule in this ruleset writes it.

        Zero for ``TX`` (a fresh, empty collection every transaction) and a
        free non-negative Int for the persistent collections, whose contents
        may have been written by an earlier request.
        """
        if key[0] in PERSISTENT_COLLECTIONS:
            sym = self._fresh_const(INT)
            self._global_defs.append(f"(assert (>= {sym} 0))")
            return sym
        return "0"

    def _initial_val(self, key: TxKey) -> str:
        if key[0] in PERSISTENT_COLLECTIONS:
            return self._fresh_const(self.tx_sorts.get(key, INT))
        return "0" if self.tx_sorts.get(key, INT) == INT else '""'

    def _cnt(self, key: TxKey, position: int, record: bool = True) -> str:
        """Current count term for *key*, or its initial state if unwritten.

        *record* is False when the caller is a ``setvar`` fetching the
        pre-write value: that is a write, not a read, and must not be counted
        as one.
        """
        if key not in self._cnt_term:
            if record:
                self._reads_before_write.setdefault(key, []).append(position)
            self._cnt_term[key] = self._initial_cnt(key)
        return self._cnt_term[key]

    def _val(self, key: TxKey, position: int, record: bool = True) -> str:
        """Current value term for *key*, or its initial state if unwritten."""
        if key not in self._val_term:
            if record:
                self._reads_before_write.setdefault(key, []).append(position)
            self._val_term[key] = self._initial_val(key)
        return self._val_term[key]

    def _bound_for(self, name: str) -> SpecBound:
        """Slot count and closedness for one spec; a lone slot if unseen."""
        return self.bounds.get(name, SpecBound(slots=1, closed=True))

    def _request_array(self, family: str, slots: int, closed: bool,
                       keyed: bool) -> tuple[list[str], list[str], list[str]]:
        """Declare (once) the bounded array backing one collection family.

        Each of *slots* members is a value constant, a "this member is present"
        flag and --- when *keyed* --- a name constant, so that a selector can be
        expressed as a filter over the same array rather than as a second,
        unrelated one.

        Two constraints tie the slots together.

        *Prefix closure* (``live_{i+1} => live_i``) says the live members occupy
        a prefix. Matching is an existential over members and so permutation
        invariant, meaning this removes no model up to reordering; what it
        removes is the pile of equivalent liveness patterns the solver would
        otherwise enumerate.

        *The count link* is deliberately asymmetric. If the last slot is unused
        the whole array has been modelled and the count is exact; if it is used
        there may be further members beyond the bound, so the count is only
        bounded below. When the bound covers every cardinality the ruleset asks
        of this family (see :func:`member_bounds`) the count is simply exact.
        """
        existing = self._request_arrays.get(family)
        if existing is not None:
            return existing

        values = [f"{family}_{i}" for i in range(1, slots + 1)]
        flags = [f"live_{family}_{i}" for i in range(1, slots + 1)]
        names = [f"{family}_name_{i}" for i in range(1, slots + 1)] if keyed else []
        for symbol in (*values, *names):
            self._globals.append(f"(declare-const {symbol} String)")
        for flag in flags:
            self._globals.append(f"(declare-const {flag} Bool)")
        for prev, cur in zip(flags, flags[1:]):
            self._global_defs.append(f"(assert (=> {cur} {prev}))")

        count = f"cnt_{family}"
        self._request_counters[family] = count
        self._globals.append(f"(declare-const {count} Int)")
        live_sum = self._live_sum(flags)
        if closed:
            self._global_defs.append(f"(assert (= {count} {live_sum}))")
        else:
            self._global_defs.append(f"(assert (>= {count} {live_sum}))")
            self._global_defs.append(
                f"(assert (=> (not {flags[-1]}) (= {count} {live_sum})))"
            )

        self._request_arrays[family] = (values, flags, names)
        return values, flags, names

    @staticmethod
    def _live_sum(flags: Sequence[str], extra: Optional[Sequence[str]] = None) -> str:
        """Number of live slots, optionally restricted by a per-slot predicate."""
        terms = [
            f"(ite {f} 1 0)" if extra is None else f"(ite (and {f} {p}) 1 0)"
            for f, p in zip(flags, extra if extra is not None else flags)
        ]
        return terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"

    def _array_for(self, ref: TargetRef) -> tuple[list[str], list[str], list[str]]:
        bound = self._bound_for(ref.family)
        keyed = ref.multi and ref.family not in self._unkeyed
        return self._request_array(ref.family, bound.slots, bound.closed, keyed)

    def _selector_predicate(self, ref: TargetRef, name_symbol: str) -> str:
        """Constraint saying a member's name matches *ref*'s selector.

        A regex selector matches anywhere in the name --- ModSecurity searches
        rather than anchoring --- so the wildcards are spliced into the pattern
        text. They cannot be added with ``re.++``/``re.*`` because
        ``re.from_ecma2020`` is a solver extension that does not compose with
        the standard regex constructors.
        """
        subject = f"(str.to_lower {name_symbol})" if ref.fold_case else name_symbol
        if ref.selector_is_regex:
            conv = _cached_pcre_to_ecma2020(ref.selector)
            body = conv.pattern
            # Only pad the side that is not already anchored: `.*(^s$).*` is
            # both redundant and markedly harder for the solver than `^s$`.
            prefix = "" if body.startswith("^") else ".*"
            suffix = "" if body.endswith("$") else ".*"
            pattern = _escape_smt_string(f"{prefix}({body}){suffix}")
            return f'(str.in_re {subject} (re.from_ecma2020 "{pattern}"))'
        literal = ref.selector.lower() if ref.fold_case else ref.selector
        return f'(= {subject} "{_escape_smt_string(literal)}")'

    # -- operator atoms ----------------------------------------------------

    def _numeric_value(self, rule: SecRule, position: int) -> str:
        """Resolve a numeric operator's argument to an SMT Int term.

        An integer literal is used as-is; ``%{tx.foo}`` resolves to ``foo``'s
        current SSA version — which is exactly the case the stateless encoder
        has to give up on (``"Operator argument '%{tx.…}' is not an integer"``).
        """
        arg = rule.operator_argument.strip()
        if re.fullmatch(r"[+-]?\d+", arg):
            return arg
        key = macro_key(arg)
        if key is None:
            raise Abstracted(f"operator argument '{arg}' is not an integer or macro")
        if key[0] not in STATEFUL_COLLECTIONS:
            raise Abstracted(f"macro '{arg}' refers to non-stateful collection")
        if self.tx_sorts.get(key, INT) != INT:
            raise Abstracted(f"macro '{arg}' resolves to a String-sorted variable")
        return self._val(key, position)

    def _numeric_atom(self, rule: SecRule, term: str, position: int) -> str:
        """Apply a numeric operator directly to an Int *term*."""
        op_name, op_negated = _normalize_operator(rule.operator)
        smt_op = _NUMERIC_SMT_OPS.get(op_name)
        if smt_op is None:
            raise Abstracted(f"operator '{rule.operator}' is not numeric")
        value = self._numeric_value(rule, position)
        return _wrap_negated(f"({smt_op} {term} {value})", rule.negated or op_negated)

    def _string_atom(self, rule: SecRule, term: str) -> str:
        """Apply *rule*'s operator to a String-valued *term*."""
        transforms = effective_transforms(rule)
        if transforms:
            self._transform_keys.setdefault(self._position, set()).update(
                t.lower() for t in transforms
            )
        try:
            expr = apply_transforms_smt(term, transforms)
            return _operator_builder(rule)(expr)
        except (UnsupportedOperatorError, UnsupportedTransformError, UnsupportedPatternError) as exc:
            raise Abstracted(str(exc)) from exc

    def _request_atom(
        self,
        rule: SecRule,
        variable: SecRuleVariable,
        position: int,
        exclusions: Sequence[TargetRef] = (),
    ) -> str:
        """Encode one request target: an existential over its live members.

        ModSecurity applies the operator to every member a target resolves to
        and fires if any matches, so this is a disjunction over the backing
        array's slots. Each disjunct is guarded by the slot's presence flag,
        by the target's own selector, and by the negation of every exclusion
        that narrows the same collection.
        """
        ref = resolve_target(variable)
        if variable.counter:
            return self._numeric_atom(rule, self._request_counter(ref), position)

        values, flags, names = self._array_for(ref)
        disjuncts = []
        for index, (value, flag) in enumerate(zip(values, flags)):
            subject = names[index] if ref.reads_names else value
            guards = [flag]
            if ref.selector and names:
                guards.append(self._selector_predicate(ref, names[index]))
            for excluded in exclusions:
                if names:
                    guards.append(
                        f"(not {self._selector_predicate(excluded, names[index])})"
                    )
            guards.append(self._string_atom(rule, subject))
            disjuncts.append("(and " + " ".join(guards) + ")")
        return disjuncts[0] if len(disjuncts) == 1 else "(or " + " ".join(disjuncts) + ")"

    def _request_counter(self, ref: TargetRef) -> str:
        """Term for ``&VAR``: the whole count, or a count of matching members."""
        values, flags, names = self._array_for(ref)
        if not ref.selector or not names:
            self._array_for(ref)
            return self._request_counters[ref.family]
        matching = [self._selector_predicate(ref, name) for name in names]
        return self._live_sum(flags, matching)

    @lru_cache(maxsize=256)
    def _name_regex(pattern: str):  # type: ignore[misc]
        """Compile a selector regex for matching state variable names.

        Names are compared case-insensitively, matching ModSecurity, and the
        match is a search rather than an anchored one. Returns None when the
        pattern cannot be compiled either as written or after PCRE
        translation.
        """
        for candidate in (pattern, _cached_pcre_to_ecma2020(pattern).pattern):
            try:
                return re.compile(candidate, re.IGNORECASE)
            except re.error:
                continue
        return None

    _name_regex = staticmethod(_name_regex)  # type: ignore[assignment]

    def _matching_state_keys(self, collection: str, pattern: str) -> list[TxKey]:
        """State keys of *collection* whose name matches *pattern*.

        Unlike a request collection, the writable namespace is statically
        known: a name can only exist if some ``setvar`` or ``capture`` writes
        it. Resolving a regex selector against that set is therefore exact ---
        and an empty result is a real finding, meaning no such variable can
        ever exist.
        """
        compiled = self._name_regex(pattern)
        if compiled is None:
            raise Abstracted(f"selector regex '/{pattern}/' could not be compiled")
        return sorted(
            k for k in self.tx_sorts
            if k[0] == collection and not name_is_dynamic(k[1])
            and compiled.search(k[1])
        )

    def _dynamic_matches(self, collection: str, pattern: Optional[str],
                         exact: Optional[str] = None) -> list[tuple[DynamicSlot, str]]:
        """Dynamic slots of *collection* whose key could satisfy the selector.

        The key is an SMT term, so the test is symbolic: equality for an exact
        name, regex membership for a selector. Whether it really matches is
        left to the solver, which is the only way a run-time-computed name can
        be related to the name a later rule asks for.
        """
        out = []
        for slot in self._dynamic_slots:
            if slot.collection != collection:
                continue
            if exact is not None:
                out.append((slot, f'(= {slot.key} "{_escape_smt_string(exact)}")'))
            else:
                conv = _cached_pcre_to_ecma2020(pattern or "")
                body = conv.pattern
                prefix = "" if body.startswith("^") else ".*"
                suffix = "" if body.endswith("$") else ".*"
                expr = _escape_smt_string(f"{prefix}({body}){suffix}")
                out.append(
                    (slot, f'(str.in_re {slot.key} (re.from_ecma2020 "{expr}"))')
                )
        return out

    def _dynamic_atom(self, rule: SecRule, slot: DynamicSlot, key_test: str,
                      position: int) -> str:
        """One disjunct: this dynamic entry is present, keyed right, and matches."""
        if slot.sort == INT:
            if effective_transforms(rule):
                raise Abstracted(f"transforms applied to Int-sorted {slot.source}")
            body = self._numeric_atom(rule, slot.value, position)
        else:
            body = self._string_atom(rule, slot.value)
        return f"(and {slot.live} {key_test} {body})"

    def _stateful_scan_atom(self, rule: SecRule, collection: str, pattern: str,
                            counter: bool, position: int) -> str:
        """Encode ``COLL:/re/`` as a scan over the matching state variables."""
        keys = self._matching_state_keys(collection, pattern)
        dynamic = self._dynamic_matches(collection, pattern)

        if counter:
            terms = [f"(ite (> {self._cnt(k, position)} 0) 1 0)" for k in keys]
            terms += [f"(ite (and {s.live} {t}) 1 0)" for s, t in dynamic]
            if not terms:
                total = "0"
            elif len(terms) == 1:
                total = terms[0]
            else:
                total = "(+ " + " ".join(terms) + ")"
            return self._numeric_atom(rule, total, position)

        if not keys and not dynamic:
            # No rule writes a name matching the selector, so the target
            # resolves to no members and the operator cannot hold.
            return "false"

        atoms = [self._dynamic_atom(rule, s, t, position) for s, t in dynamic]
        for key in keys:
            guard = f"(> {self._cnt(key, position)} 0)"
            term = self._val(key, position)
            if self.tx_sorts.get(key, INT) == INT:
                if effective_transforms(rule):
                    raise Abstracted(
                        f"transforms applied to Int-sorted {key[0]}.{key[1]}"
                    )
                atoms.append(f"(and {guard} {self._numeric_atom(rule, term, position)})")
            else:
                atoms.append(f"(and {guard} {self._string_atom(rule, term)})")
        return atoms[0] if len(atoms) == 1 else "(or " + " ".join(atoms) + ")"

    def _target_atom(self, rule: SecRule, variable: SecRuleVariable, position: int,
                     exclusions: Sequence[TargetRef] = ()) -> str:
        collection = variable.name.lower()
        if collection in STATEFUL_COLLECTIONS and variable.part:
            part = variable.part
            if len(part) > 1 and part.startswith("/") and part.endswith("/"):
                return self._stateful_scan_atom(
                    rule, collection, part[1:-1], variable.counter, position
                )
            key = (collection, part.lower())
            # A run-time-computed name may be exactly the one asked for here,
            # so the dynamic slots have to be considered alongside the keyed
            # entry rather than instead of it.
            dynamic = self._dynamic_matches(collection, None, exact=part.lower())

            if variable.counter:
                total = f"(ite (> {self._cnt(key, position)} 0) 1 0)"
                if dynamic:
                    terms = [total] + [
                        f"(ite (and {d.live} {t}) 1 0)" for d, t in dynamic
                    ]
                    total = "(+ " + " ".join(terms) + ")"
                    return self._numeric_atom(rule, total, position)
                return self._numeric_atom(rule, self._cnt(key, position), position)

            atoms = [self._dynamic_atom(rule, d, t, position) for d, t in dynamic]

            # Only a name some directive actually writes can contribute a
            # statically keyed disjunct. For any other name the variable
            # cannot exist, so it contributes nothing --- and attempting it
            # would guess a sort for a variable that was never written.
            if key in self.tx_sorts:
                term = self._val(key, position)
                if self.tx_sorts[key] == INT:
                    if effective_transforms(rule):
                        raise Abstracted(
                            f"transforms applied to Int-sorted "
                            f"{collection}.{variable.part}"
                        )
                    body = self._numeric_atom(rule, term, position)
                else:
                    body = self._string_atom(rule, term)
                atoms.insert(0, f"(and (> {self._cnt(key, position)} 0) {body})")
            elif not atoms:
                # Nothing writes this name, so the target resolves to no
                # members and the operator cannot hold.
                self._reads_before_write.setdefault(key, []).append(position)
                return "false"

            return atoms[0] if len(atoms) == 1 else "(or " + " ".join(atoms) + ")"
        return self._request_atom(rule, variable, position, exclusions)

    def _rule_match(self, rule: SecRule, position: int) -> str:
        # A negated target (`!ARGS:/__utm/`) removes members from the
        # collection it names, and only from that one, so exclusions are
        # grouped by family and applied to that family's disjuncts. An
        # exclusion on a family whose members carry no name cannot be
        # expressed and is dropped, which over-approximates the match --- the
        # safe direction (see the module docstring).
        exclusions: dict[str, list[TargetRef]] = {}
        for v in rule.variables:
            if v.negated:
                ref = resolve_target(v)
                exclusions.setdefault(ref.family, []).append(ref)

        atoms = [
            self._target_atom(rule, v, position,
                              exclusions.get(resolve_target(v).family, ()))
            for v in rule.variables
            if not v.negated
        ]
        if not atoms:
            raise Abstracted("rule has no positive targets")
        return atoms[0] if len(atoms) == 1 else "(or " + " ".join(atoms) + ")"

    def _chain_match(self, chain: Sequence[SecRule], position: int) -> str:
        """Conjoin the links, threading each link's captures to the next.

        ``capture`` fills ``TX:0``..``TX:9`` the moment the matching link's
        operator runs, so a later link of the same chain reads the captured
        values, not the state the chain started with. CRS relies on this: rule
        $920190$ captures two numbers in its first link and compares them in
        its second.
        """
        atoms = []
        for link in chain:
            atoms.append(self._rule_match(link, position))
            self._stage_captures(link, position)
        return atoms[0] if len(atoms) == 1 else "(and " + " ".join(atoms) + ")"

    def _stage_captures(self, link: SecRule, position: int) -> None:
        """Make *link*'s capture slots readable by the rest of the chain.

        The captured text depends on where the pattern matched, which the
        encoding does not track, so each slot becomes a fresh unconstrained
        value. Within the chain it is used unguarded --- the chain only gets
        this far if the link matched --- while :meth:`_commit_captures` adds
        the firing guard for the benefit of later directives.
        """
        for name in capture_writes(link):
            key = ("tx", name)
            if key in self._pending_captures:
                continue  # an earlier link of this chain already filled it
            before = self._val(key, position, record=False)
            fresh = self._fresh_const(self.tx_sorts.get(key, STRING))
            self._pending_captures[key] = (fresh, before)
            self._val_term[key] = fresh
            self._cnt_term[key] = "1"

    # -- reachability ------------------------------------------------------

    def _reach_expr(self, position: int) -> str:
        """Condition under which execution arrives at *position*.

        Two independent parts:

        * *alive* — no earlier directive has ended the transaction. This is
          maintained as a chain (``alive_p = alive_{p-1} ∧ ¬fire_{p-1}``, one
          link per terminating directive) rather than re-listing every prior
          terminator at every position, which would make the encoding
          quadratic in the number of disruptive rules.
        * *not skipped* — none of the specific directives that jump over or
          remove this position has fired. That part is position-specific and
          cannot be chained.
        """
        guards: list[str] = []
        if self._alive != "true":
            guards.append(self._alive)
        for j in self.cf.blocked_by.get(position, []):
            term = self._fire.get(j)
            if term is not None:
                guards.append(f"(not {term})")
        if not guards:
            return "true"
        if len(guards) == 1:
            return guards[0]
        return "(and " + " ".join(guards) + ")"

    def _advance_alive(self, directive: Directive, position: int, block: PositionBlock) -> None:
        """Extend the *alive* chain past a directive that can end the transaction."""
        if not directive.terminates:
            return
        sym = f"alive_{position}"
        block.declarations.append(f"(declare-const {sym} Bool)")
        fire = self._fire[position]
        body = (
            f"(not {fire})" if self._alive == "true"
            else f"(and {self._alive} (not {fire}))"
        )
        block.definitions.append(f"(assert (= {sym} {body}))")
        self._alive = sym

    # -- state updates -----------------------------------------------------

    def _state_macro(self, text: str) -> Optional[TxKey]:
        """Key a macro refers to, but only if it names a writable collection.

        ``%{rule.msg}``, ``%{MATCHED_VAR}`` and the like are engine-provided
        values, not state. Resolving them through :meth:`_val` would invent a
        state variable and pin it to the empty initial value --- an
        under-approximation, and the unsafe direction. They must become
        unknowns instead.
        """
        key = macro_key(text)
        if key is None or key[0] not in STATEFUL_COLLECTIONS:
            return None
        return key

    def _key_term(self, name: str, position: int) -> str:
        """SMT String term for a run-time-computed state name.

        The literal fragments are concatenated with the macros' current
        values, so ``hdr_%{tx.1}`` becomes ``(str.++ "hdr_" v_tx_1_1)``. A
        macro naming something the model does not track contributes an unknown
        instead, which keeps the key a free string rather than a wrong one.
        """
        pieces: list[str] = []
        last = 0
        for m in _MACRO_PIECE.finditer(name):
            if m.start() > last:
                pieces.append('"' + name[last:m.start()].replace('"', '""') + '"')
            src = (m.group(1).lower(), m.group(2).lower())
            if src[0] in STATEFUL_COLLECTIONS and self.tx_sorts.get(src) == STRING:
                pieces.append(self._val(src, position, record=False))
            else:
                pieces.append(self._fresh_const(STRING))
            last = m.end()
        if last < len(name):
            pieces.append('"' + name[last:].replace('"', '""') + '"')
        if not pieces:
            return '""'
        return pieces[0] if len(pieces) == 1 else "(str.++ " + " ".join(pieces) + ")"

    def _write_dynamic(self, op: SetVarOp, position: int, block: PositionBlock) -> None:
        """Record a write whose key is computed at run time."""
        fire = self._fire[position]
        sort = self.tx_sorts.get((op.collection, op.name), STRING)
        tag = self._sanitise((op.collection, f"dyn{len(self._dynamic_slots)}"))
        key_sym, val_sym, live_sym = f"k_{tag}", f"v_{tag}", f"live_{tag}"
        block.declarations.append(f"(declare-const {key_sym} String)")
        block.declarations.append(f"(declare-const {val_sym} {sort})")
        block.declarations.append(f"(declare-const {live_sym} Bool)")
        block.definitions.append(
            f"(assert (= {key_sym} {self._key_term(op.name, position)}))"
        )
        value = ('""' if sort == STRING else "0") if op.op == "unset" else \
            self._rhs_term(op, (op.collection, op.name), position)
        block.definitions.append(f"(assert (= {val_sym} {value}))")
        live = "false" if op.op == "unset" else fire
        block.definitions.append(f"(assert (= {live_sym} {live}))")
        self._dynamic_slots.append(DynamicSlot(
            collection=op.collection, key=key_sym, value=val_sym,
            live=live_sym, sort=sort, source=op.name,
        ))

    def _rhs_term(self, op: SetVarOp, key: TxKey, position: int) -> str:
        sort = self.tx_sorts.get(key, INT)
        if sort == INT:
            if _rhs_is_integer(op.rhs):
                return op.rhs.strip()
            src = self._state_macro(op.rhs)
            if src is not None and self.tx_sorts.get(src, INT) == INT:
                return self._val(src, position)
            return self._fresh_const(INT)
        src = self._state_macro(op.rhs)
        if src is not None and self.tx_sorts.get(src, INT) == STRING:
            return self._val(src, position)
        if "%{" in op.rhs:
            return self._fresh_const(STRING)
        return '"' + op.rhs.replace('"', '""') + '"'

    def _apply_setvars(self, directive: Directive, position: int, block: PositionBlock) -> None:
        fire = self._fire[position]
        for op in directive.setvars:
            if op.collection not in STATEFUL_COLLECTIONS:
                continue
            if name_is_dynamic(op.name):
                self._write_dynamic(op, position, block)
                continue
            key = (op.collection, op.name)
            sort = self.tx_sorts.get(key, INT)

            # --- count ---
            old_cnt = self._cnt(key, position, record=False)
            new_cnt = "0" if op.op == "unset" else "1"
            cnt_sym = self._next_version("cnt_" + self._sanitise(key))
            block.declarations.append(f"(declare-const {cnt_sym} Int)")
            block.definitions.append(
                f"(assert (= {cnt_sym} (ite {fire} {new_cnt} {old_cnt})))"
            )
            self._cnt_term[key] = cnt_sym

            # --- value ---
            old_val = self._val(key, position, record=False)
            if op.op == "unset":
                new_val = "0" if sort == INT else '""'
            elif op.op in ("inc", "dec"):
                if sort != INT:
                    new_val = self._fresh_const(STRING)
                else:
                    arith = "+" if op.op == "inc" else "-"
                    new_val = f"({arith} {old_val} {self._rhs_term(op, key, position)})"
            else:
                new_val = self._rhs_term(op, key, position)
            val_sym = self._next_version("v_" + self._sanitise(key))
            block.declarations.append(f"(declare-const {val_sym} {sort})")
            block.definitions.append(
                f"(assert (= {val_sym} (ite {fire} {new_val} {old_val})))"
            )
            self._val_term[key] = val_sym

    def _commit_captures(self, position: int, block: PositionBlock) -> None:
        """Publish the staged capture slots to subsequent directives.

        Inside the chain the fresh value was used unguarded; a later directive
        must only see it if this directive actually fired, so each slot gets
        the usual guarded SSA version here.
        """
        fire = self._fire[position]
        for key, (fresh, before) in self._pending_captures.items():
            sort = self.tx_sorts.get(key, STRING)
            cnt_before = self._cnt_before_captures.get(key, "0")
            cnt_sym = self._next_version("cnt_" + self._sanitise(key))
            block.declarations.append(f"(declare-const {cnt_sym} Int)")
            block.definitions.append(
                f"(assert (= {cnt_sym} (ite {fire} 1 {cnt_before})))"
            )
            self._cnt_term[key] = cnt_sym

            val_sym = self._next_version("v_" + self._sanitise(key))
            block.declarations.append(f"(declare-const {val_sym} {sort})")
            block.definitions.append(
                f"(assert (= {val_sym} (ite {fire} {fresh} {before})))"
            )
            self._val_term[key] = val_sym
        self._pending_captures = {}

    # -- driver ------------------------------------------------------------

    def encode(self) -> StateEncoding:
        target_removals: list[int] = []

        for position, directive in enumerate(self.order):
            if directive.kind == "marker":
                continue

            self._position = position
            block = PositionBlock(position=position)
            if directive.removes_targets:
                target_removals.append(position)

            reach = self._reach_expr(position)
            # Name it only when it is a compound expression: a single-symbol
            # reach (the common case — just the current `alive` link) needs no
            # alias, and introducing one only adds an indirection for the solver
            # and noise for anyone reading the script.
            if reach.startswith("("):
                reach_sym = f"reach_{position}"
                block.declarations.append(f"(declare-const {reach_sym} Bool)")
                block.definitions.append(f"(assert (= {reach_sym} {reach}))")
                reach = reach_sym
            self._reach[position] = reach

            # SecAction has no operator: its match condition is vacuously true.
            match_sym = "true"
            self._pending_captures = {}
            self._cnt_before_captures = {
                ("tx", name): self._cnt_term.get(("tx", name), "0")
                for link in directive.chain for name in capture_writes(link)
            }
            if directive.kind == "rule":
                match_sym = f"match_{position}"
                block.declarations.append(f"(declare-const {match_sym} Bool)")
                try:
                    match_expr = self._chain_match(directive.chain, position)
                except Abstracted as exc:
                    # Left free: the rule may or may not match. This
                    # over-approximates `fire`, so an abstracted rule is never
                    # reported dead or excluded from a pair.
                    self._abstracted[position] = str(exc)
                else:
                    block.definitions.append(f"(assert (= {match_sym} {match_expr}))")
            self._match[position] = match_sym

            fire_sym = f"fire_{position}"
            block.declarations.append(f"(declare-const {fire_sym} Bool)")
            if match_sym == "true":
                block.definitions.append(f"(assert (= {fire_sym} {reach}))")
            elif reach == "true":
                block.definitions.append(f"(assert (= {fire_sym} {match_sym}))")
            else:
                block.definitions.append(
                    f"(assert (= {fire_sym} (and {reach} {match_sym})))"
                )

            self._fire[position] = fire_sym
            self._commit_captures(position, block)
            self._apply_setvars(directive, position, block)
            self._advance_alive(directive, position, block)
            self._blocks.append(block)

        fun_decls_by_key, axioms_by_key = self._preamble()
        return StateEncoding(
            order=list(self.order),
            blocks=self._blocks,
            globals=self._globals,
            global_definitions=self._global_defs,
            fun_declarations_by_key=fun_decls_by_key,
            axioms_by_key=axioms_by_key,
            transform_keys_by_position=self._transform_keys,
            fire=self._fire,
            reach=self._reach,
            match=self._match,
            abstracted=self._abstracted,
            tx_sorts=self.tx_sorts,
            reads_before_write=self._reads_before_write,
            target_removals=target_removals,
            unresolved_markers=self.rs.unresolved_markers(),
            members=self.members,
            closed=self.closed,
            open_targets=sorted(n for n, b in self.bounds.items() if not b.closed),
            bounds=dict(self.bounds),
            dynamic_slots=list(self._dynamic_slots),
        )

    def _preamble(self) -> tuple[dict[str, str], dict[str, list[str]]]:
        """Build each used transform's ``define-fun`` and axioms, keyed by name.

        Every rule in the ruleset shares one SMT script here, so a transform's
        single global declaration has to serve all of them. The codepoint
        restriction that :func:`wafan.smt.transform_preamble` can apply is
        deliberately *not* used: it is only sound relative to the pattern a
        transform's output feeds into, and in a whole-ruleset script that is
        every pattern at once. Passing ``relevant=None`` keeps the full,
        unrestricted definition — correct, but large, which is why the result is
        keyed so :meth:`StateEncoding.script` can emit only what a slice needs.
        """
        decls: dict[str, str] = {}
        axioms: dict[str, list[str]] = {}
        used = {key for keys in self._transform_keys.values() for key in keys}
        for key in used:
            try:
                fd, ax = transform_preamble([key], None, set())
            except UnsupportedTransformError:
                continue
            if fd:
                decls[key] = fd[0]
            if ax:
                axioms[key] = ax
        return decls, axioms


def encode_ruleset(paths, members: Optional[int] = None,
                   pairwise: bool = False) -> StateEncoding:
    """Convenience wrapper: parse *paths* and return its state encoding.

    *members* overrides the array bound for multi-valued collections; when
    omitted it is derived from the ruleset (see :func:`required_members`).
    Pass ``pairwise=True`` for an encoding that will be used by a pairwise
    analysis, which asserts two rules' conditions at once and therefore needs
    twice the bound.
    """
    ruleset = Ruleset.from_paths(paths)
    return StatefulEncoder(ruleset, members=members, pairwise=pairwise).encode()
