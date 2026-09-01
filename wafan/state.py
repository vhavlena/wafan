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


def is_multi_valued(variable: SecRuleVariable) -> bool:
    """True if *variable*'s collection can hold several members at once."""
    return variable.name.upper() in MULTI_VALUED_COLLECTIONS


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

    Both are computed per target rather than globally. A single collection with
    an unbounded cardinality must not open every other one, and --- the reason
    this cannot be a global number at all --- a scalar target always has exactly
    one slot, so closing it against some other target's larger bound would make
    its own cardinality predicate unsatisfiable and the rule falsely dead.
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
                spec = _smt_var_name(v)
                multi[spec] = is_multi_valued(v)
                if v.counter:
                    if v.name.lower() in STATEFUL_COLLECTIONS:
                        continue  # TX counts come from the SSA chain, not an array
                    lower_bounds.setdefault(spec, []).append(bound)
                else:
                    per_spec[spec] += 1
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

    def script(self, assertions: Sequence[str], upto: Optional[int] = None) -> str:
        """Render a check-sat-ready SMT-LIB2 script.

        Only positions up to *upto* (inclusive) are emitted. State flows
        strictly forward, so nothing after the queried position can influence
        it — slicing here is what keeps a query proportional to the rule's
        depth in the ruleset rather than to the whole file.
        """
        limit = len(self.order) - 1 if upto is None else upto

        needed: list[str] = []
        for position, keys in self.transform_keys_by_position.items():
            if position > limit:
                continue
            for key in keys:
                if key not in needed:
                    needed.append(key)

        lines = [f"(set-logic {SMT_LOGIC})"]
        for key in needed:
            decl = self.fun_declarations_by_key.get(key)
            if decl:
                lines.append(decl)
        for key in needed:
            lines += self.axioms_by_key.get(key, [])
        lines += self.globals
        lines += self.global_definitions
        for block in self.blocks:
            if block.position > limit:
                break
            lines += block.declarations
            lines += block.definitions
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
        self._request_arrays: dict[str, tuple[list[str], list[str]]] = {}
        self._request_counters: dict[str, str] = {}
        self._transform_keys: dict[int, set[str]] = {}
        self._position: int = -1   # position currently being encoded
        # Running "the transaction has not been ended yet" term; see _reach_expr.
        self._alive: str = "true"
        self._reads_before_write: dict[TxKey, list[int]] = {}
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

    def _request_array(self, name: str, slots: int, closed: bool) -> tuple[list[str], list[str]]:
        """Declare (once) the bounded array modelling one request target.

        A target with *slots* members becomes *slots* String constants paired
        with Boolean "this member is present" flags, plus an Int count.

        Two constraints tie them together.

        *Prefix closure* --- ``live_{i+1} => live_i`` --- says the live members
        occupy a prefix. Matching is an existential over members and so is
        permutation-invariant, meaning this removes no model up to reordering;
        what it does remove is the factorial of equivalent liveness patterns
        the solver would otherwise be free to enumerate.

        *The count link* is deliberately asymmetric. If the last slot is unused
        the whole array has been modelled and the count is exact; if it is used
        there may be further members beyond the bound, so the count is only
        bounded below. When the bound covers every cardinality the ruleset asks
        for (see :func:`collections_are_closed`) the count is simply exact.
        """
        existing = self._request_arrays.get(name)
        if existing is not None:
            return existing

        values = [f"{name}_{i}" for i in range(1, slots + 1)]
        flags = [f"live_{name}_{i}" for i in range(1, slots + 1)]
        for value, flag in zip(values, flags):
            self._globals.append(f"(declare-const {value} String)")
            self._globals.append(f"(declare-const {flag} Bool)")
        for prev, cur in zip(flags, flags[1:]):
            self._global_defs.append(f"(assert (=> {cur} {prev}))")
        del slots  # the flag list is the authority from here on

        count = f"cnt_{name}"
        self._request_counters[name] = count
        self._globals.append(f"(declare-const {count} Int)")
        live_sum = "(+ " + " ".join(f"(ite {f} 1 0)" for f in flags) + ")" \
            if len(flags) > 1 else f"(ite {flags[0]} 1 0)"
        if closed:
            self._global_defs.append(f"(assert (= {count} {live_sum}))")
        else:
            self._global_defs.append(f"(assert (>= {count} {live_sum}))")
            self._global_defs.append(
                f"(assert (=> (not {flags[-1]}) (= {count} {live_sum})))"
            )

        self._request_arrays[name] = (values, flags)
        return values, flags

    def _request_counter(self, name: str) -> str:
        """Int count for ``&VAR``, declaring the backing array if needed."""
        bound = self._bound_for(name)
        self._request_array(name, bound.slots, bound.closed)
        return self._request_counters[name]

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

    def _request_atom(self, rule: SecRule, variable: SecRuleVariable, position: int) -> str:
        """Encode one request target: an existential over its live members.

        ModSecurity applies the operator to every member of a target and fires
        if any matches, so the encoding is a disjunction over the array's
        slots, each guarded by its presence flag. A single-valued target
        collapses to one slot, which is the same formula the previous model
        produced.
        """
        name = _smt_var_name(variable)
        if variable.counter:
            return self._numeric_atom(rule, self._request_counter(name), position)

        bound = self._bound_for(name)
        values, flags = self._request_array(name, bound.slots, bound.closed)
        atoms = [
            f"(and {flag} {self._string_atom(rule, value)})"
            for value, flag in zip(values, flags)
        ]
        return atoms[0] if len(atoms) == 1 else "(or " + " ".join(atoms) + ")"

    def _target_atom(self, rule: SecRule, variable: SecRuleVariable, position: int) -> str:
        collection = variable.name.lower()
        if collection in STATEFUL_COLLECTIONS and variable.part:
            key = (collection, variable.part.lower())
            if variable.counter:
                return self._numeric_atom(rule, self._cnt(key, position), position)
            term = self._val(key, position)
            if self.tx_sorts.get(key, INT) == INT:
                if effective_transforms(rule):
                    raise Abstracted(
                        f"transforms applied to Int-sorted {collection}.{variable.part}"
                    )
                return self._numeric_atom(rule, term, position)
            return self._string_atom(rule, term)
        return self._request_atom(rule, variable, position)

    def _rule_match(self, rule: SecRule, position: int) -> str:
        # A negated target (`!ARGS:foo`) excludes one member from a
        # collection. With a collection modelled by a single representative
        # there is nothing to subtract, so the exclusion is dropped: the
        # modelled match is then a superset of the real one, which is the
        # safe direction here (see the module docstring).
        atoms = [
            self._target_atom(rule, v, position)
            for v in rule.variables
            if not v.negated
        ]
        if not atoms:
            raise Abstracted("rule has no positive targets")
        return atoms[0] if len(atoms) == 1 else "(or " + " ".join(atoms) + ")"

    def _chain_match(self, chain: Sequence[SecRule], position: int) -> str:
        atoms = [self._rule_match(r, position) for r in chain]
        return atoms[0] if len(atoms) == 1 else "(and " + " ".join(atoms) + ")"

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

    def _rhs_term(self, op: SetVarOp, key: TxKey, position: int) -> str:
        sort = self.tx_sorts.get(key, INT)
        if sort == INT:
            if _rhs_is_integer(op.rhs):
                return op.rhs.strip()
            src = macro_key(op.rhs)
            if src is not None and self.tx_sorts.get(src, INT) == INT:
                return self._val(src, position)
            return self._fresh_const(INT)
        src = macro_key(op.rhs)
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
