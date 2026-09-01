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

    def __init__(self, ruleset: Ruleset) -> None:
        self.rs = ruleset
        self.order = ruleset.order
        self.cf = ruleset.control_flow
        self.tx_sorts = infer_tx_sorts(ruleset)

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
        self._request_vars: set[str] = set()
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

    def _request_var(self, name: str) -> None:
        if name not in self._request_vars:
            self._request_vars.add(name)
            self._globals.append(f"(declare-const {name} String)")

    def _request_counter(self, name: str) -> str:
        """Free non-negative Int modelling ``&VAR`` for a request collection.

        Unlike ``TX``, the size of a request collection is chosen by the
        client, so it stays free. It is still tied to the value targets: a
        collection with no members cannot match anything, which is what the
        ``(> cnt 0)`` guard in :meth:`_request_atom` expresses.
        """
        sym = self._request_counters.get(name)
        if sym is None:
            sym = f"cnt_{name}"
            self._request_counters[name] = sym
            self._globals.append(f"(declare-const {sym} Int)")
            self._global_defs.append(f"(assert (>= {sym} 0))")
        return sym

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
        name = _smt_var_name(variable)
        counter = self._request_counter(name)
        if variable.counter:
            return self._numeric_atom(rule, counter, position)
        self._request_var(name)
        atom = self._string_atom(rule, name)
        # A collection with no members has nothing for the operator to match.
        return f"(and (> {counter} 0) {atom})"

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


def encode_ruleset(paths) -> StateEncoding:
    """Convenience wrapper: parse *paths* and return its state encoding."""
    return StatefulEncoder(Ruleset.from_paths(paths)).encode()
