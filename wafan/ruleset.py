"""Ordered, control-flow-aware view of a ModSecurity ruleset.

:mod:`wafan.parser` answers "which rules are in this file?". This module
answers "in what order does ModSecurity *execute* them, and what state does
each one write?" — the structure the stateful encoder in :mod:`wafan.state`
needs in order to treat ``TX`` as mutable state rather than as free input.

Three things are modelled here that ``parse_file()`` discards:

``SecAction`` / ``SecMarker``
    ``SecAction`` is an unconditional rule: it has actions (typically
    ``setvar``) but no operator, so it always fires when reached. It is where
    CRS initialises every ``tx.*`` variable, which makes it essential to
    resolving ``&TX:foo`` counters and ``%{tx.foo}`` macros. ``SecMarker`` is
    a no-op placeholder that ``skipAfter`` jumps to.

Execution order
    ModSecurity does not run rules in file order; it runs *phase by phase*,
    and within a phase in file order (see :func:`execution_order`). A phase-1
    ``setvar`` is therefore visible to every phase-2 rule regardless of where
    it sits in the file.

Control flow
    ``skipAfter:MARKER`` jumps past every directive up to and including the
    named marker; ``ctl:ruleRemoveById`` disables a rule by id; a disruptive
    action (``deny``/``drop``/``allow``/…) ends the transaction so nothing
    after it runs. Each is resolved here into an index-level *coverage*
    relation that :mod:`wafan.state` turns into a reachability condition.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Sequence

import msc_pyparser

from .parser import (
    DEFAULT_PHASE,
    SecRule,
    SecRuleAction,
    _apply_update_targets,
    _extract_phase,
    _parse_action,
    _parse_default_action,
    _parse_update_target,
    _to_secrule,
)

# Phases ModSecurity runs, in the order it runs them.
PHASES = ("1", "2", "3", "4", "5")

# Actions that end rule processing for the transaction, so nothing ordered
# after them executes. ``block`` defers to SecDefaultAction, which in CRS is a
# deny, so it is counted here too; ``pass`` explicitly does *not* terminate.
TERMINATING_ACTIONS = frozenset({"deny", "drop", "allow", "redirect", "proxy"})

# Collections whose members are written by rules (via `setvar`) rather than
# derived from the request. These are the ones `wafan.state` tracks as mutable
# state; every other collection (ARGS, REQUEST_HEADERS, …) stays free input.
#
# The split matters for the *initial* state. TX is per-transaction: it starts
# empty on every request, which is what lets wafan conclude that a rule guarded
# by a TX flag nothing sets is dead. The rest are persistent — ModSecurity backs
# them with a store that survives across requests (`SecPersistentStorage`) — so
# a previous transaction may have populated them. Assuming those start empty
# would let wafan call a rule dead that a later request can perfectly well fire,
# which is the one error direction that produces false findings.
TRANSACTION_COLLECTIONS = frozenset({"tx"})
PERSISTENT_COLLECTIONS = frozenset({"ip", "session", "user", "resource", "global"})
STATEFUL_COLLECTIONS = TRANSACTION_COLLECTIONS | PERSISTENT_COLLECTIONS


# ---------------------------------------------------------------------------
# setvar
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SetVarOp:
    """One ``setvar`` action, decomposed.

    ModSecurity's ``setvar`` argument has four forms, all present in CRS::

        setvar:tx.foo=5                 -> op="set",   rhs="5"
        setvar:'tx.foo=+%{tx.bar}'      -> op="inc",   rhs="%{tx.bar}"
        setvar:'tx.foo=-%{tx.bar}'      -> op="dec",   rhs="%{tx.bar}"
        setvar:tx.foo                   -> op="set",   rhs="1"   (implicit 1)
        setvar:!tx.foo                  -> op="unset", rhs=""

    *name* is lowercased: ModSecurity variable names are case-insensitive,
    and CRS is inconsistent about it (``tx.paranoia_level`` is written in
    lowercase but read as ``%{TX.PARANOIA_LEVEL}``).
    """

    collection: str   # "tx", "ip", …  (lowercased)
    name: str         # variable name within the collection (lowercased)
    op: str           # "set" | "unset" | "inc" | "dec"
    rhs: str          # raw right-hand side, macros unexpanded


_SETVAR_RE = re.compile(r"^(?P<bang>!)?(?P<coll>[A-Za-z_]+)\.(?P<name>[^=]+?)(?:=(?P<rhs>.*))?$")


def parse_setvar(arg: str) -> SetVarOp | None:
    """Parse a ``setvar`` action argument; return None if unrecognised."""
    m = _SETVAR_RE.match(arg.strip().strip("'\""))
    if m is None:
        return None
    coll = m.group("coll").lower()
    name = m.group("name").strip().lower()
    if m.group("bang"):
        return SetVarOp(coll, name, "unset", "")
    rhs = m.group("rhs")
    if rhs is None or rhs == "":
        # `setvar:tx.foo` with no value sets it to 1.
        return SetVarOp(coll, name, "set", "1")
    rhs = rhs.strip()
    if rhs.startswith("+"):
        return SetVarOp(coll, name, "inc", rhs[1:].strip())
    if rhs.startswith("-"):
        return SetVarOp(coll, name, "dec", rhs[1:].strip())
    return SetVarOp(coll, name, "set", rhs)


# ---------------------------------------------------------------------------
# Directives
# ---------------------------------------------------------------------------

@dataclass
class Directive:
    """One executable unit of a ruleset, in file order.

    A ``"rule"`` directive holds a whole chain (a non-chained rule is a chain
    of one), matching :func:`wafan.parser.group_chains`, because ModSecurity
    executes a chain as a single unit: its actions run only if every link
    matches.
    """

    kind: str                                     # "rule" | "action" | "marker"
    index: int                                    # position in file order
    lineno: int
    chain: list[SecRule] = field(default_factory=list)
    actions: list[SecRuleAction] = field(default_factory=list)
    inherited_actions: list[SecRuleAction] = field(default_factory=list)
    marker: str = ""
    phase: str = DEFAULT_PHASE
    source_path: Path | None = None

    # ---- derived views over `actions` -------------------------------------

    @property
    def rule_id(self) -> str:
        if self.chain:
            return self.chain[0].rule_id
        for a in self.actions:
            if a.name == "id":
                return a.arg
        return ""

    @property
    def setvars(self) -> list[SetVarOp]:
        """Every ``setvar`` this directive performs when it fires.

        msc_pyparser represents a ``setvar`` argument in one of two shapes
        depending on quoting: ``setvar:'tx.foo=+1'`` arrives whole in
        ``act_arg``, while unquoted ``setvar:tx.foo=+1`` is split into
        ``act_arg`` (``tx.foo``) and ``act_arg_val`` (``+1``). Both forms
        occur in CRS, so the two halves are rejoined before parsing —
        otherwise an unquoted increment silently degrades into a bare "set to
        1".
        """
        ops = []
        for a in self.actions:
            if a.name != "setvar":
                continue
            spec = a.arg
            if "=" not in spec and a.arg_value:
                spec = f"{spec}={a.arg_value}"
            op = parse_setvar(spec)
            if op is not None:
                ops.append(op)
        return ops

    @property
    def skip_after(self) -> str:
        for a in self.actions:
            if a.name == "skipAfter":
                return a.arg
        return ""

    @property
    def skip_count(self) -> int:
        """``skip:N`` — skip the next N directives. 0 when absent."""
        for a in self.actions:
            if a.name == "skip":
                try:
                    return int(a.arg)
                except ValueError:
                    return 0
        return 0

    @property
    def removes_rule_ids(self) -> list[str]:
        """Rule ids disabled by ``ctl:ruleRemoveById`` on this directive.

        ``ruleRemoveById`` accepts a single id or an inclusive ``a-b`` range.
        """
        ids: list[str] = []
        for a in self.actions:
            if a.name != "ctl" or a.arg != "ruleRemoveById":
                continue
            for token in re.split(r"[,\s]+", a.arg_value):
                token = token.strip()
                if not token:
                    continue
                lo, sep, hi = token.partition("-")
                if sep and lo.isdigit() and hi.isdigit():
                    ids.extend(str(i) for i in range(int(lo), int(hi) + 1))
                elif token.isdigit():
                    ids.append(token)
        return ids

    @property
    def removes_targets(self) -> bool:
        """True if this directive conditionally removes a *target* from a rule.

        ``ctl:ruleRemoveTargetById`` / ``ruleRemoveTargetByTag`` shrink another
        rule's variable list at runtime. :mod:`wafan.state` does not model
        that (it would make a rule's variable set path-dependent); the flag
        exists so the encoder can report the resulting imprecision instead of
        silently ignoring it.
        """
        return any(
            a.name == "ctl" and a.arg in ("ruleRemoveTargetById", "ruleRemoveTargetByTag")
            for a in self.actions
        )

    @property
    def terminates(self) -> bool:
        """True if firing this directive certainly ends rule processing.

        Deliberately biased towards False. Claiming a directive terminates
        when it does not would make everything ordered after it look
        unreachable, which is the one direction that produces *false* dead-rule
        reports; the opposite error only costs precision. So termination is
        asserted only when an explicit disruptive action says so.

        ``block`` is not itself disruptive — it defers to the governing
        ``SecDefaultAction``, which in CRS is ``pass`` — so it terminates only
        when the inherited actions make it a deny.
        """
        names = {a.name for a in self.actions}
        if names & TERMINATING_ACTIONS:
            return True
        if "pass" in names:
            return False
        inherited = {a.name for a in self.inherited_actions}
        if "block" in names:
            return bool(inherited & TERMINATING_ACTIONS)
        if inherited & TERMINATING_ACTIONS:
            return True
        # No explicit disruptive action anywhere: ModSecurity's built-in
        # default is `pass`, which does not terminate.
        return False

    def label(self) -> str:
        if self.kind == "marker":
            return f"SecMarker {self.marker}"
        if self.kind == "action":
            return f"SecAction #{self.rule_id or '?'}"
        from .analyses.common import _chain_label

        return _chain_label(self.chain, pat_width=50)


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def parse_directives(paths: str | Path | Sequence[str | Path]) -> list[Directive]:
    """Parse one or more ``.conf`` files into an ordered directive list.

    Multiple paths are concatenated in the order given, which is how
    ModSecurity treats multiple ``Include`` directives — so passing
    ``crs-setup.conf`` ahead of the rule files makes its ``SecAction``
    initialisers visible to every rule that reads them.

    ``SecDefaultAction`` inheritance and ``SecRuleUpdateTargetById`` are
    applied exactly as in :func:`wafan.parser.parse_file`, except that both
    now carry across files in the sequence.
    """
    if isinstance(paths, (str, Path)):
        paths = [paths]

    directives: list[Directive] = []
    all_rules: list[SecRule] = []
    updates: list = []
    default_actions: dict[str, list[SecRuleAction]] = {}
    pending: list[SecRule] = []          # chain links accumulated so far
    pending_actions: list[SecRuleAction] = []
    pending_inherited: list[SecRuleAction] = []
    pending_lineno = 0

    for path in paths:
        conf_path = Path(path)
        parser = msc_pyparser.MSCParser()
        parser.parser.parse(conf_path.read_text(), lexer=msc_pyparser.MSCLexer().lexer)

        for entry in parser.configlines:
            etype = entry.get("type")

            if etype == "SecRule":
                rule = _to_secrule(entry, source_path=conf_path)
                rule.inherited_actions = list(default_actions.get(rule.phase, []))
                all_rules.append(rule)
                actions = [_parse_action(a) for a in entry.get("actions", [])]
                if not pending:
                    pending_lineno = rule.lineno
                    pending_inherited = list(rule.inherited_actions)
                pending.append(rule)
                pending_actions.extend(actions)
                if not rule.chained:
                    directives.append(
                        Directive(
                            kind="rule",
                            index=len(directives),
                            lineno=pending_lineno,
                            chain=pending,
                            actions=pending_actions,
                            inherited_actions=pending_inherited,
                            phase=pending[0].phase,
                            source_path=conf_path,
                        )
                    )
                    pending, pending_actions, pending_inherited = [], [], []

            elif etype == "SecAction":
                actions = [_parse_action(a) for a in entry.get("actions", [])]
                phase = _extract_phase(actions)
                directives.append(
                    Directive(
                        kind="action",
                        index=len(directives),
                        lineno=entry.get("lineno", 0),
                        actions=actions,
                        inherited_actions=list(default_actions.get(phase, [])),
                        phase=phase,
                        source_path=conf_path,
                    )
                )

            elif etype == "SecMarker":
                args = entry.get("arguments", [])
                directives.append(
                    Directive(
                        kind="marker",
                        index=len(directives),
                        lineno=entry.get("lineno", 0),
                        marker=args[0]["argument"] if args else "",
                        source_path=conf_path,
                    )
                )

            elif etype == "SecDefaultAction":
                phase, actions = _parse_default_action(entry)
                default_actions[phase] = actions

            elif etype == "SecRuleUpdateTargetById":
                updates.append(_parse_update_target(entry))

    if pending:  # unterminated chain at EOF
        directives.append(
            Directive(
                kind="rule",
                index=len(directives),
                lineno=pending_lineno,
                chain=pending,
                actions=pending_actions,
                inherited_actions=pending_inherited,
                phase=pending[0].phase,
            )
        )

    _apply_update_targets(all_rules, updates)
    return directives


# ---------------------------------------------------------------------------
# Execution order and control flow
# ---------------------------------------------------------------------------

def execution_order_with_phases(
    directives: Sequence[Directive],
) -> tuple[list[Directive], list[str]]:
    """Like :func:`execution_order`, but also return each position's phase.

    Needed because a ``SecMarker`` appears once per phase, so the marker object
    alone does not say which phase pass a given position belongs to — and
    ``skipAfter`` may only jump forward *within* its own phase.
    """
    ordered: list[Directive] = []
    phases: list[str] = []
    for phase in PHASES:
        for d in directives:
            if d.kind == "marker" or d.phase == phase:
                ordered.append(d)
                phases.append(phase)
    return ordered, phases


def execution_order(directives: Sequence[Directive]) -> list[Directive]:
    """Return *directives* in the order ModSecurity executes them.

    Rules are grouped by phase (1 through 5) and kept in file order within
    each phase. ``SecMarker`` directives have no phase of their own — they are
    positional landmarks — so each marker appears in *every* phase's
    subsequence at its file position, which is what makes a phase-2
    ``skipAfter`` able to target a marker written between phase-1 rules.

    The result is a single linear sequence: TX state written in phase 1 is
    therefore visible to phase 2 without any extra plumbing, and a phase-1
    ``deny`` correctly cuts off everything after it.
    """
    return execution_order_with_phases(directives)[0]


@dataclass
class ControlFlow:
    """Which directives each control-flow event suppresses.

    ``blocked_by`` maps a position in the execution sequence to the positions
    whose firing prevents it from running. ``terminators`` lists positions
    whose firing ends the transaction, suppressing everything after them.
    """

    blocked_by: dict[int, list[int]]
    terminators: list[int]


def resolve_control_flow(
    order: Sequence[Directive], phases: Sequence[str] | None = None
) -> ControlFlow:
    """Resolve ``skipAfter`` / ``skip`` / ``ctl:ruleRemoveById`` over *order*.

    *order* must already be in execution order (see :func:`execution_order`);
    *phases* is the parallel phase list from
    :func:`execution_order_with_phases`. Without it, phase boundaries are not
    enforced.

    - ``skipAfter:M`` at position *i* covers positions ``i+1 … m``, where *m*
      is the position of the next ``SecMarker M`` after *i* **in the same
      phase**. ModSecurity only searches forward, and rule processing is
      per-phase, so a marker that sits behind the skipping rule (or in a later
      phase) is not a valid target: the skip then runs out at the end of the
      phase and is treated as covering nothing.
    - ``skip:N`` at position *i* covers the next *N* rule positions in the
      same phase.
    - ``ctl:ruleRemoveById=X`` at position *i* covers every later position
      whose rule id is X. This one *does* cross phases: the removal holds for
      the rest of the transaction.

    Nested skips need no special handling: an inner ``skipAfter`` can only
    suppress anything if it fires, and its own firing condition already
    includes not being suppressed by the outer one.
    """
    if phases is None:
        phases = [d.phase for d in order]
    blocked: dict[int, list[int]] = {i: [] for i in range(len(order))}
    terminators: list[int] = []

    marker_positions: dict[str, list[int]] = {}
    for pos, d in enumerate(order):
        if d.kind == "marker":
            marker_positions.setdefault(d.marker, []).append(pos)

    id_positions: dict[str, list[int]] = {}
    for pos, d in enumerate(order):
        if d.kind != "marker" and d.rule_id:
            id_positions.setdefault(d.rule_id, []).append(pos)

    for pos, d in enumerate(order):
        if d.kind == "marker":
            continue

        if d.terminates:
            terminators.append(pos)

        target = d.skip_after
        if target:
            later = [
                m for m in marker_positions.get(target, [])
                if m > pos and phases[m] == phases[pos]
            ]
            if later:
                for k in range(pos + 1, later[0] + 1):
                    blocked[k].append(pos)

        n = d.skip_count
        if n > 0:
            remaining = n
            k = pos + 1
            while k < len(order) and remaining > 0 and phases[k] == phases[pos]:
                if order[k].kind != "marker":
                    blocked[k].append(pos)
                    remaining -= 1
                k += 1

        for rid in d.removes_rule_ids:
            for k in id_positions.get(rid, []):
                if k > pos:
                    blocked[k].append(pos)

    return ControlFlow(blocked_by=blocked, terminators=terminators)


@dataclass
class Ruleset:
    """A parsed ruleset with its execution order and control flow resolved."""

    directives: list[Directive]
    order: list[Directive]
    control_flow: ControlFlow
    # Phase of each position in `order`; a SecMarker appears once per phase, so
    # its position's phase cannot be read off the Directive itself.
    order_phases: list[str] = field(default_factory=list)

    @classmethod
    def from_paths(cls, paths: str | Path | Sequence[str | Path]) -> "Ruleset":
        directives = parse_directives(paths)
        order, phases = execution_order_with_phases(directives)
        return cls(directives, order, resolve_control_flow(order, phases), phases)

    def unresolved_markers(self) -> list[str]:
        """``skipAfter`` targets with no matching ``SecMarker`` in the ruleset.

        Note this checks only that the name exists somewhere. A marker that
        exists but sits *behind* its skipping rule is a separate case: the skip
        is real but reaches the end of the phase, so it suppresses nothing that
        can be pinned to an index (see :func:`resolve_control_flow`).
        """
        known = {d.marker for d in self.directives if d.kind == "marker"}
        missing = {
            d.skip_after
            for d in self.directives
            if d.kind != "marker" and d.skip_after and d.skip_after not in known
        }
        return sorted(missing)

    def setvar_writers(self) -> dict[tuple[str, str], list[Directive]]:
        """Map ``(collection, name)`` to every directive that writes it."""
        writers: dict[tuple[str, str], list[Directive]] = {}
        for d in self.order:
            for op in d.setvars:
                writers.setdefault((op.collection, op.name), []).append(d)
        return writers

    def rule_directives(self) -> Iterable[Directive]:
        return (d for d in self.order if d.kind == "rule")
