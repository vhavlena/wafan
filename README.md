# wafan

[![Test](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml/badge.svg)](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml)

**wafan** analyses ModSecurity WAF rule files with an SMT solver. Point it at your
`.conf` files and it answers questions you cannot check by eye: which rules are
redundant, which overlap, which can never fire, and what request triggers a given
rule. Rule conditions are translated into formulas over the theory of strings, and
the solver returns a proof or a counterexample.

## Install

```bash
python -m venv .venv && source .venv/bin/activate
pip install .
```

Regex rules (`@rx`) need [z3-noodler](https://github.com/VeriFIT/z3-noodler), which
supports the ECMA 2020 regex dialect ModSecurity uses; mainstream `z3` handles only
the non-regex operators. You don't have to install it: on first run wafan downloads
a prebuilt binary for your platform (Linux x86_64, macOS arm64/x86_64) and caches it
under `~/.cache/wafan` (`~/Library/Caches/wafan` on macOS). Run
`wafan-download-solver` to pre-fetch it (CI, Docker builds), or `--no-auto-solver`
to use `--solver`/`WAFAN_Z3_PATH`/`z3` instead.

## Usage

```
wafan [options] <conf> [<conf> ...]
```

Pass the `.conf` files **in the order the web server includes them** — `crs-setup.conf`
first, so its `SecAction` initialisers are visible to the rules that read them.

| Option | Default | Description |
|---|---|---|
| `--analysis` | `subsumption` | `subsumption`, `intersection`, `contradiction`, `witness` or `reachability` |
| `--stateful` | off | Analyse the ruleset as an ordered program with `TX` as mutable state; `reachability` implies it |
| `--include-actions` | off | Also analyse `SecAction` directives, not just rules |
| `--solver PATH` | *(auto)* | Solver binary; falls back to `WAFAN_Z3_PATH`, the downloaded z3-noodler, then `z3` |
| `--no-auto-solver` | off | Never download a solver |
| `--solver-args ARGS` | *(none)* | Extra flags forwarded to the solver |
| `--timeout SEC` | `30` | Per-query solver time limit |
| `--json` | off | Newline-delimited JSON instead of a report, flushed per result — for batch runs |
| `-v` / `-v2` | off | Print each pair and its verdict; `-v2` also prints the SMT formula |

## Analyses

| Analysis | Question |
|---|---|
| `subsumption` | Does rule B match every member rule A matches? Then A is redundant. |
| `intersection` | Is there one member both rules match? |
| `contradiction` | Do they overlap *and* disagree — one accepts, the other denies? |
| `witness` | What concrete input triggers each rule? |
| `reachability` | Can this rule ever fire at all? |

```console
$ wafan rules/01-subsumption-basic.conf --analysis subsumption
Subsumed pairs  (4 found)

  #1100 [ARGS @rx "select"]
    ⊆  #1200 [ARGS @rx "select|insert|delete"]
  #1300 [ARGS @rx "union"]
    ⊆  #1400 [ARGS @rx ".+"]
  ...

8 pair(s) checked and found not subsumed.

$ wafan rules/01-subsumption-basic.conf --analysis witness
Concrete triggering inputs  (4 rule(s))

  #1100 [ARGS @rx "select"]
    ARGS = 'select'
  ...
```

### Overlap is about members, not requests

A rule's condition is existential over the members its targets resolve to, so
"both rules fire" is weaker than "both rules match the same thing". Two rules on
`ARGS` both fire on `?x=select&y=union` while matching different arguments; two
rules on unrelated targets both fire on a request that happens to satisfy each.
Neither is an overlap, so the queries ask for a **shared witness**:

- `ARGS:id` and `ARGS:user` never intersect — no member is named both.
- `ARGS:id` does intersect `ARGS`, on a member named `id` matching both patterns,
  and is *subsumed* by it: the same members, filtered.
- `ARGS|REQUEST_URI` against `REQUEST_URI|REQUEST_HEADERS` intersects only if one
  URI satisfies both patterns.
- Rules sharing no target are reported disjoint (for subsumption, skipped) without
  a solver call: with no member in common the verdict is already settled.

The solver decides all of this, rather than a comparison of target names: every
spec on a collection reads the same member, with a selector as a constraint on its
name (`ARGS:/^id/` against `ARGS:idx` is a regex question). A `&` count is the
exception — it reads how many members there are, not what one of them says, so it
never supplies a shared witness. For subsumption, coverage is judged where B
looks: a chain guarded on `TX:flag` is still subsumed by the plain rule repeating
its pattern, since deleting it changes no verdict.

## Stateful analysis

By default rules are compared over free variables — right for request-derived
targets like `ARGS`, whose values a client picks freely, wrong for `TX`, which
exists only because an earlier rule ran `setvar`. `--stateful` (and
`reachability`, which always uses it) instead walks the ruleset in ModSecurity's
execution order and derives, per directive,

```
fire_p  = reach_p ∧ match_p
reach_p = no earlier rule ended the transaction, and nothing skipped or removed p
```

with `TX` in SSA form, so each write is a new version guarded by its writer's own
firing condition: `v_tx_score_2 = (ite fire_17 (+ v_tx_score_1 5) v_tx_score_1)`.

| Construct | Handling |
|---|---|
| Execution order | Phases 1→5, file order within a phase |
| `SecAction` | Fires whenever reached, running its `setvar` initialisers |
| `skipAfter:M` / `SecMarker` / `skip:N` | Firing the skip suppresses what it jumps over |
| `ctl:ruleRemoveById=X` | Suppresses rule `X` for the rest of the transaction |
| `deny` / `drop` / `allow` / `redirect` / `proxy` | Ends the transaction |
| `setvar:tx.x=V`, `=+V`, `=-V`, `!tx.x` | New SSA version; typed `Int` or `String` by inference |
| `&TX:x`, `%{tx.x}` | Count and value at the reader's position — including as an operator argument, which is what makes `@lt %{tx.threshold}` analysable |
| `ARGS`, `REQUEST_HEADERS`, … | Bounded array of members; scalars like `REQUEST_METHOD` stay single-valued |
| `IP` / `SESSION` / `USER` / `GLOBAL` | Like `TX`, but with an **unknown** initial state — ModSecurity persists them across requests |

Only `TX` is assumed to start empty; pinning a persistent collection to 0 would let
wafan call a rule dead that a later request can fire.

For pairs, `contradiction` changes shape rather than precision: in an ordered model
two disruptive rules can never both fire, since the first ends the transaction, so
the query becomes **shadowing** — "A fires on a request B would also have matched".
The member-level readings above carry over, a member here being a *slot* of a
collection's array (or a name, for `TX`).

### Reachability

Separates **unreachable** (control flow never gets there) from
**impossible_match** (it runs, but the condition cannot hold given the state the
ruleset can produce). In this `example.conf`, nothing writes `tx.crs_setup_version`,
so the guard holds, the skip fires, and the initialiser it jumps over never runs:

```apache
SecRule &TX:crs_setup_version "@eq 0" "id:901001,phase:1,pass,skipAfter:END-SETUP"
SecAction                             "id:901100,phase:1,pass,setvar:tx.paranoia_level=1"
SecMarker "END-SETUP"
SecRule TX:paranoia_level "@ge 2"     "id:942100,phase:2,deny"
```

```console
$ wafan example.conf --analysis reachability
Dead rules  (1 of 2 checked)

  Executed, but the condition can never hold:
    #942100 [TX:paranoia_level @ge "2"]  line 4
```

`SecAction`s are excluded by default — being unconditional, their reachability is a
fact about control flow rather than about the directive. `--include-actions` checks
them too, which is usually what explains the dead rules downstream: here the skip
above `#901100` means its `setvar` never runs, which is *why* `#942100`'s guard can
never hold.

```console
$ wafan example.conf --analysis reachability --include-actions
Dead directives  (2 of 3 checked)

  Never executed (control flow):
    SecAction #901100  line 2

  Executed, but the condition can never hold:
    #942100 [TX:paranoia_level @ge "2"]  line 4
```

Reachability costs O(n) solver calls, which makes it the practical first pass over
a large ruleset: run it, then point the `--stateful` pairwise analyses at what it
flagged.

### Collections as bounded arrays

ModSecurity applies an operator to *every* member of a target, so a collection is a
list of `(name, value)` pairs and not one value: `?x=a&y=b` fires a chain demanding
`ARGS "@streq a"` and `ARGS "@streq b"`, which a single-value model reports dead.
Each multi-valued collection therefore becomes `k` slots carrying a value, a name
and a presence flag, and a match is a disjunction over the live ones. `ARGS`,
`ARGS:id`, `ARGS:/re/`, `!ARGS:/re/` and `ARGS_NAMES` all read that one array,
which is what makes `ARGS:id ⊆ ARGS` and `&ARGS = &ARGS_NAMES` hold by
construction; scalars keep a single value, so no chain can demand a request that is
both `GET` and `POST`. `k` is derived per target from the widest chain and any
literal cardinality bound — past a small ceiling a target stays *open* instead, its
count bounded below rather than exact, and each run names the targets affected. See
`wafan/state.py` for the derivation and `wafan/targets.py` for how specs resolve.

### Soundness and cost

Anything the encoder cannot model faithfully — an unsupported operator, an
unresolvable macro, `ctl:ruleRemoveTargetById` — is over-approximated, so **a rule
reported dead is genuinely dead**, while a rule reported live may only be beyond
the model's precision. Such results carry an `approximate` flag, and each run
prints its caveats:

```
note: 4 directive(s) abstracted to a free Boolean (unsupported construct); they are assumed able to fire
```

Most CRS files finish well under a second. The slow ones are dominated by
individual hard queries — a large `@pmFromFile` phrase list, or `t:urlDecodeUni`,
whose precise definition is one rewrite pass per BMP codepoint. Cap them with
`--timeout`.

## Supported rule features

**Operators:** `@rx`, `@streq`, `@contains`, `@beginsWith`, `@endsWith`, `@within`,
`@pm`, `@pmFromFile`, and `@eq`/`@ge`/`@gt`/`@le`/`@lt`, each with optional `!`.

**Transforms (`t:`):** exact in SMT — `lowercase`, `uppercase`, `urlDecode`,
`urlDecodeUni`, `htmlEntityDecode`, `none`; approximated by uninterpreted functions
with partial axioms — `trim`, `trimLeft`, `trimRight`, `removeWhitespace`,
`compressWhitespace`, `removeNulls`, `normalizePath`, `normalizePathWin`.

**Chains:** a chain is one unit that fires only when every link matches.

Rules using anything unsupported are skipped and reported as unknown.

## OWASP Core Rule Set

`owasp-rules/` holds the CRS files, `rules/` small annotated examples.

```bash
wafan crs-setup.conf owasp-rules/REQUEST-942-APPLICATION-ATTACK-SQLI.conf \
      --analysis intersection -v
```

A large file means many pairwise checks, so start with `reachability` and use
`--timeout`.
