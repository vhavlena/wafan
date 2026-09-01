# wafan

[![Test](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml/badge.svg)](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml)

**wafan** is a command-line tool for analysing ModSecurity WAF rule files. Given a `.conf` file containing `SecRule` directives, it automatically checks whether rules overlap, subsume each other, or can be triggered at all — helping you catch redundancies, dead rules, and unexpected interactions before they affect a live deployment.

## What it does

WAF rule sets grow large quickly, and subtle interactions between rules are hard to spot by eye. wafan uses an SMT solver to answer three questions about any pair of rules:

- **Subsumption** — Is every request that triggers rule A also guaranteed to trigger rule B? If so, rule A is redundant given rule B (everything A blocks, B already blocks).
- **Intersection** — Is there any request that triggers both rules at the same time? Overlapping rules may indicate redundancy or conflicting actions.
- **Contradiction** — Like intersection, but does it also matter: is there a shared request where one rule accepts (`allow`/`pass`) and the other denies (`deny`/`drop`/`block`)? This flags genuine conflicts, not just harmless overlap.
- **Witness** — What is a concrete example request that triggers each rule? This lets you verify a rule behaves as intended and generate test cases.
- **Reachability** — Can this rule ever fire at all? Some rules are dead code: control flow always jumps over them, or they are guarded by a `TX` variable that no rule in the ruleset ever sets.

The tool parses the rule file, translates each rule's matching conditions into a logical formula, and asks an SMT solver to find a proof or a counterexample. Results are printed directly to the terminal.

### Two modes

By default wafan compares rules' **match conditions** in isolation, over free
variables — the right model for request-derived targets like `ARGS`, whose
values an attacker picks freely. It is the wrong model for `TX`: a `TX` variable
exists only because some earlier rule ran `setvar:tx.…`, so treating it as free
lets the solver invent state no rule can produce.

`--stateful` (and `--analysis reachability`, which always uses it) instead walks
the ruleset in ModSecurity's execution order with `TX` as mutable state, and
compares rules on whether they can actually both *fire*. See
[Stateful analysis](#stateful-analysis).

## Requirements

- Python ≥ 3.10
- [z3-noodler](https://github.com/VeriFIT/z3-noodler) — an SMT solver with full support for the ECMA 2020 regex standard used by ModSecurity `@rx` rules. Standard `z3` works only for rules using non-regex operators (`@streq`, `@contains`, etc.).

  You don't need to install it yourself: on first run, wafan automatically downloads a prebuilt `z3-noodler` binary matching your platform (Linux x86_64, macOS arm64, or macOS x86_64) and caches it under `~/.cache/wafan` (`~/Library/Caches/wafan` on macOS). On other platforms (e.g. Windows, Linux ARM), or if the download fails, wafan falls back to a `z3` binary on `PATH`. Use `--no-auto-solver` to skip the download and always use `--solver`/`WAFAN_Z3_PATH`/`z3`.

  To pre-fetch the binary ahead of time (e.g. in a CI job or Docker image build, so the first real run doesn't need network access), run:

  ```bash
  wafan-download-solver
  ```

  Pass `--version TAG` to fetch a specific z3-noodler release instead of the pinned default (or set `WAFAN_Z3_NOODLER_VERSION`).

## Installation

```bash
python -m venv .venv && source .venv/bin/activate
pip install .
```

After installation the `wafan` command is available in the activated virtual environment. You can also run it without installing: `python -m wafan`.

## Usage

```
wafan [options] <conf> [<conf> ...]
```

| Argument | Default | Description |
|---|---|---|
| `conf` | *(required)* | Path(s) to ModSecurity `.conf` file(s), **in the order the web server includes them**. Put `crs-setup.conf` first so its `SecAction` initialisers are visible to the rules that read them. |
| `--analysis` | `subsumption` | Which analysis to run: `subsumption`, `intersection`, `contradiction`, `witness`, or `reachability` |
| `--stateful` | off | Analyse the ruleset as an ordered program with `TX` as mutable state (see [Stateful analysis](#stateful-analysis)). Applies to `subsumption`/`intersection`/`contradiction`; `reachability` implies it. |
| `--solver PATH` | *(auto)* | Path to the SMT solver binary. Falls back to the `WAFAN_Z3_PATH` environment variable, then an auto-downloaded `z3-noodler` build, then `z3` on `PATH`. |
| `--no-auto-solver` | off | Disable the automatic `z3-noodler` download; use `--solver`/`WAFAN_Z3_PATH`/`z3` instead |
| `--solver-args ARGS` | *(none)* | Extra space-separated flags forwarded to the solver |
| `--timeout SEC` | `30` | Per-query solver time limit in seconds |
| `-v` | off | Verbose: print each rule (pair) being checked and its result |
| `-v2` | off | Like `-v`, but also print the raw SMT formula for each query |

## Analyses

### Subsumption

Finds rule pairs where one rule's trigger set is entirely contained within another's. If rule R1 is subsumed by rule R2 (written R1 ⊆ R2), then every request that matches R1 also matches R2. This often indicates a redundant, overly specific rule.

```bash
wafan rules/my-rules.conf --solver z3-noodler --analysis subsumption
```

Example output:
```
Subsumed pairs  (2 found)

  ARGS @rx ^select$  [id:1100]
    ⊆  ARGS @rx select|insert|delete  [id:1200]

  ARGS @rx select|insert|delete  [id:1200]
    ⊆  ARGS @rx .+  [id:1400]

4 pair(s) checked and found not subsumed.
```

### Intersection

Finds rule pairs that share at least one common triggering input. Intersecting rules may indicate redundancy or — when the rules have conflicting actions — unexpected behaviour.

```bash
wafan rules/my-rules.conf --solver z3-noodler --analysis intersection
```

Example output:
```
Intersecting pairs  (4 found)

  ARGS @rx select  [id:1100]
    ∩  ARGS @rx select|insert|delete  [id:1200]

  ARGS @rx select  [id:1100]
    ∩  ARGS @rx .+  [id:1400]

  ...

2 pair(s) checked and found disjoint.
```

### Contradiction

Like intersection, but with an extra check: it only flags a pair if the two rules also disagree on what to do with the shared input — one rule's actions accept it (`allow`/`pass`) while the other's deny it (`deny`/`drop`/`block`). This surfaces genuine conflicts between rules rather than mere harmless overlap.

```bash
wafan rules/my-rules.conf --solver z3-noodler --analysis contradiction
```

Example output:
```
Contradicting pairs  (1 found)

  ARGS @rx select  [id:1100]  [deny]
    ⨯  ARGS @rx .+  [id:1450]  [allow]

3 intersecting pair(s) with no action conflict, 2 disjoint pair(s) checked.
```

### Witness

Finds a concrete example string that would trigger each rule. Useful for writing test cases, verifying that a new rule actually fires, or understanding what a complex regex matches in practice.

```bash
wafan rules/my-rules.conf --solver z3-noodler --analysis witness
```

Example output:
```
Concrete triggering inputs  (3 rule(s))

  ARGS @rx select  [id:1100]
    ARGS = "select"

  ARGS @rx select|insert|delete  [id:1200]
    ARGS = "select"

  ARGS @rx .+  [id:1400]
    ARGS = "a"

Rules that never match  (0)
```

## Worked example

The `rules/` directory contains annotated example rule files. Here is a complete walkthrough using `rules/01-subsumption-basic.conf`, which defines four SQL-keyword detection rules:

```apache
SecRule ARGS "@rx select"          "id:1100, phase:2, deny"
SecRule ARGS "@rx select|insert|delete"  "id:1200, phase:2, deny"
SecRule ARGS "@rx union"           "id:1300, phase:2, deny"
SecRule ARGS "@rx .+"              "id:1400, phase:2, deny"
```

**Find all overlapping rule pairs:**

```bash
wafan rules/01-subsumption-basic.conf --solver z3-noodler --analysis intersection -v
```

```
Loaded 4 rules from rules/01-subsumption-basic.conf
──────────────────────────────────────────────────────────────────
Intersecting pairs  (4 found)

  ARGS @rx select  [id:1100]
    ∩  ARGS @rx select|insert|delete  [id:1200]

  ARGS @rx select  [id:1100]
    ∩  ARGS @rx .+  [id:1400]

  ARGS @rx select|insert|delete  [id:1200]
    ∩  ARGS @rx .+  [id:1400]

  ARGS @rx union  [id:1300]
    ∩  ARGS @rx .+  [id:1400]

2 pair(s) checked and found disjoint.
```

This immediately shows that rule 1400 (`.+`) overlaps with everything — it is a catch-all that fires on any non-empty input. Rules 1100 and 1300 are disjoint (a request containing "select" will never contain only "union" and vice versa).

**Generate example triggering inputs:**

```bash
wafan rules/01-subsumption-basic.conf --solver z3-noodler --analysis witness
```

```
Concrete triggering inputs  (4 rule(s))

  ARGS @rx select  [id:1100]
    ARGS = "select"

  ARGS @rx select|insert|delete  [id:1200]
    ARGS = "select"

  ARGS @rx union  [id:1300]
    ARGS = "union"

  ARGS @rx .+  [id:1400]
    ARGS = "a"
```

## Stateful analysis

`--stateful` and `--analysis reachability` model the ruleset as an ordered
program instead of a bag of independent match conditions. For every directive
the encoder derives when it actually fires:

```
fire_p  = reach_p ∧ match_p
reach_p = no earlier rule ended the transaction, and nothing skipped or removed p
```

`TX` is tracked as mutable state in SSA form, so each `setvar` creates a new
version guarded by the writing rule's own firing condition:

```
v_tx_score_2 = (ite fire_17 (+ v_tx_score_1 5) v_tx_score_1)
```

**What is modelled**

| Construct | Handling |
|---|---|
| Execution order | Grouped by phase (1→5), file order within a phase — so a phase-1 `setvar` reaches every phase-2 rule |
| `SecAction` | Unconditional rule: fires whenever reached, running its `setvar` initialisers |
| `skipAfter:M` / `SecMarker` / `skip:N` | Firing the skip suppresses the directives it jumps over |
| `ctl:ruleRemoveById=X` | Suppresses rule `X` for the rest of the transaction |
| `deny` / `drop` / `allow` / `redirect` / `proxy` | Ends the transaction, so nothing after it runs |
| `setvar:tx.x=V`, `=+V`, `=-V`, `!tx.x` | New SSA version; values typed `Int` or `String` by inference over their writes |
| `&TX:x` and `%{tx.x}` | Count and value of `tx.x`, resolved to the version current at the reader — including as an operator argument, which is what makes `@lt %{tx.threshold}` analysable |
| `IP` / `SESSION` / `USER` / `GLOBAL` / `RESOURCE` | Tracked like `TX`, but with an **unknown** initial state: ModSecurity persists these across requests |

Only `TX` is assumed to start empty. That asymmetry keeps the analysis sound in
the direction that matters — pinning a persistent collection to 0 would let
wafan declare a rule dead that a later request can fire.

### Reachability

Finds rules that can never fire, separating **`unreachable`** (control flow
never gets there) from **`impossible_match`** (it runs, but the condition cannot
hold given the state the ruleset can actually produce).

```bash
wafan crs-setup.conf owasp-rules/REQUEST-901-INITIALIZATION.conf --analysis reachability
```

```
Dead rules  (16 of 30 checked)

  Never executed (control flow):
    #901410 [UNIQUE_ID @rx "^."]  line 376
    ...
  Executed, but the condition can never hold:
    #901001 [TX @eq "0"]  line 53
    ...
```

Include order matters: analysed alone, this file reports 29 unreachable rules,
because 901001 denies with a 500 when `tx.crs_setup_version` is unset. Loading
`crs-setup.conf` first is what makes the state model correct.

Reachability is O(n) solver calls, which makes it the practical first pass over
a large ruleset.

### Stateful pairs

`--stateful` changes what the pairwise analyses ask:

| Analysis | Stateless question | Stateful question |
|---|---|---|
| `intersection` | Could one request satisfy both patterns? | Is there one transaction in which **both rules fire**? |
| `subsumption` | Does every input matching A match B? | Does every transaction firing A also **fire** B? |
| `contradiction` | Do the patterns overlap with conflicting actions? | Does an earlier rule **shadow** a conflicting later one? |

Contradiction changes shape, not just precision: in an ordered model two
disruptive rules can never *both* fire, since the first one ends the
transaction. The real defect is a silent precedence, so the query becomes
"A fires on a request B would also have matched".

Because `TX` couples rules that share no request variable, this sweep cannot use
the "no shared variable" pruning the stateless one relies on — it is a genuine
O(n²) sweep. Run `reachability` first, then focus on what it flags.

### Soundness and cost

Anything the encoder cannot model faithfully — an unsupported operator, an
unresolvable macro, `ctl:ruleRemoveTargetById` — is over-approximated, so
**a rule reported dead is genuinely dead** while a rule reported live may just be
beyond the model's precision. Results carry an `approximate` flag when a side was
abstracted, and each run prints its caveats:

```
note: 4 directive(s) abstracted to a free Boolean (unsupported construct); they are assumed able to fire
```

Most CRS files finish in well under a second. The exception is `t:urlDecodeUni`:
it is modelled precisely as one rewrite pass per BMP codepoint, and the
whole-ruleset script cannot use the per-pattern codepoint restriction the
stateless analyses apply, so its ~13 MB definition is carried by every query in
such a file.

## Supported rule features

wafan supports the most common ModSecurity rule constructs:

**Operators:** `@rx` (regex), `@streq` (exact match), `@contains` (substring), `@beginsWith`, `@endsWith`, `@within`, `@pm` (phrase match), `@eq`/`@ge`/`@gt`/`@le`/`@lt` (numeric comparison). All operators support `!` negation.

**Transforms (`t:`):** Three levels of support:

- *Precisely formalized in SMT:* `lowercase`, `uppercase`, `htmlEntityDecode`, `urlDecode`, `urlDecodeUni`, `none`
- *Accepted but approximated* (modeled as uninterpreted functions with partial axioms — analysis results may be imprecise): `removeWhitespace`, `compressWhitespace`, `removeNulls`, `trim`, `trimLeft`, `trimRight`, `normalizePath`, `normalizePathWin`

**Rule chaining:** Chained rules (linked with the `chain` action) are treated as a single unit — a chain fires only when all of its links match, mirroring ModSecurity semantics.

Rules that use unsupported operators or transforms are skipped and reported as unknown.

## Running on OWASP ModSecurity Core Rule Set

The `owasp-rules/` directory contains the OWASP CRS rule files. You can run any analysis directly against them:

```bash
wafan owasp-rules/REQUEST-942-APPLICATION-ATTACK-SQLI.conf \
      --solver z3-noodler --analysis intersection -v
```

Note that large rule files with many rules will produce a large number of pairwise checks. Use `--timeout` to cap the time spent per query.
