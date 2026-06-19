# wafan

[![Test](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml/badge.svg)](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml)

**wafan** is a command-line tool for analysing ModSecurity WAF rule files. Given a `.conf` file containing `SecRule` directives, it automatically checks whether rules overlap, subsume each other, or can be triggered at all — helping you catch redundancies, dead rules, and unexpected interactions before they affect a live deployment.

## What it does

WAF rule sets grow large quickly, and subtle interactions between rules are hard to spot by eye. wafan uses an SMT solver to answer three questions about any pair of rules:

- **Subsumption** — Is every request that triggers rule A also guaranteed to trigger rule B? If so, rule A is redundant given rule B (everything A blocks, B already blocks).
- **Intersection** — Is there any request that triggers both rules at the same time? Overlapping rules may indicate redundancy or conflicting actions.
- **Witness** — What is a concrete example request that triggers each rule? This lets you verify a rule behaves as intended and generate test cases.

The tool parses the rule file, translates each rule's matching conditions into a logical formula, and asks an SMT solver to find a proof or a counterexample. Results are printed directly to the terminal.

## Requirements

- Python ≥ 3.10
- [z3-noodler](https://github.com/VeriFIT/z3-noodler) — an SMT solver with full support for the ECMA 2020 regex standard used by ModSecurity `@rx` rules. Standard `z3` works only for rules using non-regex operators (`@streq`, `@contains`, etc.).

## Installation

```bash
python -m venv .venv && source .venv/bin/activate
pip install .
```

After installation the `wafan` command is available in the activated virtual environment. You can also run it without installing: `python -m wafan`.

## Usage

```
wafan [options] <conf>
```

| Argument | Default | Description |
|---|---|---|
| `conf` | *(required)* | Path to the ModSecurity `.conf` file to analyse |
| `--analysis` | `subsumption` | Which analysis to run: `subsumption`, `intersection`, or `witness` |
| `--solver PATH` | `z3` | Path to the SMT solver binary. Falls back to the `WAFAN_Z3_PATH` environment variable, then `z3`. Use `z3-noodler` for full `@rx` support. |
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

## Supported rule features

wafan supports the most common ModSecurity rule constructs:

**Operators:** `@rx` (regex), `@streq` (exact match), `@contains` (substring), `@beginsWith`, `@endsWith`, `@within`, `@pm` (phrase match), `@eq`/`@ge`/`@gt`/`@le`/`@lt` (numeric comparison). All operators support `!` negation.

**Transforms (`t:`):** Three levels of support:

- *Precisely formalized in SMT:* `lowercase`, `uppercase`, `htmlEntityDecode`, `urlDecode`, `none`
- *Accepted but approximated* (modeled as uninterpreted functions with partial axioms — analysis results may be imprecise): `urlDecodeUni`, `removeWhitespace`, `compressWhitespace`, `removeNulls`, `trim`, `trimLeft`, `trimRight`, `normalizePath`, `normalizePathWin`

**Rule chaining:** Chained rules (linked with the `chain` action) are treated as a single unit — a chain fires only when all of its links match, mirroring ModSecurity semantics.

Rules that use unsupported operators or transforms are skipped and reported as unknown.

## Running on OWASP ModSecurity Core Rule Set

The `owasp-rules/` directory contains the OWASP CRS rule files. You can run any analysis directly against them:

```bash
wafan owasp-rules/REQUEST-942-APPLICATION-ATTACK-SQLI.conf \
      --solver z3-noodler --analysis intersection -v
```

Note that large rule files with many rules will produce a large number of pairwise checks. Use `--timeout` to cap the time spent per query.
