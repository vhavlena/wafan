# wafan

[![Test](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml/badge.svg)](https://github.com/vhavlena/wafan/actions/workflows/python-tests.yml)

SMT-based analysis of WAF ModSecurity SecRule rulesets.

`wafan` parses ModSecurity configuration files, converts `@rx` rules to
SMT-LIB2 formulae, and runs analyses using an external SMT solver.  The
generated formulae target [z3-noodler](https://github.com/VeriFIT/z3-noodler),
which supports the `re.from_ecma2020` string function required to embed ECMA
regex patterns directly into SMT-LIB2.

## Requirements

- Python ≥ 3.10
- An SMT-LIB2-compatible solver on `PATH` — use `z3-noodler` for full
  `re.from_ecma2020` support

## Installation

```bash
python -m venv .venv && source .venv/bin/activate
pip install .
```

## CLI usage

```
wafan [--solver PATH] [--solver-args ARGS] [--timeout SEC]
      [--analysis {subsumption,intersection,witness}]
      [-v] [-v2]
      conf
```

| Argument | Default | Description |
|---|---|---|
| `conf` | *(required)* | Path to a ModSecurity `.conf` file |
| `--solver PATH` | `z3` | SMT solver binary (must accept SMT-LIB2 on stdin). Falls back to `WAFAN_Z3_PATH` env var, then `z3`. Full `re.from_ecma2020` support requires `z3-noodler`. |
| `--solver-args ARGS` | *(none)* | Extra space-separated flags forwarded to the solver binary |
| `--timeout SEC` | `30` | Per-query solver timeout in seconds |
| `--analysis` | `subsumption` | Analysis to run: `subsumption`, `intersection`, or `witness` |
| `-v` | off | Verbose: print each rule (pair) being checked along with its result |
| `-v2` | off | Like `-v`, but also print the SMT-LIB2 formula for each query |

### Analyses

| Analysis | What it detects |
|---|---|
| `subsumption` | Ordered pairs (R1, R2) where every input triggering R1 also triggers R2 (R1 ⊆ R2) |
| `intersection` | Unordered pairs (R1, R2) that share at least one triggering input (R1 ∩ R2 ≠ ∅) |
| `witness` | A concrete input string that triggers each rule, if one exists |

## Examples

```bash
# Subsumption analysis with z3-noodler
wafan rules/REQUEST-942-SQL-INJECTION.conf --solver z3-noodler

# Intersection analysis, verbose
wafan rules/REQUEST-942-SQL-INJECTION.conf --solver z3-noodler \
      --analysis intersection -v

# Find concrete triggering inputs for each rule
wafan rules/REQUEST-942-SQL-INJECTION.conf --solver z3-noodler \
      --analysis witness -v

# Full path to solver binary, extra flags, longer timeout
wafan rules/REQUEST-942-SQL-INJECTION.conf \
      --solver /opt/z3-noodler/bin/z3-noodler \
      --solver-args "--quiet" \
      --timeout 120

# Module invocation without installing the package
python -m wafan rules/REQUEST-942-SQL-INJECTION.conf --solver z3-noodler
```
