# wafan

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
      [--analysis {subsumption}]
      conf
```

| Argument | Default | Description |
|---|---|---|
| `conf` | *(required)* | Path to a ModSecurity `.conf` file |
| `--solver PATH` | `z3` | SMT solver binary (must accept SMT-LIB2 on stdin, print `sat`/`unsat` on stdout) |
| `--solver-args ARGS` | *(none)* | Extra space-separated flags forwarded to the solver |
| `--timeout SEC` | `30` | Per-query timeout in seconds |
| `--analysis` | `subsumption` | Analysis to run |

## Examples

```bash
# Subsumption analysis with z3-noodler
wafan rules/REQUEST-942-SQL-INJECTION.conf --solver z3-noodler

# Full path to solver binary, extra flags, longer timeout
wafan rules/REQUEST-942-SQL-INJECTION.conf \
      --solver /opt/z3-noodler/bin/z3-noodler \
      --solver-args "--quiet" \
      --timeout 120

# Module invocation without installing the package
python -m wafan rules/REQUEST-942-SQL-INJECTION.conf --solver z3-noodler
```
