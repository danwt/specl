# Soundness oracle

Specl's built-in soundness tests check *internal* consistency (storage backends
agree, parallel == sequential, parse roundtrip). They cannot catch a bug where
the whole checker reaches a wrong verdict. This oracle adds an *external* one: it
runs the same TLA+ spec through both TLC and specl and asserts they agree on
OK-vs-violation.

## Run

```bash
# from the repo root; java required, tla2tools.jar auto-downloaded if absent
specl/tools/soundness/oracle.sh
# or pin the tools:
SPECL=specl/target/release/specl TLA_TOOLS_JAR=/path/to/tla2tools.jar specl/tools/soundness/oracle.sh
```

Exit 0 if every spec agrees (or is an allowlisted known issue), 1 on a new
disagreement, 2 if a required tool is missing.

## Specs

Curated `.tla` + `.cfg` pairs are listed in `oracle.sh` (`SPECS`). Each must use
only scalar constants (specl's `-c` does not take set-valued constants yet) and
translate cleanly. `specs/` holds oracle-only specs; others are reused from
`specl/benchmarks/comparison/`.

## Known issues

`KNOWN_ISSUES` in `oracle.sh` lists specs whose disagreement is a filed bug, so
the oracle stays green while still guarding against new disagreements. Remove an
entry when its bug is fixed.

- `DieHard` — #96: the default symbolic path (IC3) returns a false OK; BFS, BMC,
  and TLC all find the violation.
