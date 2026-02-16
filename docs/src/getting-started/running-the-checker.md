# Running the Checker

## Basic usage

```bash
specl check spec.specl -c N=3
```

The `-c` flag sets constant values. You can pass multiple constants:

```bash
specl check spec.specl -c N=3 -c MAX=10
```

## Understanding the output

### OK — all states verified

```
Result: OK
  States explored: 1,580,000
  Distinct states: 1,580,000
  Max depth: 47
  Time: 19.0s (83K states/s)
```

All reachable states satisfy all invariants. No deadlocks were found (unless `--no-deadlock` was used).

### Invariant violation

```
Result: INVARIANT VIOLATION
  Invariant: MoneyConserved
  Trace (2 steps):
    0: init -> alice=10, bob=10
    1: BrokenDeposit -> alice=10, bob=15
```

The checker found the **shortest path** to the violation. Each step shows which action fired and the resulting state. This trace is your primary debugging tool.

### Deadlock

```
Result: DEADLOCK
  Trace (N steps):
    ...
```

A reachable state where no action is enabled. For protocols this is often expected — use `--no-deadlock` to suppress deadlock checking.

## Common flags

```bash
specl check spec.specl --no-deadlock        # skip deadlock detection
specl check spec.specl --fast               # fingerprint-only (10x less memory, no traces)
specl check spec.specl --por                # partial order reduction
specl check spec.specl --symmetry           # symmetry reduction
specl check spec.specl --threads 4          # control parallelism
specl check spec.specl --max-states 100000  # limit exploration
```

See [Performance Flags](../model-checker/performance-flags.md) for a complete reference.

## Watch mode

Re-run the check automatically when the file changes:

```bash
specl watch spec.specl -c N=3
```

## Other commands

```bash
specl format spec.specl --write    # format in place
specl lint spec.specl              # fast syntax + type check (no model checking)
specl info spec.specl -c N=3       # analyze spec: actions, state space estimates
```

See [Advanced Commands](../model-checker/advanced-commands.md) for the full CLI reference.
