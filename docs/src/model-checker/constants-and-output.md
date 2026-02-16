# Setting Constants and Reading Output

## Setting constants

Use `-c KEY=VALUE` to set constant values at check time:

```bash
specl check spec.specl -c N=3 -c MAX=10 -c TIMEOUT=5
```

Constants must be set for every `const` declared in the spec. The checker will error if a constant is missing.

## Output: OK

```
Result: OK
  States explored: 1,580,000
  Distinct states: 1,580,000
  Max depth: 47
  Time: 19.0s (83K states/s)
```

All reachable states satisfy all invariants. The state space has been fully explored within the given constant bounds.

- **States explored** — total states visited (including duplicates hit during BFS)
- **Distinct states** — unique states in the state set
- **Max depth** — longest path from initial state to any reachable state
- **Time** — wall clock time with throughput

## Output: Invariant violation

```
Result: INVARIANT VIOLATION
  Invariant: MoneyConserved
  Trace (2 steps):
    0: init -> alice=10, bob=10
    1: BrokenDeposit -> alice=10, bob=15
```

The trace shows the **shortest path** from the initial state to the violation:

- **Step 0** is always the initial state
- Each subsequent step shows the action name (with parameters if any) and the resulting variable values
- The trace is minimal — BFS guarantees no shorter path exists

Use `--diff` to show only the variables that changed in each step (helpful for specs with many variables).

## Output: Deadlock

```
Result: DEADLOCK
  Trace (N steps):
    ...
```

A reachable state where no action is enabled. Use `--no-deadlock` if deadlocks are expected (most protocol specs have quiescent states).

## Bounded model checking

Constants like `MaxTerm=3` bound the exploration. `OK` with `MaxTerm=3` means no bug exists within that bound — it does not prove unbounded correctness. Increase bounds for higher confidence:

```bash
specl check spec.specl -c N=2 -c MaxTerm=1    # quick smoke test
specl check spec.specl -c N=2 -c MaxTerm=2    # more coverage
specl check spec.specl -c N=2 -c MaxTerm=3    # thorough
specl check spec.specl -c N=3 -c MaxTerm=2    # more processes
```
