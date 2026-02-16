# How It Works

## State machine semantics

A Specl specification defines a state machine:

1. **State** — the current values of all variables
2. **Initial state** — defined by the `init` block
3. **Transitions** — each action, with each valid parameter combination, defines a possible transition from one state to another
4. **Properties** — invariants must hold in every reachable state

## Breadth-first search

The model checker explores the state space using BFS:

1. Start from the initial state
2. In each state, try all actions with all parameter combinations
3. For each enabled action (all `require` guards pass), compute the successor state
4. Check all invariants in the successor state
5. If the successor is new (not seen before), add it to the queue
6. Repeat until the queue is empty or a violation is found

BFS guarantees that any violation trace is the **shortest possible path** from the initial state to the bug.

## Parallel exploration

By default, Specl uses all available CPU cores. The BFS frontier is processed in batches: each thread processes a batch of states, collects successors locally, then merges into the shared state set. The shared set uses `DashMap` (sharded concurrent hashmap) for lock-free concurrent access.

Use `--threads N` to control parallelism, or `--no-parallel` for single-threaded deterministic execution.

## State storage

Each visited state is stored in a hash set to detect duplicates. Two modes:

- **Default** — full state storage. Enables counterexample trace reconstruction.
- **`--fast`** — fingerprint-only mode. Stores only a 64-bit hash per state (8 bytes vs ~200+ bytes). Cannot produce traces, but enables exploration of 100M+ states in ~1GB of RAM.

## Deadlock detection

A deadlock is a reachable state where no action is enabled. By default, the checker reports deadlocks as errors. Use `--no-deadlock` to suppress this (common for protocol specs where quiescent states are expected).
