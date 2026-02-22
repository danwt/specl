# Performance Flags

## Complete flag reference

| Flag | Effect | When to use |
|------|--------|-------------|
| `--fast` | Fingerprint-only (8 bytes/state, no traces) | Large state spaces (>1M states) |
| `--por` | Partial order reduction | Specs with independent actions |
| `--symmetry` | Symmetry reduction | Identical/interchangeable processes |
| `--no-parallel` | Single-threaded | Debugging, deterministic output |
| `--threads N` | Set thread count | Fine-tune parallelism |
| `--max-states N` | Stop after N states | Time/resource limits |
| `--max-depth N` | Limit BFS depth | Bounded depth verification |
| `--max-time N` | Time limit in seconds | CI/scheduled checks |
| `--memory-limit N` | Max memory in MB | Resource-constrained environments |
| `--bloom` | Bloom filter (fixed memory, probabilistic) | Very large state spaces |
| `--directed` | Priority BFS toward violations | Bug hunting |
| `--swarm N` | N parallel instances with shuffled action orders | Probabilistic bug hunting |
| `--no-deadlock` | Skip deadlock detection | Protocol specs with quiescent states |
| `--check-only NAME` | Check only named invariant(s) | Focused verification |

## `--fast` — fingerprint mode

Stores only 64-bit fingerprints instead of full states. Uses ~25x less memory. Cannot produce counterexample traces.

```bash
specl check spec.specl -c N=3 --fast    # 8 bytes/state vs ~200 bytes
```

Use this when you need to verify large state spaces and a simple "violation exists" / "OK" answer is sufficient. If a violation is found, re-run without `--fast` to get the trace.

## `--por` — partial order reduction

Computes stubborn sets: identifies which actions are independent (don't read/write overlapping variables) and explores only a sufficient subset. Can reduce the state space by orders of magnitude for loosely-coupled processes.

```bash
specl check spec.specl -c N=3 --por
```

Most effective when processes interact infrequently (e.g., separate counters that occasionally synchronize).

## `--symmetry` — symmetry reduction

When processes are interchangeable, canonicalizes states by sorting process indices. Collapses symmetric states into one representative.

```bash
specl check spec.specl -c N=3 --symmetry
```

Only effective when processes are truly identical (same actions, same initial state).

## Combining flags

Flags compose freely:

```bash
# Maximum reduction for large state space
specl check spec.specl -c N=3 --por --symmetry --fast

# Bounded exploration with time limit
specl check spec.specl -c N=4 --max-states 10000000 --max-time 300
```

## Recommended progression

```bash
# 1. Start small, default settings
specl check spec.specl -c N=2

# 2. Scale up processes
specl check spec.specl -c N=2 -c MaxTerm=2

# 3. Add reductions
specl check spec.specl -c N=2 -c MaxTerm=2 --por

# 4. Go bigger with fast mode
specl check spec.specl -c N=3 -c MaxTerm=2 --por --fast

# 5. Maximum coverage
specl check spec.specl -c N=3 -c MaxTerm=2 --por --symmetry --fast
```
