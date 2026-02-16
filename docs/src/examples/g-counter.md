# G-Counter CRDT

A Grow-only Counter where each process maintains a local counter. Processes increment their own counter and merge others' state via pointwise max. The global value is the sum of all local counters.

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/g-counter.specl)

```specl
{{#include ../../../specl/examples/showcase/g-counter.specl}}
```

## What to notice

- **Nested dicts.** `counter: Dict[0..N, Dict[0..N, 0..Max]]` — `counter[p][q]` is process p's view of process q's count.
- **Nested dict update.** `counter = counter | {p: counter[p] | {p: counter[p][p] + 1}}` — updates the inner dict for the incrementing process.
- **Conditional comprehension.** The `Merge` action uses `if counter[q][r] > counter[p][r] then counter[q][r] else counter[p][r]` inside a dict comprehension to compute the pointwise max.
- **`func` and `let`.** `GlobalSum()` is a pure function used in the `Monotonic` invariant via `let cur = GlobalSum()`.
- **Shadow variable for temporal reasoning.** `prev_sum` tracks the previous global sum to verify monotonicity as a safety property (since temporal operators are not yet implemented).

```bash
specl check g-counter.specl -c N=2 -c Max=3 --no-deadlock
```
