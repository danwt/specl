# Two-Phase Commit

Two-Phase Commit (2PC) is the standard protocol for distributed transactions. One coordinator sends prepare, participants vote yes/no, and the coordinator decides commit (all yes) or abort (any no).

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/two-phase-commit.specl)

```specl
{{#include ../../../specl/examples/showcase/two-phase-commit.specl}}
```

## What to notice

- **Quantifiers in guards.** `require all p in 0..N: voted[p] == true` — the coordinator waits for all votes. `require any p in 0..N: voted[p] == true and vote[p] == 0` — abort if any vote is no.
- **`implies` in invariants.** `coord_pc == 2 implies all p in 0..N: vote[p] == 1` — if committed, all must have voted yes.
- **Agreement invariant.** No participant commits while another aborts — the fundamental safety property of 2PC.

```bash
specl check two-phase-commit.specl -c N=2 --no-deadlock
```
