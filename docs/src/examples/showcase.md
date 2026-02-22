# Showcase Overview

The showcase is a curated set of 8 examples that together cover all commonly-used language features, represent diverse domains, and range from trivial to strenuous.

| Spec | Domain | Lines | Key features |
|------|--------|-------|--------------|
| [Peterson](./peterson.md) | Mutual exclusion | 70 | Dict, Bool, parameterized actions, program counter |
| [Dining Philosophers](./dining-philosophers.md) | Concurrency | 43 | Modular arithmetic, multi-key dict update |
| [Two-Phase Commit](./two-phase-commit.md) | Transactions | 96 | `all`/`any` quantifiers, `implies` |
| [G-Counter](./g-counter.md) | CRDTs | 78 | Nested dicts, `let`, `func`, conditional comprehension |
| [MESI](./mesi.md) | Cache coherence | 146 | Full dict comprehension with `if/then/else` |
| [Paxos](./paxos.md) | Consensus | 95 | `powerset`, set comprehensions, nested quantifiers |
| [Redlock](./redlock.md) | Distributed locking | 153 | `Set`, `union`, intentional invariant violation |
| [Raft](./raft.md) | Consensus (complex) | 386 | `Seq`, `Set[Seq[Int]]`, message passing, slicing |

## Quick verification results

| Spec | Command | States |
|------|---------|--------|
| Peterson | `specl check peterson.specl --no-deadlock` | 17 |
| Dining Philosophers | `specl check dining-philosophers.specl --no-deadlock` | ~100 |
| Two-Phase Commit | `specl check two-phase-commit.specl -c N=2 --no-deadlock` | 134 |
| G-Counter | `specl check g-counter.specl -c N=2 -c Max=3 --no-deadlock` | 54K |
| MESI | `specl check mesi.specl -c C=2 -c V=1 --no-deadlock` | 34 |
| Paxos | `specl check paxos.specl -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock` | 316K |
| Redlock | `specl check redlock.specl -c N=2 -c M=1 -c TTL=3 -c MaxTime=8` | violation in 15 steps |
| Raft | `specl check raft.specl -c N=1 -c MaxVal=0 -c MaxElections=2 --no-deadlock` | 956 |

## Strenuous checks

| Spec | Params | States | Time |
|------|--------|--------|------|
| Raft | N=2, MaxVal=1, MaxElections=2, MaxLogLen=3 | 166M | ~4 min |
| Paxos | N=3, MaxBallot=3, V=2 | 3.35M | ~9s |
| Paxos (symbolic) | N=10, MaxBallot=10, V=3 | k-induction | ~90s |

All showcase specs are in [`specl/examples/showcase/`](https://github.com/danwt/specl/tree/main/specl/examples/showcase).
