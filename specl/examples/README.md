# Specl Examples

## Directory Structure

| Directory | Description |
|-----------|-------------|
| `showcase/` | 8 curated examples covering all language features — the first place to look |
| `other/` | 100+ additional specs — protocols, puzzles, stress tests, semaphore problems |

The sibling `benchmarks/` directory contains TLC comparison scripts (`.tla`, `.cfg`, `.sh`) for performance benchmarking against TLC — it has no `.specl` files.

## Showcase

The showcase is a small, carefully chosen set of examples that together:
- Cover all commonly-used language features
- Represent diverse, practical domains
- Range from trivial to strenuous
- Demonstrate both BFS and symbolic checking

| Spec | Domain | Lines | What it demonstrates |
|------|--------|-------|----------------------|
| [Peterson](showcase/peterson.specl) | Mutual exclusion | 70 | Dict, Bool, range types, parameterized actions, guards, invariants |
| [Dining Philosophers](showcase/dining-philosophers.specl) | Concurrency | 43 | Modular arithmetic `%`, multi-key dict update |
| [Two-Phase Commit](showcase/two-phase-commit.specl) | Transactions | 96 | `const`, `all`/`any` quantifiers, `implies` |
| [G-Counter](showcase/g-counter.specl) | CRDTs | 78 | Nested dicts, `let` bindings, `func`, dict comprehension with conditional |
| [MESI](showcase/mesi.specl) | Cache coherence | 146 | Full dict comprehension with `if/then/else`, hardware domain |
| [Paxos](showcase/paxos.specl) | Consensus | 95 | `powerset`, set comprehensions, complex nested quantifiers |
| [Redlock](showcase/redlock.specl) | Distributed locking | 153 | `Set`, `union`, intentional invariant violation (Kleppmann attack) |
| [Raft](showcase/raft.specl) | Consensus (complex) | 386 | `Seq`, `Set[Seq[Int]]`, `++`, slicing, `head`/`tail`/`len`, `union`/`diff`, message passing |

### Verification Results

Quick checks (all pass in under 1 second):

| Spec | Check Command | States |
|------|---------------|--------|
| Peterson | `specl check peterson.specl --no-deadlock` | 17 |
| Dining Philosophers | `specl check dining-philosophers.specl --no-deadlock` | ~100 |
| Two-Phase Commit | `specl check two-phase-commit.specl -c N=2 --no-deadlock` | 134 |
| G-Counter | `specl check g-counter.specl -c N=2 -c Max=3 --no-deadlock` | 54K |
| MESI | `specl check mesi.specl -c C=2 -c V=1 --no-deadlock` | 34 |
| Paxos | `specl check paxos.specl -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock` | 316K |
| Redlock | `specl check redlock.specl -c N=2 -c M=1 -c TTL=3 -c MaxTime=8` | violation in 15 steps |
| Raft | `specl check raft.specl -c N=1 -c MaxVal=0 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=2 --no-deadlock` | 956 |

Strenuous checks (minutes at larger parameters):

| Spec | Mode | Params | Result |
|------|------|--------|--------|
| Raft | BFS | N=2, MaxVal=1, MaxElections=2, MaxRestarts=0, MaxLogLen=3 | 166M states, ~4 min |
| Paxos | BFS | N=3, MaxBallot=3, V=2 | 3.35M states, ~9s |
| Paxos | symbolic | N=10, MaxBallot=10, V=3 | k-induction, ~90s |

Bug-finding:

| Spec | Check Command | Bug Found |
|------|---------------|-----------|
| [Redlock](showcase/redlock.specl) | `-c N=2 -c M=1 -c TTL=3 -c MaxTime=8` | MutualExclusion violated — Kleppmann's attack: locks expire while client is paused, second client acquires majority |

### Notes

- **Raft** does not support symbolic mode (uses `Set[Seq[T]]` for message passing).
- **Paxos** is the best example for exercising both modes: BFS at N=3+, symbolic at N=10+.
- **MESI** has an inherently small state space (4 cache states per core) — even C=10 produces only hundreds of states.

## Scaling Guide

State spaces grow exponentially with constants. Start small:

| Constant increase | Typical state space growth |
|-------------------|---------------------------|
| N: 2 → 3 | 10-100x |
| N: 3 → 4 | 100-1000x |
| MaxRound/MaxBallot: +1 | 5-50x |
| Values: +1 | 2-10x |

Use `--fast` (fingerprint-only, 10x less memory) for large state spaces. Use `--por` for specs with independent actions.
