# Technical Status

Current status of Specl's verification capabilities, TLA+ compatibility, and performance relative to TLC/Apalache.

## Soundness

Specl's explicit-state checker has three soundness assurance mechanisms:

**Differential testing.** Property-based tests (proptest) generate random micro-specs and verify that all four storage backends (full-state, fingerprint-only, tree-compressed, collapse-compressed) explore identical state counts. This catches bugs in state representation, hashing, and deduplication.

**Determinism checks.** Tests verify that parallel and sequential exploration produce identical results, and that repeated parallel runs are deterministic.

**Parser roundtrip.** Property-based tests verify parse → pretty-print → parse idempotence across hundreds of synthetically generated specs.

**What is NOT tested:** There is no cross-tool oracle (e.g., running the same spec through both Specl and TLC and comparing results). The soundness tests verify internal consistency, not correctness against an external reference. The symbolic backend (Z3) inherits Z3's soundness guarantees.

## TLA+ compatibility

The `specl translate` command handles most TLA+ syntax:

**Supported:**
- Variables, constants, operators (including parameterized)
- Init/Next predicates
- Invariants
- Set comprehensions, quantifiers (`\A`, `\E`)
- Primed variables → assignment translation
- EXCEPT notation → dict update (`f | {k: v}`)
- Records, tuples, sequences
- Let-bindings with operator definitions
- Operator inlining (constant, helper, stateful)

**Not yet supported:**
- Function comprehensions (`[x \in S |-> expr]`) — affects 9 showcase specs (raft.tla, paxos.tla, pbft.tla, etc.)
- Module composition (`EXTENDS`, `INSTANCE`)
- Recursive functions

**Test corpus:** All showcase and example `.tla` files translate successfully except 9 known failures (all due to function comprehension syntax). The translator handles ~4200 lines of TLA+ grammar.

## Performance vs TLC

Specl is faster than TLC on all benchmarks tested. The primary advantages:

| Technique | Specl | TLC |
|-----------|-------|-----|
| Value representation | NaN-boxed 8-byte values, inline integers | Object arrays with string serialization |
| Hashing | AHash (non-cryptographic), incremental XOR | MD5 (cryptographic), full rehash per state |
| Dict access | O(1) flat vector (IntMap) | Hash-based function lookup |
| Parallelism | rayon batch BFS, lock-free AtomicFPSet | Concurrent workers with shared disk storage |
| Guard evaluation | Bytecode VM with superinstructions | Interpreted TLA+ expressions |

**Measured speedups** (Raft benchmark, 2M states, `--fast`, 16 threads):

| Configuration | Wall time |
|---|---|
| Baseline (1 thread) | 9.74s |
| After optimizations (1 thread) | 5.40s (1.8x) |
| After optimizations (16 threads) | 2.00s (4.9x) |
| With PGO (16 threads) | 3.73s (2.6x vs baseline) |

The benchmarking infrastructure includes head-to-head scripts comparing Specl vs TLC on TCommit and EWD840 at varying sizes. JVM startup (~0.7s) is noted but not subtracted.

**Apalache comparison:** No direct benchmarks. Apalache uses a fundamentally different approach (symbolic with SMT solvers) and targets different use cases (unbounded verification). Direct time comparison is not meaningful — they solve different problems.

## Backend architecture

Both explicit-state (BFS) and symbolic (Z3) backends compile into a single `specl` binary. Auto-routing selects the backend based on spec analysis:

- **Unbounded types detected** → symbolic (cannot enumerate state space)
- **Finite state space** → BFS (explicit-state)
- **Symbolic fails** → automatic fallback to BFS with explanation

There are no plans to split into separate binaries. The shared compilation pipeline (parse → typecheck → IR) makes a single binary the pragmatic choice.

## What is not yet implemented

- **Liveness checking** — temporal operators (`always`, `eventually`, `leads_to`) parse and type-check but are not evaluated by the model checker. Fairness declarations are similarly parsed but unused.
- **Module composition** — each spec is a single module. No `EXTENDS` or `INSTANCE`.
- **Recursive functions** — functions cannot call themselves.

See [Roadmap](../tips/roadmap.md) for planned optimizations (Cranelift JIT, compiled verifier).
