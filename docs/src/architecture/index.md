# Architecture and Performance

## Crate structure

```
specl/crates/
├── specl-syntax/    Lexer, parser, AST, pretty-printer
├── specl-types/     Type checker
├── specl-ir/        IR, bytecode compiler, guard indexing, COI analysis
├── specl-eval/      Tree-walk evaluator + bytecode VM
├── specl-mc/        BFS explorer, parallel via rayon, state store, operation cache
├── specl-symbolic/  Symbolic verification (Z3-based)
├── specl-tla/       TLA+ parser and translator
├── specl-cli/       CLI (the `specl` binary)
└── specl-lsp/       Language server (the `specl-lsp` binary)
```

## Compilation pipeline

```
source → AST (specl-syntax)
       → typed AST (specl-types)
       → IR with compiled actions (specl-ir)
       → bytecode for guards/invariants/effects (specl-eval)
       → BFS exploration (specl-mc)
```

## Why Specl is faster than TLC

TLC is a Java-based model checker dating to ~2002. Specl's architecture avoids several structural limitations.

### State representation

TLC represents states as sorted string arrays with MD5 hashing (128-bit, cryptographic). Specl uses `Arc<Vec<Value>>` with a cached 64-bit XOR fingerprint computed incrementally via AHash. When an action modifies only 2 of 6 variables, Specl recomputes only those 2 variable hashes and XORs the delta — TLC rehashes the entire state.

### Bytecode VM

TLC evaluates via a Java tree-walk interpreter: every AST node is a virtual method call, every intermediate result is boxed. Specl compiles guards, invariants, and effect expressions to a bytecode VM — a flat array of opcodes executed in a tight `match` loop. This eliminates recursive dispatch, reduces allocations, and enables CPU branch prediction.

### Guard indexing

When an action has parameters (e.g., `Transfer(from: 0..N, to: 0..N)`), TLC evaluates the full guard for every parameter combination. Specl analyzes guard conjuncts at compile time, determines which conjuncts depend on which parameters, and evaluates them incrementally as each parameter level is bound. If `from != to` fails, inner parameters are never enumerated.

### Invariant skipping

TLC checks all invariants on every new state. Specl tracks which variables each invariant reads (as a u64 bitmask) and skips invariants when none of their relevant variables changed. On specs like Raft where most actions touch 2-3 of 6 variables, this skips 50-70% of invariant evaluations.

### Dict updates

TLC's `EXCEPT` creates a new function object per update. Specl's `Value::IntMap` (a flat `Vec<i64>`) gives O(1) indexed dict lookups, and the bytecode VM has dedicated `NestedDictUpdate` opcodes that update nested dicts in a single pass without allocating intermediate dicts.

### Parallel BFS

TLC supports multiple workers but uses a shared queue with lock contention. Specl uses rayon with batch processing: each thread processes a batch of states, collects successors locally, then merges. The seen-set uses DashMap (sharded concurrent hashmap) or AtomicFPSet (lock-free fingerprint set for `--fast` mode, 8 bytes per entry).

### Operation caching

Specl maintains a per-action, thread-local direct-mapped cache keyed on `(parameter_hash, read_set_xor)`. When the same action with the same parameters hits the same read-set values, the successor fingerprint is reconstructed via XOR decomposition without re-evaluating the action. Adaptive disabling (2048-probe warmup, 2.4% minimum hit rate threshold) ensures the cache is only used when beneficial.

### Memory efficiency

TLC stores full states in a hashtable (~200+ bytes per state). Specl's `--fast` mode uses `AtomicFPSet`: a lock-free open-addressing hash table storing only 64-bit fingerprints (8 bytes/entry). This enables 100M+ states in ~1GB of RAM.

## State space reductions

### Partial order reduction (POR)

`--por` computes stubborn sets. For each state, Specl identifies which actions are independent (don't read/write overlapping variables) and explores only a sufficient subset. Effective for loosely-coupled processes.

### Symmetry reduction

`--symmetry` canonicalizes states by sorting process indices when processes are interchangeable.

### Cone of influence (COI)

At compile time, Specl computes which variables each action reads and writes. Actions that cannot affect any invariant variable are skipped entirely. Automatic and zero-overhead.
