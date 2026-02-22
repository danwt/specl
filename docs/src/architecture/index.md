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

For symbolic checking, the pipeline diverges after IR:

```
       → IR with compiled actions (specl-ir)
       → Z3 SMT encoding (specl-symbolic)
       → BMC / k-induction / IC3 verification
```

## Explicit-state engine

### NaN-boxed values

Runtime values are 8 bytes each, using NaN-boxing. Integers and booleans are stored inline in the NaN payload of an IEEE 754 double — no heap allocation, no pointer chasing. Collections (dicts, sets, sequences) use the remaining NaN bit patterns for a tagged `Arc` pointer. This eliminates the overhead of a tagged enum with a separate heap pointer for every value.

### Bytecode VM and superinstructions

Specl compiles guards, invariants, and effect expressions to a bytecode VM — a flat array of opcodes executed in a tight `match` loop. This eliminates the recursive dispatch and boxing overhead of a tree-walk interpreter.

On top of the base bytecode, a peephole optimizer fuses common multi-opcode patterns into **superinstructions**. For example, `VarParamDictGetIntEq` fuses "load variable, load parameter, dict lookup, load integer, compare equal" into a single opcode. The optimizer profiles execution during a 2048-probe warmup phase and re-optimizes hot paths with adaptive specialization.

Current superinstructions (~15 total) cover:

- Dict lookups with parameter keys (`ParamIntDictGet`, `VarParamDictGet2`)
- Guard patterns (`BoolEq`, `VarParamDictGetIntEq`)
- Collection operations (`DictUpdateN`, `VarParamDictGetLen`)
- Sequence operations (`SeqConcat`, `SeqSlice`, `SeqHead`, `SeqTail`)
- Literal construction (`SetLit`, `SeqLit`)
- Set operations (`SetUnion`, `SetDiff`)
- Quantifier operations (`Forall`, `Exists`, `SetComp` over set and range domains)

### State representation and hashing

States are stored as `Arc<Vec<Value>>` with a cached 64-bit fingerprint. Each variable's hash is computed independently via AHash and the state fingerprint is computed by XOR-combining the variable hashes. When an action modifies only 2 of 17 variables, Specl recomputes only those 2 variable hashes and XORs the delta — an incremental update rather than a full rehash.

For comparison, TLC represents states as sorted string arrays with MD5 hashing (128-bit, cryptographic) and rehashes the entire state on every modification.

### State storage

Three storage backends, automatically selected based on spec characteristics:

**Full state storage (default).** Uses DashMap (sharded concurrent hashmap) mapping fingerprints to full states. Supports trace reconstruction for counterexample reporting.

**Fingerprint-only storage (`--fast`).** Uses `AtomicFPSet`: a lock-free open-addressing hash table storing only 64-bit fingerprints (8 bytes per entry). No trace reconstruction, but enables 100M+ states in ~1GB of RAM. Uses triangular probing (probe distance grows quadratically, better clustering than linear probing) and CPU prefetch hints for cache-friendly access. Dynamic resizing prevents stalls when the load factor exceeds the threshold.

**Bloom filter storage (`--bloom`).** Uses a bloom filter for fixed-memory probabilistic state deduplication. Trades a small probability of missing states for constant memory usage regardless of state space size. Useful for specs where the state space exceeds available RAM.

#### Tree compression

State storage optionally uses LTSmin-style tree compression. Each variable value is stored in a shared tree node, and states that differ in only a few variables share most of their storage nodes. This reduces memory consumption and improves cache locality.

Collapse compression is also available: states are compressed into a compact byte representation by collapsing common variable-value patterns.

### Guard indexing

When an action has parameters (e.g., `Transfer(from: 0..N, to: 0..N)`), Specl analyzes guard conjuncts at compile time. It determines which conjuncts depend on which parameters and evaluates them incrementally as each parameter level is bound. If `from != to` fails for a given `from` value, the inner `to` parameter is never enumerated.

State-dependent parameter domains go further: when a parameter iterates over a set stored in state (e.g., `action Handle(msg: messages)`), the domain is read from the current state at evaluation time, avoiding enumeration of values that aren't present.

### Invariant skipping

Specl tracks which variables each invariant reads (as a u64 bitmask). When a successor state is generated, invariants are only checked if at least one of their relevant variables changed. On specs like Raft where most actions touch 2-3 of 17 variables, this skips 50-70% of invariant evaluations.

### Dict representation

Specl's `Value::IntMap` is a flat `Vec<i64>` giving O(1) indexed dict lookups. `IntMap2` is a flattened 2-level dict: a single contiguous array for `Dict[0..N, Dict[0..M, T]]`, avoiding nested allocation. The bytecode VM has dedicated `NestedDictUpdate` and `DictUpdateN` opcodes that update nested dicts in a single pass without allocating intermediate dicts.

### Parallel BFS

Specl uses rayon with batch processing: each thread processes a batch of states, collects successors into a thread-local buffer, then merges into the shared frontier. The seen-set uses either DashMap or AtomicFPSet depending on storage mode. An atomic counter tracks the seen-set size (avoiding the expensive `DashMap::len()` call).

Early fingerprint deduplication filters duplicate successors before constructing full State objects — avoiding allocation for states already in the seen-set.

### Operation caching

A per-action, thread-local direct-mapped cache keyed on `(parameter_hash, read_set_xor)`. When the same action with the same parameters hits the same read-set values, the successor fingerprint is reconstructed via XOR decomposition without re-evaluating the action. Adaptive disabling (2048-probe warmup, 2.4% minimum hit rate threshold) ensures the cache is only used when beneficial.

### Action ordering

Actions are sorted by guard cost (estimated from guard complexity) so that cheap-to-reject guards are evaluated first. Guards with redundant `Contains` checks for state-dependent domains are stripped at compile time. A precomputed `has_state_dep` flag avoids runtime checks for parameter domain types.

### Allocator and build optimizations

- **mimalloc** as the global allocator — better multi-threaded allocation performance than the system allocator.
- **Profile-guided optimization (PGO)** with diverse training workloads (small, medium, and large specs across different protocol types). PGO improves branch prediction accuracy in the VM dispatch loop.
- **LTO** (link-time optimization) and `#[inline(always)]` annotations on hot-path functions (`expect_int`, `expect_bool`, `expect_set`, value constructors).

### Benchmark: effect of optimizations

On a Raft benchmark (2M states, `--fast --bfs`, 16 threads):

| Configuration | Wall time | Speedup |
|---|---|---|
| Before optimizations | 9.74s (1 thread), 2.48s (16 threads) | baseline |
| After optimizations | 5.40s (1 thread), 2.00s (16 threads) | 1.8x / 1.24x |
| After + PGO | 3.73s (16 threads) | 2.61x vs original |

## Symbolic engine

The symbolic backend (`specl-symbolic`) encodes Specl specs as SMT formulas and uses Z3 to verify invariants without enumerating states.

### Encoding

Each Specl variable becomes a Z3 constant (or function for parameterized types). Dict types are encoded as Z3 arrays. Sets as Z3 sets. Sequences as Z3 arrays with a length variable. The init block becomes a constraint on the initial state. Each action becomes a transition relation formula: a conjunction of the guard (as a precondition) and the effects (as equalities between current-state and next-state variables). The overall transition relation is a disjunction of all action formulas.

### Verification techniques

**Bounded model checking (BMC).** Unroll the transition relation for k steps, creating variables for each time step. Check whether the invariant can be violated at any step. If a violation is found, reconstruct a concrete counterexample trace. Depth is configurable via `--bmc-depth`.

**k-induction.** A two-phase proof:
1. **Base case:** check that the invariant holds for all states reachable in k steps (equivalent to BMC at depth k).
2. **Inductive step:** assume the invariant holds for k consecutive states, and check that it holds for the (k+1)th state.

If both phases pass, the invariant holds for all reachable states regardless of depth. Many practical invariants are 2-inductive (k=2 suffices).

**CTI learning.** When the inductive step fails, the counterexample-to-induction (CTI) is analyzed. If the CTI state is unreachable (determined by a BMC check), a blocking clause is added to exclude it, and induction is retried. This loop iteratively strengthens the inductive hypothesis.

**IC3/PDR via CHC solving.** Uses Z3's Spacer engine to solve the verification problem as a set of constrained Horn clauses (CHC). Spacer computes inductive invariants automatically using property-directed reachability (PDR). Multiple Spacer parameter profiles (default, aggressive, flexible) are available.

**Golem CHC solver.** An alternative CHC backend to Z3 Spacer, available when the Golem binary is installed. Can sometimes solve problems that Spacer cannot.

**Portfolio mode.** Runs BMC, k-induction, and IC3 in parallel (separate threads) and takes the first result. Useful when it's unclear which technique will work best for a given spec.

**Smart cascade.** The default symbolic mode. Tries techniques in order of cost: single-step induction → k-induction with CTI → IC3 → BMC. Stops as soon as one succeeds. For most small-to-medium specs, induction or k-induction succeeds in milliseconds.

### Configurable solver timeout

Symbolic solver calls have a configurable timeout (`--solver-timeout`). This prevents individual Z3 calls from blocking indefinitely on hard instances.

## State space reductions

### Partial order reduction (POR)

`--por` computes stubborn sets using guard-based precomputation. For each state, Specl identifies which actions are independent (don't read/write overlapping variables) and explores only a sufficient subset. The implementation uses instance-level POR with key tracking — independence is checked at the level of specific dict keys, not whole variables.

Sleep sets provide additional reduction on top of stubborn sets. When two actions are independent and one has already been explored, the other is added to the sleep set and skipped in successor states.

### Symmetry reduction

`--symmetry` canonicalizes states by computing orbit representatives — sorting process indices when processes are interchangeable. The implementation detects symmetry groups automatically from the spec structure.

### Cone of influence (COI)

At compile time, Specl computes which variables each action reads and writes. Actions that cannot affect any checked invariant variable (transitively) are skipped entirely. When `--check-only` is used to check a specific invariant, the COI analysis filters both actions and invariant checks. Automatic and zero-overhead.

## Alternative exploration modes

### Directed search (`--directed`)

Priority-guided BFS that scores states by proximity to potential invariant violations. States that are "closer" to violating an invariant (based on guard and invariant analysis) are explored first. Useful for finding bugs faster in large state spaces.

### Swarm verification (`--swarm N`)

Runs N parallel model checker instances, each with a different random permutation of the action order. Different action orderings explore different parts of the state space first, increasing the chance of finding violations in bounded time. Combines with `--max-time` for time-bounded bug hunting.

### Simulation (`specl simulate`)

Random trace exploration without exhaustive search. Generates random execution traces by picking enabled actions uniformly at random. Useful for quick sanity checks and understanding spec behavior before committing to full model checking.
