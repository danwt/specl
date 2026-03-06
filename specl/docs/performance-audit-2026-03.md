# Specl Performance Audit (March 2026)

Target: state spaces of 1M-100M states. Estimated cumulative improvement: 20-40%.

## HIGH Priority

### H1: Global allocator swap to mimalloc
- **Files**: `Cargo.toml`, new 2-line `main.rs` setup
- **Impact**: 5-15% wall-clock on multi-threaded workloads
- **Effort**: 5 minutes
- **Why**: Default glibc/macOS allocator has high contention under parallel BFS. `mimalloc` or `tikv-jemallocator` dramatically reduce cross-thread allocation overhead. Every `Arc::new`, `Vec::push`, `Value::clone` of heap types hits the allocator.

### H2: SmallVec for parameter values (pvals)
- **Files**: `explorer.rs` (generate_successors, apply_template_actions)
- **Impact**: 10-15% in specs with parameterized actions
- **Effort**: 1 hour
- **Why**: `apply_template_actions` builds `Vec<Vec<Value>>` for parameter combinations. Most actions have 0-2 parameters. Use `SmallVec<[Value; 2]>` for inner vecs and `SmallVec<[SmallVec<[Value; 2]>; 4]>` for outer. Eliminates heap allocation for the common case in the hottest loop.

### H3: Remove double contains+insert in store
- **Files**: `explorer.rs` ~lines 2827-2841, `store.rs`
- **Impact**: 5-10% (eliminates redundant hash+lookup on every state)
- **Effort**: 30 minutes
- **Why**: Current pattern is `if !store.contains(&fp) { store.insert(state) }`. For DashMap-based stores, this does two separate shard locks and two hash lookups. Use `DashMap::entry()` API or a single `insert_if_absent` method that returns whether insertion happened.

### H4: Arc<[Value]> instead of Arc<Vec<Value>> for State::vars
- **Files**: `state.rs`
- **Impact**: 3-5% (one fewer indirection per state access, better cache behavior)
- **Effort**: 1 hour
- **Why**: `Arc<Vec<Value>>` is a pointer to a pointer to data (Arc -> Vec header -> heap). `Arc<[Value]>` is a pointer directly to the data (fat pointer, single allocation). With millions of states, eliminating one indirection per variable access compounds. Also saves 24 bytes per state (no Vec capacity/len separate from Arc).

### H5: Release profile optimization
- **File**: `Cargo.toml` workspace `[profile.release]`
- **Impact**: 3-8%
- **Effort**: 5 minutes
- **Current**: `lto = "thin"`, `codegen-units = 1`, `debug = true`
- **Change to**: `lto = "fat"`, `panic = "abort"`, `strip = "symbols"` (keep `debug = true` in a separate `[profile.release-debug]` if needed). Fat LTO enables cross-crate inlining critical for the bytecode VM dispatch. `panic = "abort"` eliminates unwind tables and landing pads.

## MEDIUM Priority

### M1: Bitmask stubborn set instead of HashSet
- **Files**: `explorer.rs` (POR computation, `compute_stubborn_set`)
- **Impact**: 3-5% when POR enabled
- **Effort**: 2 hours
- **Why**: Stubborn set computation uses `HashSet<usize>` for action indices. Action count is typically <256. A `u64` or `[u64; 4]` bitmask is O(1) insert/contains/union with no allocation. Also speeds up NES/NDS set operations.

### M2: Fast symmetry signatures without allocation
- **Files**: `state.rs` (build_signatures, canonicalize)
- **Impact**: 2-5% when symmetry enabled
- **Effort**: 2 hours
- **Why**: `build_signatures` allocates `Vec<Vec<Vec<u8>>>` for each state's signature. For N symmetric processes with M variables each, this is N*M heap allocations per state. Pre-allocate a flat buffer and use slices, or compute signatures as `u64` hashes directly (sufficient for greedy lexicographic ordering).

### M3: Remove AtomicU32 execution_count from Bytecode
- **Files**: `bytecode.rs`
- **Impact**: 1-3% (eliminates false sharing in parallel mode)
- **Effort**: 15 minutes
- **Why**: `Bytecode` struct contains `AtomicU32` for execution counting. In parallel BFS, multiple threads evaluate the same bytecode objects, causing cache-line bouncing on the atomic increment. Either move the counter to a separate cache-line-padded location, make it thread-local, or remove it (only used for adaptive OpCache disabling -- can sample instead).

### M4: COW state effects instead of full copy
- **Files**: `direct_eval.rs` (apply_effects_bytecode_reuse)
- **Impact**: 2-5% for specs with many variables but few changes per action
- **Effort**: 3 hours
- **Why**: Currently copies the entire parent state's variable vector via `extend_from_slice`, then overwrites changed variables. For a spec with 100 variables where an action changes 2, this copies 98 values unnecessarily. Use copy-on-write: clone the `Arc<[Value]>`, only allocate a new backing store when actually mutating. Or track which indices are written and build the new state from old + delta.

### M5: Pack QueueEntry tighter
- **Files**: `explorer.rs` (QueueEntry type alias)
- **Impact**: 1-3% (better cache utilization for BFS queue)
- **Effort**: 1 hour
- **Why**: `QueueEntry = (Fingerprint, State, usize, u64, u64)` is ~56 bytes. The `usize` depth and two `u64` fields (sleep set, hash) could be packed. Consider: depth as `u32` (4B saves 4B), or store depth separately. Smaller queue entries = more entries per cache line = faster BFS iteration. For 1M queued states, this saves ~4MB of cache pressure.

### M6: Shrink Op enum
- **Files**: `bytecode.rs`
- **Impact**: 1-2% (better instruction cache utilization)
- **Effort**: 2 hours
- **Why**: Op enum has ~60 variants with varying payload sizes. Check `std::mem::size_of::<Op>()` -- if it's large (>16 bytes), consider boxing rare large payloads or using a more compact encoding. The VM dispatch loop iterates over `&[Op]`; smaller ops = more ops per cache line = fewer instruction cache misses.

## LOW Priority

### L1: Avoid cloning params in action application
- **Files**: `explorer.rs`, `direct_eval.rs`
- **Impact**: 1-2%
- **Effort**: 1 hour
- **Why**: Parameter `Value`s are cloned when passed to the evaluator. For `Int`/`Bool` this is trivially cheap (8-byte copy). But for `Str`/`Set` parameters it's an Arc refcount increment. Pass by reference where possible.

### L2: Consider scc::HashMap over DashMap
- **Files**: `store.rs`
- **Impact**: 0-5% (workload dependent)
- **Effort**: 2 hours
- **Why**: `scc::HashMap` is lock-free and can outperform DashMap under high contention (many threads, high insert rate). Worth benchmarking. The identity hasher (`FingerprintBuildHasher`) is already optimal.

### L3: Software prefetch in BFS loop
- **Files**: `explorer.rs` (main BFS iteration)
- **Impact**: 1-3% on large state spaces
- **Effort**: 1 hour
- **Why**: Already done in `fpset.rs` (good). Could also prefetch the next batch entry's state data while processing the current one. `std::arch::x86_64::_mm_prefetch` with `_MM_HINT_T0`.

### L4: Skip empty pvals early
- **Files**: `explorer.rs` (apply_template_actions)
- **Impact**: 0-1%
- **Effort**: 15 minutes
- **Why**: If any parameter domain is empty, the cartesian product is empty. Check for empty domains before building combinations.

### L5: SmallVec for domain references
- **Files**: `explorer.rs` (guard index, domain computation)
- **Impact**: 0-1%
- **Effort**: 30 minutes
- **Why**: Domain computation collects references into Vecs. Most domains are small. SmallVec avoids allocation.

## Things Already Done Well

- **NaN-boxed Value**: 8-byte representation, excellent. Clone is O(1) for inline types.
- **XOR-decomposable fingerprints**: O(1) incremental update per variable change. Excellent.
- **AtomicFPSet**: Lockless with triangular probing and software prefetch. State of the art.
- **Identity hasher**: `FingerprintBuildHasher` skips re-hashing already-hashed fingerprints. Correct.
- **Bytecode superinstructions**: VarParamDictGetIntEq etc. reduce dispatch overhead for common patterns.
- **Thread-local buffers**: `VmBufs` and `ParBufs` avoid cross-thread contention for temporary allocations.
- **splitmix64 hashing**: Fast, well-distributed for integer-heavy state variables.
- **Guard indexing + PC dispatch table**: Avoids evaluating irrelevant guards. Good pruning.
- **Fingerprint-first checking**: `compute_effects_bytecode_reuse` defers State construction until fingerprint passes. Excellent optimization.
- **IntMap/IntMap2**: Cache-friendly dense dict storage using raw NaN-boxed bits for hashing.
- **Batched parallel BFS**: `batch_size = num_threads * 4096` is a reasonable starting point.

## Recommended Implementation Order

1. **H5** - Release profile (5 min, guaranteed improvement)
2. **H1** - mimalloc (5 min, high impact)
3. **H3** - Remove double contains+insert (30 min, clear win)
4. **H4** - Arc<[Value]> (1 hour, systematic improvement)
5. **H2** - SmallVec pvals (1 hour, high impact for parameterized specs)
6. **M3** - Remove atomic counter (15 min, easy parallel win)
7. **M1** - Bitmask stubborn set (2 hours, POR improvement)
8. **M5** - Pack QueueEntry (1 hour, cache improvement)
9. **M4** - COW effects (3 hours, bigger refactor)
10. **M2** - Fast signatures (2 hours, symmetry improvement)

## Profiling

Before implementing, profile with:
```sh
cargo install samply
samply record -- target/release/specl check --fast path/to/large_spec.specl
```

Focus on which functions dominate. The priorities above are educated guesses -- profiling may reorder them significantly.
