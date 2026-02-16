# Performance Analysis: specl vs TLC on Bronson AVL

## Benchmark Results

| Metric | specl (Rust, BFS) | TLC (Java, BFS) |
|--------|-------------------|------------------|
| Result | INVARIANT VIOLATION | INVARIANT VIOLATION |
| Wall clock | ~11.2s | ~8.5s |
| CPU time | 145s | 64s |
| Workers | 16 threads | 16 threads |
| States generated | unknown | 1,757,151 |
| Distinct states | unknown | 886,971 |
| Depth | ~97 | 97 |

**CPU efficiency**: TLC uses 2.3x less CPU to find the same bug at the same depth.

## Architecture Comparison

### Where specl SHOULD be faster

| Advantage | specl | TLC |
|-----------|-------|-----|
| Evaluation | Bytecode VM (tight dispatch loop) | AST tree-walk interpreter (recursive, heap-heavy) |
| Values | NaN-boxed 8 bytes inline | Java objects 24+ bytes, GC pressure |
| Fingerprint | XOR-decomposable, O(1) incremental | Rabin polynomial, full recompute per state |
| State dedup | Lock-free AtomicFPSet (CAS + prefetch) | Synchronized FPSet (monitor locks) |
| Parallelism | Batch-parallel rayon (no queue contention) | Shared queue + monitor locks |
| Memory | No GC, deterministic drop | GC pauses, 16-byte object headers |
| 2D dicts | IntMap2 flattened (no pointer chasing) | Nested FcnRcdValue |

Will Schultz's benchmarks show that compiling TLA+ specs to C++ gives **18-59x** speedup over TLC. specl's bytecode VM should be somewhere between TLC's interpreter and native C++ compilation. Yet on this benchmark, specl is **2.3x worse** on CPU.

### What's different about the Bronson AVL model

This is not a typical protocol spec. It has:

- **81 variables** (most protocol specs have 5-20)
- **125 actions** (most have 5-20)
- **Heavy sequence usage**: `retStack` and `auSaveStack` are `Seq[Int]` with push/pop/len on every action
- **Many dict merges per action**: each action typically updates 3-5 dict variables via `|`
- **Large PC-based dispatch**: actions are guarded by `require pc[p] == N` for specific N values, creating a huge dispatch table
- **Deep call stacks**: the algorithm encodes procedure calls via sequences, with frequent append/slice operations

## Hypotheses for specl Underperformance

### H1: Arc overhead on sequences (HIGH confidence)

Every sequence push/pop creates a new `Arc<Vec<Value>>`. The Bronson AVL model does sequence operations on `retStack` and `auSaveStack` in nearly every action. Each operation:
1. `Arc::make_mut` — if refcount > 1, clones the entire Vec (allocation + copy)
2. push/pop modifies the Vec
3. New state wraps result in Arc (allocation)

In TLC, Java ArrayList operations benefit from escape analysis — the JIT can sometimes elide the intermediate allocations entirely. In specl, every intermediate sequence IS a heap allocation because it's Arc-wrapped.

**Impact**: With 125 actions × 2 processes × multiple sequence ops per action, this is millions of small allocations per second.

### H2: State construction cost (HIGH confidence)

Every successor state creates:
1. `Arc<Vec<Value>>` for 81 variables (heap alloc: 81 × 8 = 648 bytes + Arc header + Vec header)
2. `Arc<[u64]>` for 81 var hashes (heap alloc: 81 × 8 = 648 bytes + Arc header)

That's 2 heap allocations per successor state. At millions of successors, this is significant. The `std::mem::take` pattern on `next_vars_buf` avoids one copy but the Arc wrapping is unavoidable.

TLC's `TLCStateMut` uses `System.arraycopy` — one flat copy, no pointer indirection.

### H3: Guard evaluation waste (HIGH confidence)

With 125 actions and PC-based dispatch (`require pc[p] == N`), most actions fail their guard immediately. But specl still:
1. Sets up the evaluation context
2. Evaluates the guard bytecode (load pc, load p, dict-get, compare)
3. Discovers the guard fails
4. Moves to the next action

For 2 processes × 125 actions = 250 guard evaluations per state. ~248 of these will fail immediately. The question is whether specl's guard indexing eliminates this overhead.

**Check**: Does specl's guard indexing create an index on PC values? If not, every state evaluates all 125 guards even though only 2-4 can fire (one per process at their current PC).

TLC likely doesn't index either, but its JIT may compile the hot guard evaluation into extremely tight native code with branch prediction working well (the same guards fail in the same pattern repeatedly).

### H4: Parallel overhead (MEDIUM confidence)

CPU efficiency:
- specl: 145s CPU / 11.2s wall = 12.9x effective parallelism (81% of 16 threads)
- TLC: 64s CPU / 8.5s wall = 7.5x effective parallelism (47% of 16 threads)

specl achieves HIGHER parallel efficiency than TLC, but burns more total CPU. This suggests the bottleneck is **per-state cost**, not parallel coordination. The rayon batch-parallel design is working well — the problem is what happens inside each batch item.

### H5: DashMap contention in Full mode (MEDIUM confidence)

specl uses DashMap (sharded concurrent hashmap) for the state store in Full mode. DashMap has 16 shards by default. With 16 worker threads, shard contention is possible. Each state insertion locks a shard.

TLC's FPSet is also synchronized, but it only stores 8-byte fingerprints (not full states), so the critical section is shorter.

**Mitigation**: Run with `--fast` (AtomicFPSet, lock-free) to see if this helps. If wall-clock improves significantly, DashMap is the bottleneck.

### H6: XOR fingerprint quality (LOW confidence)

XOR-decomposable fingerprints have weaker mixing than Rabin polynomials. If many states hash to nearby buckets, probe chains in the hash table get longer. This is unlikely to explain a 2.3x difference but could contribute.

### H7: Bytecode VM dispatch overhead (LOW confidence)

The bytecode VM uses a match-based dispatch loop. Even though it's compiled to native code by rustc, the branch predictor may struggle with 100+ Op variants. TLC's JIT compiles the hot AST-walk paths into straight-line native code specialized for this specific spec.

This is the "sufficiently smart JIT" hypothesis — Java's C2 compiler may be producing better machine code for the hot inner loop than Rust's LLVM for the generic bytecode dispatch.

## Systematic Profiling Plan

### Phase 1: Instrument specl to report states/second

Add `--stats` or make `--profile` output include:
- Total states generated
- Distinct states found
- States/second (wall and CPU)
- Per-action firing count (already exists with `--profile`)
- Guard evaluation count vs guard pass count (measure guard waste)

This gives apples-to-apples throughput comparison with TLC.

### Phase 2: CPU profiling with perf/flamegraph

```bash
# Build with debug symbols but release optimizations
cargo build --release
# or set in Cargo.toml: [profile.release] debug = true

# Profile the Bronson AVL check
perf record -g --call-graph dwarf \
  specl check bronson_avl.specl --no-deadlock --threads 1 --max-time 30

# Generate flamegraph
perf script | inferno-collapse-perf | inferno-flamegraph > flame.svg
```

**Single-threaded first** (`--threads 1`) to eliminate parallel noise. Look for:
- What % of time is in `vm_eval` (bytecode VM)?
- What % is in `Arc::make_mut` / `Arc::clone` / `Arc::drop`?
- What % is in DashMap/state store operations?
- What % is in fingerprint computation?
- What % is in state construction (Arc wrapping)?

### Phase 3: Allocation profiling

```bash
# Using heaptrack (if available on macOS, otherwise use Instruments)
heaptrack specl check bronson_avl.specl --no-deadlock --threads 1 --max-time 30
heaptrack_print heaptrack.specl.*.zst | head -100

# Or on macOS, use Instruments with the Allocations instrument
# Or use DHAT via valgrind
```

Measure:
- Allocations per second
- Total bytes allocated
- Top allocation call sites

This will directly reveal if H1 (Arc overhead on sequences) and H2 (state construction cost) are the bottleneck.

### Phase 4: Micro-benchmarks

Create a benchmark harness (Criterion.rs) for:

1. **Single action evaluation**: Time the evaluation of one action (guard + effect) on a fixed state
2. **Dict merge**: Time `dict | {k: v}` for IntMap of size 15 (typical for this model)
3. **Sequence push/pop**: Time Seq operations with various refcount scenarios
4. **State construction**: Time creating a State from a Vec<Value> of 81 elements
5. **Fingerprint update**: Time incremental vs full fingerprint computation
6. **Guard indexing effectiveness**: Count how many guards are evaluated vs how many pass

### Phase 5: Compare storage backends

Run the same benchmark with each storage mode:

```bash
specl check bronson_avl.specl --no-deadlock --threads 16 --max-time 30         # Full (default)
specl check bronson_avl.specl --no-deadlock --threads 16 --max-time 30 --fast  # Fingerprint only
specl check bronson_avl.specl --no-deadlock --threads 16 --max-time 30 --bloom # Bloom filter
```

If `--fast` is significantly faster, the DashMap state store is a bottleneck.

### Phase 6: Single-thread comparison

```bash
specl check bronson_avl.specl --no-deadlock --threads 1 --max-time 30
java -jar tla2tools.jar -workers 1 BronsonAVL.tla
```

Eliminates all parallel overhead. If specl is still slower single-threaded, the problem is purely per-state evaluation cost.

## Concrete Improvement Suggestions

### Immediate wins (no architecture change)

#### 1. PC-indexed action dispatch

For models with PC-based guards (`require pc[p] == N`), build a dispatch table at compile time:

```
pc_dispatch: Dict[Int, Vec<ActionIndex>]
  0 -> [action_writeInv_erase, action_writeInv_insert]
  1 -> [action_update_begin, ...]
  2 -> [action_au_readChild, ...]
  ...
```

For each state, only evaluate actions whose PC value matches. This turns 250 guard evaluations into ~4-8.

**Expected impact**: 10-30x reduction in guard evaluation overhead.

#### 2. Sequence COW optimization

For Seq operations (push/pop/head/tail), avoid Arc::make_mut when the sequence is consumed (refcount == 1). Currently the bytecode VM may create unnecessary clones.

Add specialized bytecode ops:
- `Op::SeqPush` — push element, in-place if refcount == 1
- `Op::SeqPop` — pop element, in-place if refcount == 1
- `Op::SeqLast` — read last element without cloning

**Expected impact**: Eliminates most sequence allocations in this model.

#### 3. Avoid double Arc allocation in State construction

Instead of two Arcs (`Arc<Vec<Value>>` + `Arc<[u64]>`), use a single allocation:

```rust
struct StateInner {
    fp: Fingerprint,
    len: usize,
    // followed by: [Value; len] then [u64; len] in a single allocation
}
```

Or use `Arc<(Vec<Value>, Vec<u64>)>` to at least reduce from 2 allocs to 1.

**Expected impact**: 50% reduction in per-state allocation overhead.

#### 4. Inline small sequences

Sequences of length <= 7 (fitting in 56 bytes) could be stored inline in the NaN-boxed Value, similar to how Int/Bool are inline. The Bronson AVL stacks are typically short (depth <= 5-6).

**Expected impact**: Eliminates heap allocation for most sequence operations in this model.

### Medium-term improvements

#### 5. State pool / arena allocator

Use a thread-local arena allocator for successor state construction. Allocate states from a pre-allocated slab, reset per batch. This eliminates per-state heap allocation entirely.

```rust
struct StateArena {
    vars_pool: Vec<Vec<Value>>,    // recycled var buffers
    hashes_pool: Vec<Vec<u64>>,     // recycled hash buffers
}
```

**Expected impact**: Near-zero allocation overhead per state transition.

#### 6. Compiled evaluation (JIT or AOT)

Instead of bytecode VM dispatch, compile each action's guard and effect to native Rust closures at spec load time. This eliminates the match-based dispatch overhead and lets LLVM optimize each action independently.

This is essentially what Will Schultz's "bespoke compilation" does for TLA+ → C++. specl could generate Rust code, compile it as a dylib, and dlopen it.

**Expected impact**: Based on Schultz's results, 5-50x improvement over bytecode interpretation. This would decisively beat TLC.

#### 7. Specialize the evaluator for common patterns

Detect at compile time that an action is "simple" (PC guard + a few dict updates + sequence push/pop) and generate a specialized fast-path that bypasses the general bytecode VM entirely.

The Bronson AVL model is 125 actions that each follow the pattern:
```
require pc[p] == N
dict1 = dict1 | {p: new_val1}
dict2 = dict2 | {p: new_val2}
pc = pc | {p: next_pc}
```

A specialized handler for this pattern could be 5-10x faster than general bytecode evaluation.

### Long-term

#### 8. Action-level partial order reduction

The Bronson AVL model has 2 writers operating on disjoint subtrees most of the time. POR could dramatically reduce the state space by recognizing that concurrent operations on different keys are independent.

This requires computing independence at the action-instance level (which specl already has infrastructure for via `write_key_params` and `read_key_params`).

#### 9. Symmetry reduction for writers

The two writer processes are symmetric (same code, different parameters). Symmetry reduction could halve the state space.

## Recommended Next Steps

1. **Profile single-threaded** (`perf record` + flamegraph) — 30 minutes of work, immediately reveals the bottleneck
2. **Add state count reporting** to specl's output — enables direct throughput comparison
3. **Test `--fast` mode** — if significantly faster, focus on DashMap optimization
4. **Implement PC-indexed dispatch** — likely the single biggest win for this class of models
5. **Profile allocation** — confirms/denies the Arc overhead hypothesis
