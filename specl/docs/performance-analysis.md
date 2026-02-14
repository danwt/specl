# Specl Performance Analysis Report

**Date:** 2026-02-14
**System:** Apple Silicon (arm64), 16 threads, Rust release build
**Benchmark specs:** Raft, Lamport Mutex, Paxos, Ricart-Agrawala, Bakery, 2PC, others
**Commits:** NaN boxing (`cf5dcbc`), tree compression (`2008d6d`), arena allocation (`13b05a4`)

## 1. Benchmark Results

### 1.1 Multi-threaded throughput (default parallelism, 16 threads)

| Spec + Mode         |   States | Time(s) | States/s |
|----------------------|---------:|--------:|---------:|
| Raft N=2 full        |  501,981 |    0.83 |  604,796 |
| Raft N=2 --fast      |  500,003 |    5.44 |   91,912 |
| Raft N=2 --collapse  |  502,243 |    1.15 |  436,733 |
| Raft N=2 --tree      |  501,930 |    1.38 |  363,717 |
| Raft N=3 full        |2,006,574 |    4.10 |  489,408 |
| Raft N=3 --fast      |2,000,004 |   27.20 |   73,529 |
| Raft N=3 --collapse  |2,006,227 |    5.30 |  378,533 |
| Raft N=3 --tree      |2,006,051 |    6.30 |  318,420 |

### 1.2 Multi-threaded throughput across specs (16 threads)

| Spec                    |  States | full (s/s) | --fast (s/s) | --collapse (s/s) | --tree (s/s) |
|-------------------------|--------:|-----------:|-------------:|-----------------:|-------------:|
| Lamport Mutex N=3       | 505,500 |    618,900 |       90,500 |          418,700 |      379,700 |
| Paxos N=2 B=3 V=2      | 316,100 |    429,800 |       64,000 |          346,300 |      324,100 |
| Ricart-Agrawala N=3     |2,820,000|    479,500 |       52,900 |          332,800 |      317,000 |
| Bakery N=3 MT=8         |  12,000 |    717,700 |      136,500 |          590,300 |      467,100 |

Pattern is consistent: full mode fastest, --fast 5-9x slower (no parallelism), collapse/tree 15-35% slower.

### 1.3 Single-threaded throughput

| Spec + Mode              |   States | Time(s) | States/s |
|---------------------------|---------:|--------:|---------:|
| Raft N=2 full 1T          |  500,003 |    5.16 |   96,899 |
| Raft N=2 --collapse 1T    |  500,003 |    6.40 |   78,125 |
| Raft N=2 --tree 1T        |  500,003 |    7.13 |   70,126 |
| Raft N=3 full 1T          |2,000,004 |   26.76 |   74,738 |
| Raft N=3 --collapse 1T    |2,000,004 |   34.00 |   58,823 |
| Raft N=3 --tree 1T        |2,000,004 |   39.48 |   50,658 |

### 1.4 Memory usage (single-threaded, Raft N=3, 2M states)

| Mode     | Peak RSS (MB) | Time(s) | States/s |
|----------|-------------:|--------:|---------:|
| full     |        2,055 |   26.01 |   76,893 |
| collapse |        1,935 |   34.54 |   57,903 |
| tree     |        1,908 |   37.83 |   52,868 |
| fast     |        1,374 |   27.18 |   73,583 |

### 1.5 Parallelism efficiency

| Mode     | 1T (s/s) | 16T (s/s) | Speedup |
|----------|--------:|---------:|--------:|
| full     |  74,738 |  489,408 |   6.5x  |
| collapse |  58,823 |  378,533 |   6.4x  |
| tree     |  50,658 |  318,420 |   6.3x  |
| fast     |  73,583 |   73,529 |   1.0x  |

Key observation: **`--fast` mode does not parallelize.** It uses a separate single-threaded BFS loop (`check_fast_phase1`), bypassing the parallel rayon-based explorer entirely.

### 1.6 Internal timing breakdown (Raft N=3, single-threaded `--profile`)

Wall-clock breakdown from `--profile` flag (coarse categories, not CPU profile):

| Component             | % of time |
|-----------------------|-----------|
| Successor generation  |     94.3% |
| Store + queue         |      4.6% |
| Invariant checking    |      1.0% |

Note: "successor generation" includes guard evaluation, effect application, fingerprint computation, and all hashing within those operations. The CPU profile in section 2 breaks this down further.

## 2. CPU Profile Analysis

Samply CPU profile: Raft N=3 single-threaded, 27,571 samples (~28s)

### 2.1 Self-time breakdown by category

| Category      | Self-time % | Explanation |
|---------------|------------|-------------|
| **Hashing (SipHash)** | **51.7%** | `DefaultHasher::write` for Value fingerprinting |
| **Value::kind()** | **13.1%** | NaN-box tag extraction on every value access |
| Bytecode VM   |   4.2% | `vm_eval_inner` instruction dispatch |
| Explorer      |   2.4% | BFS queue management, action enumeration |
| Clone/Drop    |   2.2% | Arc refcount operations for Value |
| Store ops     |   2.1% | DashMap insert/contains |
| Eval (treewalk) | 2.0% | `eval` / `eval_binary` fallback |
| Allocation    |   0.9% | malloc/free |

### 2.2 Top individual functions by self-time

| % self | Function |
|--------|----------|
| 34.5%  | `<SipHasher as Hasher>::write` (all call sites combined) |
| 13.1%  | `Value::kind` (NaN-box tag decode) |
|  9.3%  | `<Value as Hash>::hash` |
|  0.9%  | `<Value as Ord>::cmp` |
|  0.7%  | `<Value as Drop>::drop` |
|  0.5%  | `bytecode::vm_eval_inner` |
|  0.4%  | `store::StateStore::len` |

### 2.3 Top inclusive-time call chains

| % incl | Function |
|---------|----------|
| 95.0%   | `Explorer::check` (entry point) |
| 94.9%   | `Explorer::generate_successors` |
| 94.9%   | `Explorer::apply_template_actions` |
| 50.8%   | fold loop over actions |
| 32.7%   | `<Value as Hash>::hash` (all call sites) |
| 20.9%   | `bytecode::vm_eval` |
| 15.3%   | `direct_eval::apply_effects_bytecode` |
| 8.6%    | `state::hash_var` |

## 3. Root Cause Analysis

### 3.1 The hashing bottleneck (51.7% of total time)

The dominant cost is **SipHash invocations during fingerprint computation**. The fingerprint (state hash) uses XOR-decomposition: `fp = XOR(hash_var(i, var[i]))` for all variables. The `hash_var` function has fast paths for `Int` and `Bool` (inline splitmix64), but all composite types (Dict, Set, Seq) fall through to `std::collections::hash_map::DefaultHasher` which uses SipHash-1-3.

For the Raft spec, 15 of 17 variables are composite types:
- 11 Dict types (represented as `Vec<(Value, Value)>`)
- 4 Set types (represented as `Vec<Value>`)
- Many have nested structure: `Dict[Int, Dict[Int, Bool]]`, `Set[Seq[Int]]`

SipHash recursively traverses the entire value tree for each composite variable. With N=3 Raft:
- `votesGranted`: Dict with 4 entries, each mapping to Dict with 4 entries → 16 inner hashes
- `reqVoteReqs`: Set of Seq[Int] messages → hash each message sequence
- Each `update_fingerprint` re-hashes the old AND new value of changed variables

This creates O(state_size * avg_collection_depth) hash operations per state transition.

### 3.2 Value::kind() overhead (13.1% of total time)

The NaN-boxing representation extracts the type tag via `kind()`, which does bitwise operations and unsafe pointer casts. This is called pervasively: every hash, compare, clone, drop, and eval operation starts with `kind()`. The 13.1% self-time indicates the 12-way `match` on the tag byte causes branch mispredictions, especially inside hash/compare loops over heterogeneous collections where the type pattern is unpredictable. In tight loops processing Vec<Value> with uniform types (e.g., all-Int dict keys), PGO could help the CPU predict the dominant branch.

### 3.3 --fast mode parallelism gap

`check_fast_phase1()` is a completely separate BFS implementation with its own `VecDeque` loop. It does not use the rayon-parallel `check_parallel()` path. This makes `--fast` mode 6.5x slower than `full` mode in multi-threaded scenarios despite using less memory.

## 4. Optimization Recommendations (Priority Order)

### P0: Replace SipHash with ahash for fingerprinting (~2-3x overall speedup expected)

**Impact:** 51.7% of time is in SipHash. ahash is 3-5x faster for small-to-medium inputs on modern CPUs.

**Change:** In `hash_var()` (state.rs:54-63), replace `DefaultHasher` with `ahash::AHasher`:
```rust
// Before (slow):
use std::collections::hash_map::DefaultHasher;
let mut hasher = DefaultHasher::new();

// After (fast):
let mut hasher = ahash::AHasher::default();
```

ahash already exists in `Cargo.toml` as a workspace dependency. This is a one-line change.

**Expected speedup:** If ahash is 3x faster on the hashing, the 51.7% becomes ~17%, saving ~35% of total time. Single-threaded Raft N=3 would go from ~75K/s to ~115K/s.

### P1: Memoize Value hash inside Arc (~additional 1.5-2x for composite-heavy specs)

**Impact:** Even with ahash, hashing a Dict of Dicts is O(n*m) per call.

**Change:** Add a cached hash field to heap-allocated composite types. When a Value is created or modified, compute and cache its hash. Subsequent `hash()` calls return the cached value in O(1).

Implementation options:
1. Store hash alongside the Arc data (e.g., `Arc<(u64, Vec<(Value, Value)>)>`)
2. Use `once_cell::sync::Lazy` inside the Arc for lazy computation
3. Add a hash field to the NaN-boxed representation (would require expanding beyond 8 bytes)

Option 1 is cleanest: compute hash at construction time (Values are immutable after creation).

### P2: Parallelize --fast mode (~6x speedup for fast mode)

**Impact:** --fast currently gets 0 parallelism benefit.

**Change:** Route `--fast` through the existing `check_parallel()` / `check_sequential()` paths instead of the separate `check_fast_phase1()` loop. The storage backend already supports fingerprint-only mode (`StorageBackend::Fingerprint`), so this requires wiring the parallel explorer to use it.

### P3: Reduce Value::kind() dispatch overhead

**Impact:** 13.1% self-time.

**Options:**
1. **Likely-branch hints** on Int/Bool fast paths (dominant types)
2. **Specialize hot loops**: fingerprint computation, bytecode dispatch, and hash should have monomorphized paths for common type combinations
3. **Profile-guided optimization (PGO)**: Build with instrumentation on Raft, then rebuild with profile data. This lets LLVM optimize branch prediction and inlining across the 12-way tag dispatch.

### P4: IntMap optimization for Dict[Int, *] patterns

**Impact:** Moderate — avoids Vec<(Value, Value)> for integer-keyed dicts.

Raft variables like `currentTerm: Dict[Int, Int]` with keys `0..N` could be represented as a flat `Vec<Value>` indexed by key, eliminating key storage and key hashing entirely. The compiler already has `TAG_INTMAP` for `Vec<i64>` but not for `Vec<Value>`.

### P5: Arena-pool for State::vars Vec allocation

**Impact:** 0.9% allocation time, marginal.

The arena allocation for VM buffers (`VmBufs`) is already done. The remaining allocation overhead is from `Vec<Value>` creation for new states. A pooled allocator (e.g., `typed-arena` or object pool) could eliminate this, but the 0.9% impact makes it low priority.

## 5. Mode Selection Guide

| Scenario | Recommended mode | Rationale |
|----------|-----------------|-----------|
| Default exploration | `full` | Fastest multi-threaded throughput, full traces |
| Memory-constrained (>10M states) | `--fast` | 33% less memory, no traces. **Currently single-threaded only** — apply P2 fix for parallel throughput |
| Memory-constrained (with traces) | `--tree` | 7% less memory than full, tree compression |
| Small state spaces (<100K) | `full` | Overhead of compression not worthwhile |
| Debugging (trace needed) | `full` or `--collapse` | Both support trace reconstruction |

## 6. Summary

The single biggest optimization opportunity is **replacing SipHash with ahash for fingerprint hashing** (P0). This addresses 51.7% of CPU time with a one-line change. Combined with hash memoization (P1), this could yield a 2-4x overall throughput improvement.

The second structural issue is **--fast mode lacking parallelism** (P2), which makes it paradoxically the slowest mode in multi-threaded scenarios despite doing less work per state.

The NaN-boxing and arena allocation changes from this session provide a solid foundation. The NaN-boxing reduced Value size from 32 bytes to 8 bytes, and the arena allocation eliminated per-eval Vec allocations. The tree compression provides a new storage option with better structural sharing, though its throughput overhead (~30% slower than full mode) means it's best suited for memory-constrained scenarios with large state spaces.
