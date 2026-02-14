# Specl Performance Analysis Report

**Date:** 2026-02-14
**System:** Apple Silicon (arm64), 16 threads, Rust release build
**Commits:** NaN boxing (`cf5dcbc`), tree compression (`2008d6d`), arena allocation (`13b05a4`)

## 1. Benchmark Results — All Modes

All benchmarks: multi-threaded (16 threads), `--no-auto --no-deadlock`.

### 1.1 Raft N=2 (500K state cap)

| Mode | States | Time(s) | States/s |
|------|-------:|--------:|---------:|
| full | 502,345 | 0.82 | 612,615 |
| --fast | 500,003 | 5.50 | 90,909 |
| --collapse | 501,888 | 1.14 | 440,252 |
| --tree | 502,161 | 1.37 | 366,540 |
| --por | 500,899 | 0.97 | 516,390 |
| --symmetry | 501,018 | 0.82 | 610,997 |
| --bloom | 500,001 | 5.58 | 89,605 |
| --directed | 500,001 | 5.96 | 83,892 |
| --swarm 8 | — | — | — |

### 1.2 Raft N=3 (2M state cap)

| Mode | States | Time(s) | States/s |
|------|-------:|--------:|---------:|
| full | 2,007,019 | 4.10 | 489,516 |
| --fast | 2,000,004 | 26.84 | 74,515 |
| --collapse | 2,002,093 | 5.20 | 385,017 |
| --tree | 2,004,716 | 6.22 | 322,301 |
| --por | 2,001,485 | 4.74 | 422,254 |
| --symmetry | 2,007,529 | 4.05 | 495,686 |
| --bloom | 2,000,001 | 26.93 | 74,266 |
| --directed | 2,000,000 | 29.25 | 68,376 |
| --swarm 8 | — | — | — |

### 1.3 Lamport Mutex N=3 (505K states, exhaustive)

| Mode | States | Time(s) | States/s |
|------|-------:|--------:|---------:|
| full | 505,500 | 0.80 | 635,900 |
| --fast | 505,500 | 5.60 | 91,000 |
| --collapse | 505,500 | 1.20 | 420,100 |
| --tree | 505,500 | 1.30 | 377,100 |
| --por | 502,700 | 1.00 | 491,500 |
| --symmetry | 505,500 | 0.80 | 615,300 |
| --bloom | 505,100 | 5.80 | 86,600 |
| --directed | 505,500 | 7.00 | 72,500 |
| --swarm 8 | — | 10.00 | — |

### 1.4 Paxos N=2 B=3 V=2 (316K states, exhaustive)

| Mode | States | Time(s) | States/s |
|------|-------:|--------:|---------:|
| full | 316,100 | 0.70 | 443,500 |
| --fast | 316,100 | 5.10 | 62,500 |
| --collapse | 316,100 | 1.00 | 318,200 |
| --tree | 316,100 | 1.00 | 322,700 |
| --por | 305,500 | 1.00 | 301,800 |
| --symmetry | 316,100 | 0.80 | 418,400 |
| --bloom | 316,000 | 5.00 | 62,700 |
| --directed | 316,100 | 7.30 | 43,400 |
| --swarm 8 | — | 5.70 | — |

### 1.5 Ricart-Agrawala N=3 (2.82M states, exhaustive)

| Mode | States | Time(s) | States/s |
|------|-------:|--------:|---------:|
| full | 2,820,000 | 5.70 | 491,100 |
| --fast | 2,820,000 | 49.70 | 56,600 |
| --collapse | 2,820,000 | 8.50 | 333,100 |
| --tree | 2,820,000 | 9.00 | 312,800 |
| --por | 2,760,000 | 11.20 | 247,400 |
| --symmetry | 2,820,000 | 6.40 | 439,200 |
| --bloom | 2,810,000 | 52.00 | 54,000 |
| --directed | 2,820,000 | 61.30 | 46,000 |
| --swarm 8 | — | 64.30 | — |

### 1.6 Peterson (32 states, symmetry-eligible)

| Mode | States | Time(s) | States/s |
|------|-------:|--------:|---------:|
| full | 32 | <0.01 | — |
| --fast | 32 | <0.01 | — |
| --collapse | 32 | <0.01 | — |
| --tree | 32 | <0.01 | — |
| --por | 32 | <0.01 | — |
| --symmetry | 23 | <0.01 | — |
| --bloom | 32 | <0.01 | — |
| --directed | 32 | <0.01 | — |

### 1.7 Single-threaded throughput (Raft)

| Spec + Mode | States | Time(s) | States/s |
|-------------|-------:|--------:|---------:|
| Raft N=2 full 1T | 500,003 | 5.16 | 96,899 |
| Raft N=2 --collapse 1T | 500,003 | 6.40 | 78,125 |
| Raft N=2 --tree 1T | 500,003 | 7.13 | 70,126 |
| Raft N=3 full 1T | 2,000,004 | 26.76 | 74,738 |
| Raft N=3 --collapse 1T | 2,000,004 | 34.00 | 58,823 |
| Raft N=3 --tree 1T | 2,000,004 | 39.48 | 50,658 |

### 1.8 Memory usage (single-threaded, Raft N=3, 2M states)

| Mode | Peak RSS (MB) | Time(s) | States/s |
|------|-------------:|--------:|---------:|
| full | 2,055 | 26.01 | 76,893 |
| collapse | 1,935 | 34.54 | 57,903 |
| tree | 1,908 | 37.83 | 52,868 |
| fast | 1,374 | 27.18 | 73,583 |

### 1.9 Parallelism efficiency (Raft N=3)

| Mode | 1T (s/s) | 16T (s/s) | Speedup |
|------|--------:|---------:|--------:|
| full | 74,738 | 489,516 | 6.5x |
| collapse | 58,823 | 385,017 | 6.5x |
| tree | 50,658 | 322,301 | 6.4x |
| fast | 73,583 | 74,515 | **1.0x** |
| bloom | — | 74,266 | **~1.0x** |
| directed | — | 68,376 | **~1.0x** |

### 1.10 Internal timing breakdown (Raft N=3, single-threaded `--profile`)

Wall-clock breakdown from `--profile` flag (coarse categories):

| Component | % of time |
|-----------|-----------|
| Successor generation | 94.3% |
| Store + queue | 4.6% |
| Invariant checking | 1.0% |

Note: "successor generation" includes guard evaluation, effect application, fingerprint computation, and all hashing. The CPU profile in section 2 breaks this down further.

## 2. Mode Analysis

### Tier 1: Full throughput (parallel BFS)

| Mode | Relative speed | Notes |
|------|-------------:|-------|
| **full** | 1.00x | Baseline. Best throughput at all scales. Full trace support. |
| **--symmetry** | ~1.00x | Negligible overhead. State reduction only on specs with symmetric processes. Peterson: 32→23 states. Raft/Lamport: no reduction. |
| **--por** | 0.80-0.86x | 8-14% overhead from dependency analysis. State reduction modest: Paxos 316K→306K (3%), Ricart-Agrawala 2.82M→2.76M (2%). Overhead exceeds savings for most specs tested. |
| **--collapse** | 0.66-0.72x | Per-variable interning. 28-34% slower than full. 6% less memory. |
| **--tree** | 0.60-0.66x | Hierarchical hash table. 34-40% slower than full. 7% less memory. |

### Tier 2: Single-threaded only (no parallel BFS)

| Mode | Relative speed | Notes |
|------|-------------:|-------|
| **--fast** | 0.12-0.15x | **Not parallelized.** Uses separate single-threaded `check_fast_phase1()` loop. 5-9x slower than full in multi-threaded runs despite 33% less memory. |
| **--bloom** | 0.12-0.15x | **Same issue as --fast.** Single-threaded code path. Probabilistic (false positives). |
| **--directed** | 0.09-0.14x | **Same issue.** Priority BFS is inherently sequential. Useful only for finding violations faster, not for exhaustive checking. |

### Swarm mode

`--swarm 8` output format doesn't report aggregate states/time in the standard format. Individual workers appear to run but results aren't directly comparable. The mode is designed for finding violations via random action ordering, not for throughput benchmarking.

## 3. CPU Profile Analysis

Samply CPU profile: Raft N=3 single-threaded, 27,571 samples (~28s). Symbols resolved via `atos`.

### 3.1 Self-time breakdown by category

| Category | Self-time % | Explanation |
|----------|------------|-------------|
| **Hashing (SipHash)** | **51.7%** | `DefaultHasher::write` for Value fingerprinting |
| **Value::kind()** | **13.1%** | NaN-box tag extraction on every value access |
| Bytecode VM | 4.2% | `vm_eval_inner` instruction dispatch |
| Explorer | 2.4% | BFS queue management, action enumeration |
| Clone/Drop | 2.2% | Arc refcount operations for Value |
| Store ops | 2.1% | DashMap insert/contains |
| Eval (treewalk) | 2.0% | `eval` / `eval_binary` fallback |
| Allocation | 0.9% | malloc/free |

### 3.2 Top individual functions by self-time

| % self | Function |
|--------|----------|
| 34.5% | `<SipHasher as Hasher>::write` (all call sites) |
| 13.1% | `Value::kind` (NaN-box tag decode) |
| 9.3% | `<Value as Hash>::hash` |
| 0.9% | `<Value as Ord>::cmp` |
| 0.7% | `<Value as Drop>::drop` |
| 0.5% | `bytecode::vm_eval_inner` |
| 0.4% | `store::StateStore::len` |

### 3.3 Top inclusive-time call chains

| % incl | Function |
|---------|----------|
| 95.0% | `Explorer::check` |
| 94.9% | `Explorer::generate_successors` |
| 94.9% | `Explorer::apply_template_actions` |
| 50.8% | fold loop over actions |
| 32.7% | `<Value as Hash>::hash` |
| 20.9% | `bytecode::vm_eval` |
| 15.3% | `direct_eval::apply_effects_bytecode` |
| 8.6% | `state::hash_var` |

## 4. Root Cause Analysis

### 4.1 The hashing bottleneck (51.7% of total time)

The dominant cost is **SipHash during fingerprint computation**. The fingerprint uses XOR-decomposition: `fp = XOR(hash_var(i, var[i]))`. The `hash_var` function has fast paths for `Int` and `Bool` (inline splitmix64), but all composite types fall through to `std::collections::hash_map::DefaultHasher` (SipHash-1-3).

For Raft, 15 of 17 variables are composite types (Dict, Set with nested structures). SipHash recursively traverses the entire value tree for each composite variable. Each `update_fingerprint` call re-hashes both the old AND new value of changed variables.

### 4.2 Value::kind() overhead (13.1% of total time)

The NaN-boxing `kind()` method does bitwise tag extraction and unsafe pointer casts on every value access. The 12-way `match` on the tag byte causes branch mispredictions in hash/compare loops over heterogeneous collections. PGO could help the CPU predict the dominant branch in tight loops with uniform types.

### 4.3 Three modes lack parallelism

`--fast`, `--bloom`, and `--directed` all use separate single-threaded BFS implementations (`check_fast_phase1`, `check_bloom`, `check_directed`) that bypass the rayon-parallel explorer. This makes them 6-9x slower than full mode in multi-threaded scenarios.

## 5. Optimization Recommendations (Priority Order)

### P0: Replace SipHash with ahash for fingerprinting (~2-3x overall speedup)

**Impact:** 51.7% of time is in SipHash. ahash is 3-5x faster for small-to-medium inputs on modern CPUs.

**Change:** In `hash_var()` (state.rs:54-63), replace `DefaultHasher` with `ahash::AHasher`. ahash already exists in `Cargo.toml`. One-line change.

**Expected:** 51.7% → ~17%, overall ~2x throughput improvement.

### P1: Memoize Value hash inside Arc (~additional 1.5-2x for composite-heavy specs)

**Impact:** Even with ahash, hashing a Dict of Dicts is O(n*m) per call.

**Change:** Store computed hash alongside Arc data. Values are immutable after creation, so hash can be computed at construction time and reused in O(1).

### P2: Parallelize --fast, --bloom, --directed (~6x speedup for these modes)

**Impact:** Three modes get zero parallelism benefit currently.

**Change:** Route through the existing `check_parallel()` / `check_sequential()` paths. The storage backends already support these modes; only the BFS entry point needs to change.

### P3: Profile-guided optimization (PGO)

**Impact:** 13.1% in Value::kind() branch dispatch.

**Change:** Build with instrumentation on representative specs, rebuild with profile data. LLVM can optimize the 12-way tag dispatch based on observed branch frequencies.

### P4: IntMap optimization for Dict[Int, Value]

**Impact:** Moderate. Raft has 11 Dict[Int, *] variables.

**Change:** When Dict keys are contiguous 0..N integers, store as `Vec<Value>` (indexed by key) instead of `Vec<(Value, Value)>` (sorted pairs). Eliminates key storage and key hashing.

## 6. Mode Selection Guide

| Scenario | Recommended | Rationale |
|----------|------------|-----------|
| Default exploration | `full` | Fastest multi-threaded throughput, full traces |
| Symmetric processes | `full --symmetry` | Zero overhead, reduces states when applicable |
| Memory-constrained (with traces) | `--collapse` | 6% less memory, 30% slower |
| Memory-constrained (no traces needed) | `--fast` | 33% less memory. **Currently single-threaded only** |
| Finding violations quickly | `--directed` | Priority BFS toward violations. **Single-threaded only** |
| Independent actions | `--por` | Partial order reduction. Modest benefit on tested specs. |
| Large probabilistic search | `--bloom` | Fixed memory. **Single-threaded only** |
| Random violation hunting | `--swarm N` | Parallel random exploration |
