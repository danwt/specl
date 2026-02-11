<p align="center">
  <img src="assets/png/logo-256.png" alt="Specl" width="128">
</p>

<h1 align="center">Specl</h1>

<p align="center">
  <img src="https://img.shields.io/badge/License-PolyForm_Noncommercial-blue.svg" alt="License">
  <img src="https://img.shields.io/badge/Rust-1.75+-orange.svg" alt="Rust">
  <img src="https://img.shields.io/badge/Status-Alpha-yellow.svg" alt="Status">
</p>

A specification language and model checker for concurrent and distributed systems. Modern alternative to TLA+/TLC: clean syntax, implicit frame semantics, fast Rust engine.

**[Full manual](https://danieltisdall.com/specl)** | **[Announcement](https://danieltisdall.com/blog/2026-02-11-0028)** | **[VSCode Extension](https://marketplace.visualstudio.com/items?itemName=specl.specl)**

## Quick start

```bash
cargo install --path crates/specl-cli
specl check examples/easy/Counter.specl -c MAX=5
```

```specl
module Counter

const MAX: 0..10
var count: 0..10

init { count = 0 }

action Inc() { require count < MAX; count = count + 1 }
action Dec() { require count > 0; count = count - 1 }

invariant Bounded { count >= 0 and count <= MAX }
```

## Performance

Beats TLC on all benchmarks (single-thread, verified identical state counts):

| Benchmark | States | Specl | TLC | Speedup |
|-----------|--------|-------|-----|---------|
| Raft N=2 | 1.58M | 83K st/s | 40K | **2.1x** |
| Percolator C=2 K=2 | 4.2M | 104K st/s | 56K | **1.9x** |
| Counters N=4 MAX=9 | 100K | 253K st/s | 174K | **1.5x** |
| Parallel Commits K=2 | 13.3M | 115K st/s | 76K | **1.5x** |
| EPaxos R=2 | 757K | 118K st/s | 84K | **1.4x** |

With parallel BFS (8 threads): 1M+ states/second on Counters, 573K on Raft.

## Examples

| | |
|---|---|
| [Raft consensus](specl/examples/benchmark/01-raft/raft.specl) | Leader election + log replication (1.58M states) |
| [Percolator](specl/examples/benchmark/14-percolator/percolator.specl) | Google's distributed transactions with snapshot isolation (4.2M states) |
| [Parallel Commits](specl/examples/benchmark/15-parallel-commits/parallel-commits.specl) | CockroachDB's parallel commit protocol (13.3M states) |
| [Bronson AVL](specl/examples/benchmark/16-bronson-avl/bronson_avl.specl) | Concurrent AVL tree — finds rebalancing bug in 760K states (TLC needed 126M) |
| [EPaxos](specl/examples/benchmark/12-epaxos/epaxos.specl) | Egalitarian Paxos (757K states) |
| [Two-Phase Commit](specl/examples/benchmark/03-tpc/tpc.specl) | Classic distributed commit protocol |
| [Dining Philosophers](specl/examples/easy/DiningPhilosophers.specl) | Mutual exclusion with shared resources |
| [Traffic Light](specl/examples/easy/TrafficLight.specl) | Safety invariants for a traffic controller |

See also: [`examples/easy/`](specl/examples/easy/) (beginner), [`examples/realistic/`](specl/examples/realistic/) (mid-complexity), [`examples/benchmark/`](specl/examples/benchmark/) (production protocols).

## Toolchain

- **VSCode extension** — diagnostics, hover, completion, format-on-save ([Marketplace](https://marketplace.visualstudio.com/items?itemName=specl.specl))
- **Formatter** — `specl format spec.specl --write`
- **Watch mode** — `specl watch spec.specl -c N=3`
- **TLA+ translator** — `specl translate spec.tla -o spec.specl`

## Development

```bash
cargo test --workspace && cargo clippy --workspace
```

## License

[PolyForm Noncommercial 1.0.0](LICENSE) — free for non-commercial use. See [commercial licensing](COMMERCIAL-LICENSE.md) for commercial use. Contact **contact@danwt.com**.
