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

Faster than TLC (the standard TLA+ model checker) on all benchmarks tested. Written in Rust with a bytecode VM, incremental fingerprinting, guard indexing, and parallel BFS.

With parallelism: 1M+ states/second on typical workloads.

## Examples

| | |
|---|---|
| [Raft consensus](specl/examples/benchmark/01-raft/raft.specl) | Leader election + log replication (1.58M states) |
| [Percolator](specl/examples/benchmark/14-percolator/percolator.specl) | Google's distributed transactions with snapshot isolation (4.2M states) |
| [Parallel Commits](specl/examples/benchmark/15-parallel-commits/parallel-commits.specl) | CockroachDB's parallel commit protocol (13.3M states) |
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

## Claude Code Integration

Specl includes an expert skill for [Claude Code](https://code.claude.com) that teaches Claude how to write, debug, and verify Specl specifications.

### Installation

**Option 1: Load as plugin** (recommended for easy updates)

```bash
claude --plugin-dir /path/to/specl
```

Skills will be namespaced: `/specl:expert-specl`

**Option 2: Install skill only** (lightweight)

```bash
./install-skill.sh
```

Skills will be available without namespace: `/expert-specl`

### Usage

Claude will automatically use the skill when you:
- Work with `.specl` files
- Ask about model checking or formal verification
- Mention distributed protocols (Raft, Paxos, 2PC, etc.)
- Debug invariant violations or deadlocks

Or invoke it directly:
```
/expert-specl help me model a consensus protocol
```

See [PLUGIN.md](PLUGIN.md) for distribution and publishing options.

## Development

```bash
cargo test --workspace && cargo clippy --workspace
```

## License

[PolyForm Noncommercial 1.0.0](LICENSE) — free for non-commercial use. See [commercial licensing](COMMERCIAL-LICENSE.md) for commercial use. Contact **contact@danwt.com**.
