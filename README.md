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

**[Full manual](https://specl.danieltisdall.com)** | **[Announcement](https://danieltisdall.com/blog/2026-02-11-0028)** | **[VSCode Extension](https://marketplace.visualstudio.com/items?itemName=specl.specl)**

## Quick start

```bash
cargo install --path crates/specl-cli
specl check examples/other/Counter.specl -c MAX=5
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
| [Peterson](specl/examples/showcase/peterson.specl) | Mutual exclusion for 2 processes |
| [Dining Philosophers](specl/examples/showcase/dining-philosophers.specl) | Classic concurrency problem |
| [Two-Phase Commit](specl/examples/showcase/two-phase-commit.specl) | Distributed transaction protocol |
| [G-Counter](specl/examples/showcase/g-counter.specl) | Grow-only counter CRDT |
| [MESI](specl/examples/showcase/mesi.specl) | Cache coherence protocol |
| [Paxos](specl/examples/showcase/paxos.specl) | Single-decree Paxos (Synod) consensus |
| [Redlock](specl/examples/showcase/redlock.specl) | Distributed lock bug-finding (Kleppmann attack) |
| [Raft](specl/examples/showcase/raft.specl) | Leader election + log replication (Vanlightly's async model) |

See [`examples/`](specl/examples/) for the full catalogue (100+ specs) and verification results.

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

## Development

```bash
cargo test --workspace && cargo clippy --workspace
```

## License

[PolyForm Noncommercial 1.0.0](LICENSE) — free for non-commercial use. See [commercial licensing](COMMERCIAL-LICENSE.md) for commercial use. Contact **contact@danwt.com**.
