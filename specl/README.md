# Specl

A specification language and model checker for concurrent and distributed systems.

Specl lets you write formal specifications and automatically verify safety properties using explicit-state model checking, symbolic verification (Z3), and partial order reduction.

## Install

### From GitHub Releases (recommended)

Download the latest binary for your platform from [Releases](https://github.com/danwt/specl/releases).

```bash
# Example: Linux x86_64
curl -L https://github.com/danwt/specl/releases/latest/download/specl-linux-x86_64 -o specl
chmod +x specl
sudo mv specl /usr/local/bin/
```

### From source

```bash
git clone https://github.com/danwt/specl.git
cd specl/specl
cargo install --path crates/specl-cli
```

## Quick start

```bash
# Check a spec
specl check examples/showcase/DieHard.specl

# Translate from TLA+
specl translate myspec.tla

# Analyze a spec
specl info examples/showcase/DieHard.specl

# Simulate random traces
specl simulate examples/showcase/DieHard.specl
```

## Documentation

- [Examples](examples/) — showcase specs and benchmarks
- [CHANGELOG](CHANGELOG.md) — release history
- [VS Code extension](editors/vscode/) — language server with go-to-definition, hover, rename, and more

## Versioning

Use tagged releases (`v2.0.1`, etc.) for stability. The `main` branch may contain unreleased changes.
