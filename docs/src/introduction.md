# Introduction

[Specl](https://github.com/danwt/specl) is a specification language and exhaustive model checker for concurrent and distributed systems. You describe what your system *should* do, and the model checker explores every reachable state to verify correctness — or gives you a step-by-step counterexample showing exactly how it fails.

## What is model checking?

Distributed systems fail in subtle ways. Race conditions, message reordering, partial failures, and Byzantine faults combine to produce behaviors that no amount of unit testing will catch. The state space is too large for random testing and too complex for manual reasoning.

A model checker solves this by **exhaustive exploration**: given a specification of your system's state machine, it systematically visits every reachable state and verifies that your safety properties hold in all of them. If a property is violated, you get the shortest trace — the exact sequence of actions — that leads to the bug.

This is how protocols like Raft, Paxos, and TiDB's transaction protocol are verified. Specl makes this process accessible with clean syntax and a fast Rust engine.

## Why Specl?

Specl is a modern replacement for [TLA+](https://lamport.azurewebsites.net/tla/tla.html)/TLC. The key improvements:

- **Clean syntax.** No backslash operators (`/\`, `\/`, `~`), no primed variables (`x'`), no `UNCHANGED`. Just `and`, `or`, `not`, `=` for assignment, `==` for comparison.
- **Implicit frame semantics.** Variables not mentioned in an action stay unchanged automatically.
- **Dict comprehensions.** The workhorse for modelling N processes with per-process state.
- **Fast Rust engine.** Bytecode-compiled VM, parallel BFS, incremental fingerprinting. Beats TLC on every benchmark.
- **Full toolchain.** VSCode extension with diagnostics/completion/hover, formatter, watch mode, TLA+ translator.

## Quick comparison with TLA+

| TLA+ | Specl |
|------|-------|
| `x' = x + 1` | `x = x + 1` |
| `x = y` (equality) | `x == y` |
| `UNCHANGED <<y, z>>` | *(implicit)* |
| `/\`, `\/`, `~` | `and`, `or`, `not` |
| `\A x \in S: P(x)` | `all x in S: P(x)` |
| `\E x \in S: P(x)` | `any x in S: P(x)` |
| `[f EXCEPT ![k] = v]` | `f \| { k: v }` |

If you're new to model checking, start with [Your First Spec](./getting-started/first-spec.md). If you're coming from TLA+, see the full [TLA+ Comparison](./tla-comparison/index.md).
