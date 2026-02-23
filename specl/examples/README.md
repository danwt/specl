# Specl Examples

## Directory Structure

| Directory | Description |
|-----------|-------------|
| `showcase/` | 10 curated examples covering all language features — the first place to look |
| `other/` | 100+ additional specs — protocols, puzzles, stress tests, semaphore problems |
| `regression/` | Bug-report regression specs — one `.specl` per GitHub issue |

The sibling `benchmarks/` directory contains TLC comparison scripts (`.tla`, `.cfg`, `.sh`) for performance benchmarking against TLC — it has no `.specl` files.

## Showcase

> **New to specl?** Start with **[features.specl](showcase/features.specl)** — a single spec that demonstrates every language construct with inline comments explaining each one.

The showcase is a small, carefully chosen set of examples that together:
- Cover all commonly-used language features
- Represent diverse, practical domains
- Range from trivial to strenuous
- Demonstrate both BFS and symbolic checking

| Spec | Domain | Lines | What it demonstrates |
|------|--------|-------|----------------------|
| [Peterson](showcase/peterson.specl) | Mutual exclusion | 70 | Dict, Bool, range types, parameterized actions, guards, invariants |
| [Dining Philosophers](showcase/dining-philosophers.specl) | Concurrency | 43 | Modular arithmetic `%`, multi-key dict update |
| [Two-Phase Commit](showcase/two-phase-commit.specl) | Transactions | 96 | `const`, `all`/`any` quantifiers, `implies` |
| [G-Counter](showcase/g-counter.specl) | CRDTs | 78 | Nested dicts, `let` bindings, `func`, dict comprehension with conditional |
| [MESI](showcase/mesi.specl) | Cache coherence | 146 | Full dict comprehension with `if/then/else`, hardware domain |
| [Paxos](showcase/paxos.specl) | Consensus | 95 | `powerset`, set comprehensions, complex nested quantifiers |
| [Redlock](showcase/redlock.specl) | Distributed locking | 153 | `Set`, `union`, intentional invariant violation (Kleppmann attack) |
| [Raft](showcase/raft.specl) | Consensus (complex) | 386 | `Seq`, `Set[Seq[Int]]`, `++`, slicing, `head`/`tail`/`len`, `union`/`diff`, message passing |
| [Token Ring + View](showcase/token-ring-view.specl) | State abstraction | 40 | `view` declaration for state projection, auxiliary variable elimination |
| **[Features](showcase/features.specl)** | **Language reference** | **199** | **Every construct: all types, set/dict/seq ops, `let`, `fix`, `powerset`, `union_all`, `keys`/`values`, `iff`, `implies`, tuples, `view`, `auxiliary invariant`, nondeterministic init** |

### Verification Results

Quick checks (all pass in under 1 second):

| Spec | Check Command | States |
|------|---------------|--------|
| Peterson | `specl check peterson.specl --no-deadlock` | 17 |
| Dining Philosophers | `specl check dining-philosophers.specl --no-deadlock` | ~100 |
| Two-Phase Commit | `specl check two-phase-commit.specl -c N=2 --no-deadlock` | 134 |
| G-Counter | `specl check g-counter.specl -c N=2 -c Max=3 --no-deadlock` | 54K |
| MESI | `specl check mesi.specl -c C=2 -c V=1 --no-deadlock` | 34 |
| Paxos | `specl check paxos.specl -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock` | 316K |
| Redlock | `specl check redlock.specl -c N=2 -c M=1 -c TTL=3 -c MaxTime=8` | violation in 15 steps |
| Raft | `specl check raft.specl -c N=1 -c MaxVal=0 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=2 --no-deadlock` | 956 |
| Token Ring + View | `specl check token-ring-view.specl -c N=4 -c MaxSteps=20 --no-deadlock --bfs` | 4 (view projects away `steps`) |
| Features | `specl check features.specl --no-deadlock --bfs --no-auto` | 88 |

Strenuous checks (minutes at larger parameters):

| Spec | Mode | Params | Result |
|------|------|--------|--------|
| Raft | BFS | N=2, MaxVal=1, MaxElections=2, MaxRestarts=0, MaxLogLen=3 | 166M states, ~4 min |
| Paxos | BFS | N=3, MaxBallot=3, V=2 | 3.35M states, ~9s |
| Paxos | symbolic | N=10, MaxBallot=10, V=3 | k-induction, ~90s |

Bug-finding:

| Spec | Check Command | Bug Found |
|------|---------------|-----------|
| [Redlock](showcase/redlock.specl) | `-c N=2 -c M=1 -c TTL=3 -c MaxTime=8` | MutualExclusion violated — Kleppmann's attack: locks expire while client is paused, second client acquires majority |

### Notes

- **Raft** does not support symbolic mode (uses `Set[Seq[T]]` for message passing).
- **Paxos** is the best example for exercising both modes: BFS at N=3+, symbolic at N=10+.
- **MESI** has an inherently small state space (4 cache states per core) — even C=10 produces only hundreds of states.

## Scaling Guide

State spaces grow exponentially with constants. Start small:

| Constant increase | Typical state space growth |
|-------------------|---------------------------|
| N: 2 → 3 | 10-100x |
| N: 3 → 4 | 100-1000x |
| MaxRound/MaxBallot: +1 | 5-50x |
| Values: +1 | 2-10x |

Use `--fast` (fingerprint-only, 10x less memory) for large state spaces. Use `--por` for specs with independent actions.

## Language Features Quick Reference

### Empty dict literal

`{:}` is the canonical empty dict literal. Prefer it over workarounds like `{i: 0 for i in 1..0}`.

```specl
var msgs: Dict[0..N, Set[0..N]]
init { msgs = {i: {} for i in 0..N}; }  // each node starts with empty set
```

### Set[T] operations

`Set[T]` supports: `union` (`union`), `intersect` (`intersect`), `diff` (`diff`), membership (`in`, `not in`), `subset_of`, `len()`, `powerset()`, `union_all()`, and set comprehension with filter (`{x in S if P}`).

```specl
var held: Set[0..N]
held = held union {k};           // add element
held = held diff {k};            // remove element
require k in held;               // membership test
len(held intersect other) == 0   // disjointness check
{i in 0..N if owner[i] == c}    // set comprehension
```

See [Redlock](showcase/redlock.specl), [Kaspa](showcase/kaspa.specl), [Features](showcase/features.specl).

### Tuple types

`(T1, T2)` tuple type with positional field access `.0`, `.1`, etc.

```specl
var pair: (Bool, 0..3)
init { pair = (false, 0); }
action Step() { pair = (true, pair.1 + 1); }
```

### if-then-else expressions

Inline `if c then t else f` works anywhere an expression is allowed — guards, effects, function bodies, dict comprehensions.

```specl
mode = if len(held) == 0 then 1 else mode;
{c: (if c == core then 3 else 0) for c in 0..C}
```

See [MESI](showcase/mesi.specl) (dict comprehension), [Raft](showcase/raft.specl) (functions), [Features](showcase/features.specl) (effects).

### Nondeterministic init

Init is predicate-based. Omit the constraint for a variable to get all valid initial states — the checker enumerates every value in the variable's type domain.

```specl
var mode: 0..2
init {
    // mode intentionally unconstrained: checker explores mode=0, mode=1, mode=2
}
```

See [Features](showcase/features.specl).

### View abstraction

`view { var1, var2 }` projects the state space onto a subset of variables. States identical on view variables are deduplicated even if they differ on other variables. Useful for eliminating auxiliary bookkeeping variables that don't affect safety.

```specl
var has_token: Dict[0..N, Bool]
var steps: 0..MaxSteps          // auxiliary counter
view { has_token }              // only has_token matters for state deduplication
```

See [Token Ring + View](showcase/token-ring-view.specl).

## Regression Tests

Every bug report gets a `.specl` file in `regression/` and a test in `crates/specl-cli/tests/regression_integration.rs` **before** the fix:

1. File the GitHub issue (e.g. #69)
2. Create `examples/regression/issue-69-short-description.specl` with a minimal reproducer
3. Add `// Use:` comment with constants if needed
4. Add test(s) in `regression_integration.rs` that fail without the fix
5. Fix the bug — tests now pass
6. Commit the spec, the test, and the fix together

Naming convention: `issue-{N}-{kebab-case-description}.specl`

Existing regression specs: issues #69 (in operator in quantifier body), #70 (type inference for untyped func params), #72 (not in operator), #73 (type inference for builtins).
