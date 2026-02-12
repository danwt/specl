---
name: expert-specl
description: >
  Expert for Specl, a modern specification language and model checker for concurrent and distributed
  systems. Covers the full Specl language, CLI toolchain, distributed protocols (Raft, Paxos, consensus,
  BFT), concurrent algorithms, and formal verification. Use when: writing/debugging .specl files,
  modeling distributed systems, verifying safety properties, analyzing invariant violations, optimizing
  state space exploration, or translating TLA+. Keywords: specl, model checking, formal verification,
  TLA+, distributed systems, consensus, Raft, Paxos, BFT, invariants, state space, specification language.
---

# Specl — Specification Language & Model Checker

Specl is an exhaustive model checker for concurrent and distributed systems. Write a spec (state machine), and the checker explores every reachable state to verify invariants or produce minimal counterexample traces.

**Modern TLA+ alternative** with clean syntax, implicit frame semantics, and a fast Rust engine (1M+ states/second).

## Quick Reference

### Installation

```bash
# From Specl repo at /Users/danwt/Documents/repos/specl/specl
cargo install --path crates/specl-cli    # `specl` binary
cargo install --path crates/specl-lsp    # language server (optional)
```

**VSCode extension**: https://marketplace.visualstudio.com/items?itemName=specl.specl

### Essential Commands

```bash
specl check spec.specl -c N=3 -c MAX=10    # check with constants
specl check spec.specl --no-deadlock        # skip deadlock check (for protocols)
specl check spec.specl --fast               # fingerprint-only (10x less memory, no traces)
specl check spec.specl --por                # partial order reduction
specl check spec.specl --symmetry           # symmetry reduction
specl format spec.specl --write             # auto-format
specl watch spec.specl -c N=3              # re-check on save
specl translate spec.tla -o spec.specl     # TLA+ to Specl
```

### Minimal Example

```specl
module Counter
const MAX: 0..10
var count: 0..10
init { count = 0 }
action Inc() { require count < MAX; count = count + 1 }
action Dec() { require count > 0; count = count - 1 }
invariant Bounded { count >= 0 and count <= MAX }
```

Run: `specl check Counter.specl -c MAX=3` → explores all 4 states, verifies invariant.

## Critical Language Rules

- **`=`** assigns next-state (in actions). **`==`** compares (in guards/invariants).
- Variables not mentioned in an action stay unchanged (**implicit frame** — no UNCHANGED needed).
- Use `and` to update multiple variables atomically in one action.
- `require` is a guard/precondition. If false, action is skipped (not an error).
- Checker explores **ALL actions × ALL parameter combinations × ALL reachable states** via BFS.
- **ALL `require` statements MUST come BEFORE any assignments** in an action.

## Language Reference

### Module Structure

```specl
module Name

const C: Int              // set at check time: -c C=5
var x: 0..10              // state variable with type bound

init { x = 0 }            // initial state (one block)

action Step() { ... }     // state transition

func Helper(a) { ... }    // pure function (no state modification)

invariant Safe { ... }    // must hold in every reachable state
```

### Types

| Type | Example | Notes |
|------|---------|-------|
| `Bool` | `true`, `false` | |
| `Int` | `42`, `-7` | Unbounded |
| `Nat` | `0`, `100` | Non-negative |
| `0..10` | | Inclusive range of ints |
| `Set[T]` | `{1, 2, 3}` | Finite set |
| `Seq[T]` | `[a, b, c]` | Ordered list (0-indexed) |
| `Dict[K, V]` | `{k: 0 for k in 0..N}` | Map from keys to values |
| `String` | `"red"` | String literal |

### Operators

| Category | Operators |
|----------|-----------|
| Logical | `and`, `or`, `not`, `implies`, `iff` |
| Comparison | `==`, `!=`, `<`, `<=`, `>`, `>=` |
| Arithmetic | `+`, `-`, `*`, `/`, `%` |
| Set | `in`, `not in`, `union`, `intersect`, `diff`, `subset_of` |
| Sequence | `++` (concat), `head(s)`, `tail(s)`, `len(s)`, `s[i]` (index) |
| Conditional | `if ... then ... else ...` (expression — always requires else) |

### Dicts (The Workhorse)

Model N processes with state via dicts. Create with comprehension, update with `|` (merge):

```specl
var role: Dict[Int, Int]
init { role = {p: 0 for p in 0..N} }
action Promote(i: 0..N) { role = role | {i: 2} }
```

**Multi-key update:**
```specl
balance = balance | { from: balance[from] - amt, to: balance[to] + amt }
```

**Nested dict update** (e.g., `votesGranted[i][j]`):
```specl
votesGranted = votesGranted | {i: votesGranted[i] | {j: true}}
```

**Empty dict initialization** (avoid type inference error):
```specl
// ❌ WRONG: {} is inferred as Set
var state: Dict[Int, Int]
init { state = {} }  // Type error!

// ✅ CORRECT: Use empty range comprehension
init { state = {i: 0 for i in 1..0} }
```

### Parameterized Actions

Checker tries ALL valid parameter combinations in every reachable state:

```specl
action Transfer(from: 0..N, to: 0..N, amount: 1..MAX) {
    require from != to
    require balance[from] >= amount
    balance = balance | { from: balance[from] - amount, to: balance[to] + amount }
}
```

### Quantifiers

```specl
all x in 0..N: P(x)       // universal: true if P holds for ALL x
any x in 0..N: P(x)       // existential: true if P holds for SOME x
```

Work in invariants, guards, and any expression.

### Set Comprehensions

```specl
{p in 0..N if state[p] == 1}                    // filter
len({v in 0..N if votedFor[v] == i})             // count matching
len({v in 0..N if voted[v]}) * 2 > N + 1         // majority quorum check
```

### Functions

Pure, no state modification, used for reusable logic:

```specl
func LastLogTerm(l) { if len(l) == 0 then 0 else l[len(l) - 1] }
func Quorum(n) { (n / 2) + 1 }
func Min(a, b) { if a <= b then a else b }
```

## Common Modeling Patterns

### Process Ensemble

```specl
var state: Dict[Int, Int]
init { state = {i: 0 for i in 0..N} }
action Act(p: 0..N) { state = state | {p: newVal} }
```

### Message Passing

Encode messages as sequences (tuples), store in a set:

```specl
var msgs: Set[Seq[Int]]
init { msgs = {} }

// Message format: [type, src, dst, payload...]
action Send(src: 0..N, dst: 0..N, term: Int) {
    require role[src] == CANDIDATE
    msgs = msgs union {[1, src, dst, term]}  // RequestVote
}

action Receive(src: 0..N, dst: 0..N, term: Int) {
    require [1, src, dst, term] in msgs
    // handle message...
}
```

### Quorum Checking

```specl
// Simple majority (2f+1 out of N)
len({v in 0..N if votes[v]}) * 2 > N + 1

// Byzantine quorum (2f+1 out of 3f+1)
len({i in 0..N if signed[i]}) >= (N * 2) / 3 + 1
```

### Encoding Enums

Use integer constants with comments:

```specl
// Roles: 0=Follower, 1=Candidate, 2=Leader
var role: Dict[Int, 0..2]
action BecomeCandidate(i: 0..N) {
    require role[i] == 0  // Follower
    role = role | {i: 1}  // → Candidate
}
```

### Multiple Variable Updates

Use `and` to update multiple variables atomically:

```specl
action Reset() {
    x = 0
    and y = 0
    and z = 0
}
```

## Modelling Approach

1. **Identify state.** What variables fully describe the system? For N processes, use `Dict[Int, ...]`.
2. **Identify actions.** What transitions can happen? Use parameters for nondeterminism.
3. **Write guards.** `require` restricts when actions fire.
4. **Write invariants.** Safety properties that must always hold.
5. **Start small.** Use N=2 or N=3, small bounds. State spaces grow exponentially.

## CLI Flags Reference

| Flag | Effect | When to Use |
|------|--------|-------------|
| `-c KEY=VAL` | Set constant value | Always (e.g., `-c N=3 -c MaxTerm=2`) |
| `--no-deadlock` | Don't report deadlocks | Protocols with quiescent states (most distributed protocols) |
| `--fast` | Fingerprint-only (no traces, 8 bytes/state) | Large state spaces (>1M states), or when memory-constrained |
| `--por` | Partial order reduction | Independent processes/actions (e.g., message passing) |
| `--symmetry` | Symmetry reduction | Identical processes (homogeneous systems) |
| `--no-parallel` | Single-threaded | Debugging, deterministic output |
| `--threads N` | Set thread count | Fine-tune parallelism |
| `--max-states N` | Stop after N states | Testing, time limits |
| `--max-depth N` | Limit exploration depth | Bounded verification |
| `--memory-limit N` | Max memory in MB | Resource limits |
| `--write` | (format) Write in place | Auto-formatting |

## Analyzing Results

### OK Result

```
Result: OK
  States explored: 1,580,000
  Distinct states: 1,580,000
  Max depth: 47
  Time: 19.0s (83K states/s)
```

All reachable states satisfy all invariants. No deadlocks (unless `--no-deadlock`).

### Invariant Violation

```
Result: INVARIANT VIOLATION
  Invariant: Consistency
  Trace (5 steps):
    0: init
    1: BecomeCandidate(i=0)
    2: RequestVote(src=0, dst=1)
    3: GrantVote(src=1, dst=0)
    ...
```

**How to debug:**
1. Read trace step-by-step (each step = one action + resulting state)
2. Identify which action caused violation
3. Check if guards are too weak (action shouldn't have fired)
4. Check if invariant is too strict (async timing issues)

### Deadlock

```
Result: DEADLOCK
  Trace (N steps):
    ...
```

A reachable state where no action is enabled. For protocols this is often expected (use `--no-deadlock`). For liveness/progress properties, reveals real bugs.

## Common Pitfalls & Solutions

| Pitfall | Solution |
|---------|----------|
| `=` vs `==` confusion | `=` assigns in actions, `==` compares in invariants/guards |
| Empty dict `{}` type error | Use `{i: 0 for i in 1..0}` for empty dict |
| `require` after assignment | ALL requires must come before ANY assignments |
| No `has_key()` function | Pre-populate dict with all keys, use `dict[k] == val` |
| State space explosion | Start with N=2, reduce ranges, use `--fast/--por/--symmetry` |
| Deadlock on protocol spec | Add `--no-deadlock` (quiescent states are expected) |
| Range with arithmetic in param | Can't use `0..N+1`, define `const MAX` instead |
| `any` used as binder | `any x: P(x)` is Bool, can't use `x` outside |
| Double assignment to variable | Model critical section atomically, don't acquire + release |
| Invariant fails due to async timing | Relax invariant or check fundamental property only |

## Performance Optimization

### State Space Estimation

**Factors:**
- Number of processes: Exponential impact (N=2 → N=3 can be 100× larger)
- Value ranges: Multiplicative (0..10 vs 0..5)
- Message sets: Combinatorial explosion
- Dict sizes: Cartesian product of all key-value combinations

**State space orders of magnitude:**
- 10-100 states: Tiny (Counter, simple locks)
- 100-10K states: Small (basic protocols, small N)
- 10K-100K states: Medium (realistic protocols with N=2)
- 100K-1M states: Large (use `--fast`)
- 1M+ states: Very large (use `--fast` + `--por` + `--symmetry`)

### Reduction Techniques

1. **Smaller constants:** N=2 instead of N=3 (100× reduction)
2. **Tighter types:** `0..3` instead of `Int`
3. **Bounded collections:** `require len(msgs) < 10`
4. **Abstraction:** Model at right level (don't model implementation details)
5. **Symmetry reduction:** `--symmetry` flag (all processes identical)
6. **Partial order reduction:** `--por` flag (independent actions)
7. **Fast mode:** `--fast` (8 bytes/state, no traces)

### Optimization Workflow

```bash
# 1. Start small, verify correctness
specl check spec.specl -c N=2 -c MaxTerm=1

# 2. Scale up slightly
specl check spec.specl -c N=2 -c MaxTerm=2

# 3. Add partial order reduction if needed
specl check spec.specl -c N=2 -c MaxTerm=2 --por

# 4. Use fast mode for large spaces
specl check spec.specl -c N=3 -c MaxTerm=2 --por --fast

# 5. Add symmetry if applicable
specl check spec.specl -c N=3 -c MaxTerm=2 --por --symmetry --fast
```

## TLA+ Comparison

| TLA+ | Specl |
|------|-------|
| `x' = x + 1` | `x = x + 1` |
| `x = y` (equality) | `x == y` |
| `UNCHANGED <<y, z>>` | *(implicit)* |
| `/\`, `\/`, `~` | `and`, `or`, `not` |
| `\in`, `\notin` | `in`, `not in` |
| `\A x \in S: P(x)` | `all x in S: P(x)` |
| `\E x \in S: P(x)` | `any x in S: P(x)` |
| `[f EXCEPT ![k] = v]` | `f \| { k: v }` |
| `Init == ...` | `init { ... }` |
| `Next == A \/ B` | *(implicit — all actions OR'd)* |

**Key advantages over TLA+:**
- Cleaner syntax (no backslash operators)
- Implicit frame semantics (no UNCHANGED)
- Faster model checker (Rust vs Java)
- Better type inference
- Integrated toolchain (formatter, LSP, watch mode)

## Examples Repository

**Location:** `/Users/danwt/Documents/repos/specl/specl/examples/`

### Showcase (`examples/showcase/`)

Curated protocol specs reviewed for faithfulness and invariant coverage:
- `raft.specl` — Raft consensus (async, Vanlightly model)
- `paxos.specl` — Single-decree Paxos (Synod)
- `comet.specl` — CometBFT/Tendermint BFT with Byzantine faults
- `simplex.specl` — Simplex consensus (TCC 2023)
- `percolator.specl` — Google Percolator (snapshot isolation)
- `mesi.specl` — MESI cache coherence
- `redlock.specl` — Redis Redlock bug-finding (Kleppmann attack)
- `swim.specl` — SWIM failure detection
- `chandy-lamport.specl` — Consistent snapshot algorithm
- `TwoPhaseCommit.specl` — Classic 2PC
- `narwhal_tusk.specl` — Narwhal/Tusk DAG consensus (design reference)

### Other (`examples/other/`)

Additional specs: beginner examples, semaphore puzzles (prefixed `sem-`), stress tests, simplified protocol models, and more.

## Use Cases

### ✅ Good Fit

- **Distributed consensus protocols** (Raft, Paxos, Byzantine agreement)
- **Distributed transactions** (2PC, snapshot isolation, serializable isolation)
- **Byzantine fault tolerance** (PBFT, BFT consensus)
- **Concurrent algorithms** (locks, semaphores, barriers, queues)
- **Safety property verification** (mutual exclusion, consistency, linearizability)
- **Cache coherence protocols** (MESI, MOESI)
- **Network protocols** (alternating bit, sliding window)
- **Finding minimal counterexamples** (shortest path to violation)
- **Small-to-medium state spaces** (< 10M states, or larger with `--fast`)

### ❌ Not a Good Fit

- **Liveness properties** (fairness, eventual consistency) — TLA+ with fairness better suited
- **Infinite state spaces** without abstraction — use theorem proving (Coq, Isabelle)
- **Performance modeling** — use simulation or queueing theory
- **Smart contract logic** — use Solidity analyzers (Slither, Mythril)
- **Real-time systems** — use timed automata (UPPAAL)
- **Probabilistic systems** — use PRISM or Storm
- **Very large state spaces** without reduction techniques (>100M states)

## Key Insights

### Why Specl Over TLA+?

- **Cleaner syntax** — no backslash operators, implicit frame
- **Faster checker** — Rust vs Java, 1M+ states/second
- **Better tooling** — formatter, LSP, watch mode, integrated translator
- **Better type inference** — less type annotation needed
- **Lower barrier to entry** — simpler syntax, clearer error messages

### When to Use Model Checking

- **Finding bugs in protocols** — exhaustive search finds corner cases
- **Verifying safety properties** — proves invariants hold in all reachable states
- **Understanding protocol behavior** — traces show actual execution paths
- **Bounded verification** — proves correctness within bounds (term, log length, etc.)

### Limitations

- **State space explosion** — exponential growth with N processes
- **Bounded model checking** — correctness proven only within bounds
- **No liveness** — can't prove "eventually" properties (use TLA+ with fairness)
- **Abstraction required** — must model at right level (not too detailed)

## Project Structure

```
/Users/danwt/Documents/repos/specl/specl/
├── crates/
│   ├── specl-syntax/   # Lexer, parser, AST, pretty-printer
│   ├── specl-types/    # Type checker
│   ├── specl-ir/       # IR, bytecode compiler, guard indexing
│   ├── specl-eval/     # Tree-walk evaluator + bytecode VM
│   ├── specl-mc/       # BFS explorer, parallel via rayon, state store
│   ├── specl-tla/      # TLA+ parser and translator
│   ├── specl-cli/      # CLI (the `specl` binary)
│   └── specl-lsp/      # Language server
├── examples/
│   ├── easy/           # 12 beginner examples
│   ├── realistic/      # 16 mid-complexity examples
│   └── benchmark/      # 18 production protocols
└── editors/            # VSCode extension

/Users/danwt/Documents/repos/specl/examples/
├── semaphores/         # 13 semaphore puzzles
└── realistic/          # narwhal_tusk.specl
```

## Resources

- **Specl repo:** `/Users/danwt/Documents/repos/specl`
- **Main examples:** `/Users/danwt/Documents/repos/specl/specl/examples/`
- **Semaphore puzzles:** `examples/other/sem-*.specl`
- **VSCode extension:** https://marketplace.visualstudio.com/items?itemName=specl.specl
- **Manual:** https://danieltisdall.com/specl
- **Announcement:** https://danieltisdall.com/blog/2026-02-11-0028
