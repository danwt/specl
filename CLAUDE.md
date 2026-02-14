# Specl — Specification Language & Model Checker

Specl is a specification language and exhaustive model checker for concurrent and distributed systems. Modern replacement for TLA+/TLC with clean syntax, implicit frame semantics, and a fast Rust engine.

## Installation

```bash
git clone https://github.com/danwt/specl.git
cd specl/specl
cargo install --path crates/specl-cli    # gives you `specl` command
cargo install --path crates/specl-lsp    # optional: language server
```

VSCode extension: https://marketplace.visualstudio.com/items?itemName=specl.specl

## CLI Usage

```bash
specl check spec.specl -c N=3 -c MAX=10    # check with constants
specl check spec.specl --no-deadlock        # skip deadlock check (common for protocols)
specl check spec.specl --no-parallel        # single-threaded
specl check spec.specl --threads 4          # control parallelism
specl check spec.specl --max-states 100000  # limit exploration
specl check spec.specl --max-time 60        # time limit in seconds
specl check spec.specl --fast               # fingerprint-only (10x less memory, no traces)
specl check spec.specl --por                # partial order reduction
specl check spec.specl --symmetry           # symmetry reduction
specl check spec.specl --bloom              # bloom filter (fixed memory, probabilistic)
specl check spec.specl --directed           # priority BFS toward violations
specl check spec.specl --swarm 8            # parallel instances with shuffled orders
specl check spec.specl --check-only Safety  # only check named invariant(s)
specl check spec.specl --diff               # show only changed vars in traces
specl check spec.specl --output json        # JSON output
specl check spec.specl --output itf         # Apalache-compatible ITF trace
specl check spec.specl --output mermaid     # Mermaid sequence diagram
specl check spec.specl --output dot         # Graphviz DOT state graph (small specs only)
specl check spec.specl --profile            # per-action firing counts and timing
specl info spec.specl -c N=3               # analyze spec: state space, actions, optimizations
specl estimate spec.specl -c N=3           # estimate state space size and resources
specl test examples/                        # batch check all .specl files using // Use: comments
specl simulate spec.specl -c N=3           # random trace simulation
specl lint spec.specl                       # fast syntax + type + compile check (no MC)
specl format spec.specl --write             # format in place
specl watch spec.specl -c N=3              # re-check on file change
specl translate spec.tla -o spec.specl     # convert TLA+ to Specl
```

## Language Reference

### Structure

Every spec is a module with constants, variables, an init block, actions, and invariants:

```specl
module Name

const C: Int          // set at check time with -c C=5
var x: 0..10          // state variable

init { x = 0 }

action Step() { require x < C; x = x + 1 }

invariant Safe { x >= 0 and x <= C }
```

### Critical Syntax Rules

- **`=`** assigns next-state value (inside actions). **`==`** compares values.
- Variables not mentioned in an action stay unchanged (implicit frame — no UNCHANGED needed).
- Use `and` to update multiple variables in one action.
- `require` is a guard/precondition. If false, the action cannot fire.
- The checker explores ALL actions in ALL reachable states with ALL parameter combinations.

### Types

| Type | Example | Notes |
|------|---------|-------|
| `Bool` | `true`, `false` | |
| `Int` | `42`, `-7` | Unbounded |
| `Nat` | `0`, `100` | Non-negative |
| `0..10` | | Inclusive range |
| `Set[T]` | `{1, 2, 3}` | Finite set |
| `Seq[T]` | `[a, b, c]` | Ordered list |
| `Dict[K, V]` | `{k: 0 for k in 0..N}` | Map/function |
| `String` | `"red"` | String literal |
| `Option[T]` | `Some(x)`, `None` | Optional value |
| `(T1, T2)` | `(1, true)` | Tuples |

Type aliases: `type Name = TypeExpr`

### Dicts (the workhorse)

Model N processes with state via dicts. Create with comprehension, update with `|` (merge):

```specl
var role: Dict[Int, Int]
init { role = {p: 0 for p in 0..N} }
action Promote(i: 0..N) { role = role | {i: 2} }
```

Multi-key update: `balance = balance | { from: balance[from] - amt, to: balance[to] + amt }`

Nested dict update (e.g., `votesGranted[i][j]`): `votesGranted = votesGranted | {i: votesGranted[i] | {j: true}}`

### Parameterized Actions

The checker tries all valid parameter combinations:

```specl
action Transfer(from: 0..N, to: 0..N, amount: 1..MAX) {
    require from != to
    require balance[from] >= amount
    balance = balance | { from: balance[from] - amount, to: balance[to] + amount }
}
```

### Quantifiers

```specl
all x in 0..N: balance[x] >= 0       // universal: true for ALL x
any x in 0..N: role[x] == 2          // existential: true for SOME x
```

### Operators

| Category | Operators |
|----------|-----------|
| Logical | `and`, `or`, `not`, `implies`, `iff` |
| Comparison | `==`, `!=`, `<`, `<=`, `>`, `>=` |
| Arithmetic | `+`, `-`, `*`, `/`, `%` |
| Set | `in`, `not in`, `union`, `intersect`, `diff`, `subset_of` |
| Sequence | `++` (concat), `head(s)`, `tail(s)`, `len(s)`, `s[lo..hi]` (slice) |
| Dict | `keys(d)`, `values(d)` |
| Set | `powerset(s)`, `union_all(s)` |
| Choose | `choose x in S: P(x)` (pick a value satisfying P) |
| Conditional | `if ... then ... else ...` (expression, always needs else) |

### Set Comprehensions

```specl
{p in 0..N if state[p] == 1}                    // filter
len({v in 0..N if votedFor[v] == i})             // count
len({v in 0..N if voted[v]}) * 2 > N + 1         // quorum check
```

### Functions

Pure, no state modification:

```specl
func LastLogTerm(l) { if len(l) == 0 then 0 else l[len(l) - 1] }
func Quorum(n) { (n / 2) + 1 }
```

## How to Think About Modelling

### Core Idea

A spec defines a state machine: initial state + actions (transitions) + invariants (safety properties). The model checker exhaustively explores every reachable state via BFS. If an invariant is violated, it produces the shortest trace (sequence of actions) leading to the violation.

### Modelling Approach

1. **Identify the state.** What variables fully describe the system? For N processes, use `Dict[Int, ...]` keyed by process ID.
2. **Identify the actions.** What can happen? Each action is a possible state transition. Use parameters to model nondeterminism (e.g., which process acts, what value is chosen).
3. **Write guards.** `require` restricts when actions can fire. Model protocol preconditions here.
4. **Write invariants.** What must ALWAYS hold? Safety properties go here.
5. **Start small.** Use N=2 or N=3 and small bounds. State spaces grow exponentially. Verify correctness first, scale up for confidence.

### Common Patterns

**Process ensemble:** `var state: Dict[Int, Int]` with `action Act(p: 0..N) { ... state = state | {p: newVal} }`

**Message passing:** Model message sets as `var msgs: Set[Seq[Int]]` (sequences encode message fields). Add with `msgs = msgs union {[type, src, dest, payload]}`, consume with `require [type, src, dest, payload] in msgs`.

**Nondeterministic choice:** Use action parameters: `action Choose(v: 0..3)` — checker explores all values.

**Quorum:** `len({i in 0..N if votes[i]}) * 2 > N + 1`

**Encoding enums as ints:** `// 0=follower, 1=candidate, 2=leader` with `var role: Dict[Int, 0..2]`

### Language Constraints

- `let` bindings available: `let x = expr in body` for local definitions within expressions.
- `any` is a boolean quantifier, NOT a binder — can't use the bound variable outside.
- Range expressions in parameters can't use arithmetic: `0..V+1` is invalid. Add a `const MaxVal` instead.
- State spaces grow exponentially. Typical sizes: N=2 is ~100K-2M states, N=3 is ~10M-100M. Always start with N=2.
- `implies` inside nested `all` quantifiers has precedence issues — flatten: `all c: all k: (A and B) implies C`.
- `enabled(Action)`, `changes(var)`, `property`, `fairness`, temporal operators (`always`, `eventually`, `leads_to`) — parse and type-check but NOT yet in model checker.

## Analysing Results

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
  Invariant: MoneyConserved
  Trace (2 steps):
    0: init -> alice=10, bob=10
    1: BrokenDeposit -> alice=10, bob=15
```

The trace shows the shortest path to the violation. Each step shows which action fired and the resulting state. This is the primary debugging tool.

### Deadlock

```
Result: DEADLOCK
  Trace (N steps):
    ...
```

A reachable state where no action is enabled. For protocols this is often expected (use `--no-deadlock`). For mutual exclusion / liveness specs, this reveals real bugs.

### Tips

- **Use `--no-deadlock` for protocols.** Most distributed protocols have quiescent states.
- **Read the trace carefully.** Each step = one action firing. The trace is minimal.
- **Bounded model checking.** `MaxTerm=3` bounds exploration. OK within bound doesn't prove unbounded correctness, but finds most bugs.
- **Use `--fast` for large state spaces.** 8 bytes/state, can't produce traces, but tells you if a violation exists.
- **Use `--por` for independent processes.** Partial order reduction dramatically shrinks state space.

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

## Project Structure

```
specl/crates/
├── specl-syntax/   Lexer, parser, AST, pretty-printer
├── specl-types/    Type checker
├── specl-ir/       IR, bytecode compiler, guard indexing
├── specl-eval/     Tree-walk evaluator + bytecode VM
├── specl-mc/       BFS explorer, parallel via rayon, state store
├── specl-tla/      TLA+ parser and translator
├── specl-cli/      CLI (the `specl` binary)
└── specl-lsp/      Language server (the `specl-lsp` binary)
```

## Language Server (LSP)

The `specl-lsp` binary provides IDE support via the Language Server Protocol (36 unit tests):

- **Hover**: Declaration info for vars, consts, actions, funcs, types, invariants, properties
- **Completion**: Keywords, types, and symbols (vars, consts, actions, funcs, invariants) from the current file
- **Signature help**: Parameter info when typing inside `action()` or `func()` calls
- **Go-to-definition**: Jump to declaration of any identifier
- **Goto type definition**: Navigate from variable/const/param to its type alias declaration
- **Find all references**: Locate all uses of an identifier
- **Document highlight**: Highlight all occurrences of symbol under cursor (WRITE for declarations, READ for uses)
- **Rename**: Rename an identifier across the file (with prepare_rename validation)
- **Linked editing ranges**: Edit all occurrences of an identifier simultaneously (multi-cursor)
- **Document symbols**: Outline view of all declarations (with accurate multi-line ranges)
- **Workspace symbols**: Cross-file symbol search (`Ctrl+T` in VSCode)
- **Selection ranges**: Smart expand/shrink selection (declaration → file)
- **Call hierarchy**: Incoming/outgoing call relationships between actions and funcs
- **Inlay hints**: Parameter names shown inline at call sites (e.g. `Recovery(leader: 0, other: 2)`)
- **Code actions**: Insert templates for init blocks, actions, invariants; quick fix for undefined variables
- **Code lens**: Reference counts above action and func declarations (click to find all references)
- **Folding ranges**: Collapse declaration blocks and comment groups
- **Formatting**: Pretty-print the document
- **Semantic tokens**: Syntax highlighting (keywords, types, variables, functions, etc.)
- **Diagnostics**: Parse and type errors shown inline

## Examples

See `specl/examples/showcase/` (61 curated protocol specs — Raft, Paxos, EPaxos, CometBFT, Percolator, MESI, PBFT, SWIM, Narwhal-Tusk, Simplex, Redlock, Chandy-Lamport, G-Counter CRDT, PN-Counter CRDT, OR-Set CRDT, Vector Clocks, Lamport Clocks, Peterson, Dekker, Token Ring, Dining Philosophers, Chandy-Misra, Bakery, Reader-Writer, RW Write Preference, Leader Election, ABD Register, CAS Register, Lamport Mutex, Ricart-Agrawala, Ticket Lock, Byzantine Generals, RCU, Seqlock, Barrier, Two-Phase Locking, Two-Phase Commit, Three-Phase Commit, Bounded Buffer, WAL, Group Commit, Michael-Scott Queue, Treiber Stack, Work-Stealing Deque, Snapshot Isolation, Hazard Pointers, Epoch Reclamation, ABA Problem, Sleeping Barber, Dining Savages, Cigarette Smokers, Priority Inversion, Double-Checked Locking, Crash Consensus, Token Bucket, Circuit Breaker, Gossip Protocol, Map-Reduce, Reactor, Lease, etc.) and `specl/examples/other/` (additional specs, semaphore puzzles, stress tests).
