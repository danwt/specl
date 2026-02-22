# Specl Language Reference

## Module Structure

```specl
module Name
const C: Int              // set at check time: -c C=5
var x: 0..10              // state variable with type bound
init { x = 0 }            // initial state (one block)
action Step() { ... }     // state transition
func Helper(a) { ... }    // pure function (no state modification)
invariant Safe { ... }    // must hold in every reachable state
```

## Types

| Type | Example | Notes |
|------|---------|-------|
| `Bool` | `true`, `false` | |
| `Int` | `42`, `-7` | Unbounded |
| `Nat` | `0`, `100` | Non-negative int |
| `0..10` | | Inclusive range of ints |
| `Set[T]` | `{1, 2, 3}` | Finite set |
| `Seq[T]` | `[a, b, c]` | Ordered list (0-indexed) |
| `Dict[K, V]` | `{k: 0 for k in 0..N}` | Map from keys to values |
| `String` | `"red"` | String literal |

## Operators

| Category | Operators |
|----------|-----------|
| Logical | `and`, `or`, `not`, `implies`, `iff` |
| Comparison | `==`, `!=`, `<`, `<=`, `>`, `>=` |
| Arithmetic | `+`, `-`, `*`, `/`, `%` |
| Set | `in`, `not in`, `union`, `intersect`, `diff`, `subset_of` |
| Sequence | `++` (concat), `head(s)`, `tail(s)`, `len(s)`, `s[i]` (index) |
| Conditional | `if ... then ... else ...` (expression — always requires else) |

## Dicts

Create with comprehension:

```specl
var role: Dict[Int, Int]
init { role = {p: 0 for p in 0..N} }
```

Update with `|` (merge):

```specl
role = role | {i: 2}                                               // one key
balance = balance | { from: balance[from] - amt, to: balance[to] + amt }  // multiple keys
votesGranted = votesGranted | {i: votesGranted[i] | {j: true}}     // nested dict
```

Access: `role[i]`, `votesGranted[i][j]`

**Empty dict initialization:**

```specl
// ❌ Error: cannot unify dict[Int, Int] and Set[?0]
var state: Dict[Int, Int]
init { state = {} }

// ✅ Fix: Use empty range comprehension
init { state = {i: 0 for i in 1..0} }
```

Reason: `{}` is ambiguous — could be empty set or empty dict. Specl infers set by default.

## Parameterized Actions

Checker tries ALL valid parameter combinations in every reachable state:

```specl
action Transfer(from: 0..N, to: 0..N, amount: 1..MAX) {
    require from != to
    require balance[from] >= amount
    balance = balance | { from: balance[from] - amount, to: balance[to] + amount }
}
```

## Guards

`require` is a precondition. If false, the action is skipped (not an error):

```specl
action Eat(p: 0..2) {
    require philState[p] == 1
    require fork[p] == true and fork[(p + 2) % 3] == true
    philState = philState | { p: 2 }
    and fork = fork | { p: false, (p + 2) % 3: false }
}
```

**ALL `require` statements MUST come BEFORE any assignments:**

```specl
// ❌ Parse error
action Bad() {
    x = x + 1 and
    require y > 0
}

// ✅ Correct: All requires first
action Good() {
    require y > 0
    x = x + 1
}
```

## Quantifiers

```specl
all x in 0..N: P(x)       // universal: true if P holds for ALL x
any x in 0..N: P(x)       // existential: true if P holds for SOME x
```

Work in invariants, guards, and any expression.

**Note:** `any` is a boolean quantifier, NOT a binder — you cannot use the bound variable outside the quantifier expression.

## Set Comprehensions

```specl
{p in 0..N if state[p] == 1}                    // filter
len({v in 0..N if votedFor[v] == i})             // count matching
len({v in 0..N if voted[v]}) * 2 > N + 1         // quorum check
```

## Let Bindings

Local definitions within expressions:

```specl
let x = len(log[i]) in
    if x == 0 then 0 else log[i][x - 1]

// Nested lets
let a = foo(x) in
let b = bar(y) in
    a + b

// In invariants
invariant Safe {
    all i in 0..N:
        let t = currentTerm[i] in
        t >= 0 and t <= MaxTerm
}
```

## Functions

Pure, no state modification, used for reusable logic:

```specl
func LastLogTerm(l) { if len(l) == 0 then 0 else l[len(l) - 1] }
func Quorum(n) { (n / 2) + 1 }
func Max(a, b) { if a > b then a else b }
func Min(a, b) { if a <= b then a else b }
```

## Multiple Variable Updates

Use `and` to update multiple variables atomically:

```specl
action Reset() {
    x = 0
    and y = 0
    and z = 0
}
```

**Important:** Cannot assign to the same variable twice in one action:

```specl
// ❌ WRONG: Double assignment
action Bad() {
    mutex = mutex - 1 and
    count = count + 1 and
    mutex = mutex + 1  // ERROR!
}

// ✅ CORRECT: Model atomically
action Good() {
    require mutex > 0
    count = count + 1
}
```

## Common Patterns

### Process Ensemble

Model N processes with state via dicts:

```specl
var state: Dict[Int, Int]
init { state = {i: 0 for i in 0..N} }
action Transition(p: 0..N) { state = state | {p: newVal} }
```

### Message Passing

Encode messages as sequences (tuples), store in a set:

```specl
var msgs: Set[Seq[Int]]
init { msgs = {} }

// Message types: [1, src, dst, term] = RequestVote
//                [2, src, dst, term, granted] = RequestVoteResponse
action SendRequestVote(src: 0..N, dst: 0..N) {
    require role[src] == CANDIDATE
    msgs = msgs union {[1, src, dst, currentTerm[src]]}
}

action ReceiveRequestVote(src: 0..N, dst: 0..N, term: Int) {
    require [1, src, dst, term] in msgs
    // Process request...
    msgs = msgs union {[2, dst, src, currentTerm[dst], 1]}  // grant vote
}
```

### Quorum Patterns

```specl
// Simple majority (N=3, need 2)
len({i in 0..N if voted[i]}) * 2 > N + 1

// Byzantine quorum (N=3f+1, need 2f+1)
len({i in 0..N if certified[i]}) >= (N * 2) / 3 + 1

// Check if specific value has quorum
len({i in 0..N if vote[i] == v}) * 2 > N + 1
```

### Encoding Enums

Use integer constants with comments:

```specl
// Roles: 0=Follower, 1=Candidate, 2=Leader
var role: Dict[Int, 0..2]
action BecomeCandidate(i: 0..N) { require role[i] == 0; role = role | {i: 1} }
```

### Nondeterministic Choice

Use action parameters:

```specl
// Checker explores all possible values
action ChooseValue(v: 0..MAX_VALUE) {
    require state == INIT
    chosen = v
}
```

### Bounded Collections

Prevent state space explosion:

```specl
action Send(msg: Seq[Int]) {
    require len(msgs) < MAX_MSGS  // Bound message queue
    msgs = msgs union {msg}
}
```

### Leader Election

```specl
func Leader(term) { term % N }  // Deterministic leader

action CheckLeader(i: 0..N, term: Int) {
    require i == Leader(term)
    require role[i] == CANDIDATE
    role = role | {i: LEADER}
}
```

### Log Replication

```specl
// Append entries to log
action AppendEntries(follower: 0..N, leader: 0..N, entries: Seq[Int]) {
    require role[leader] == LEADER
    require role[follower] == FOLLOWER
    require currentTerm[follower] == currentTerm[leader]
    log = log | {follower: log[follower] ++ entries}
}
```

## State Space Analysis

### Estimating State Space Size

**Factors:**
- Number of processes: Exponential impact (N=2 → N=3 can be 100× larger)
- Value ranges: Multiplicative (0..10 vs 0..5)
- Message sets: Combinatorial explosion
- Dict sizes: Cartesian product of all key-value combinations

**Examples:**
```
Counter (count: 0..10):                               11 states
Mutex (N=3, state: 0..5):                            ~56 states
Two-Phase Commit (2 RMs):                            ~hundreds of states
Raft (N=2, MaxTerm=2, MaxLogLen=2):                  ~1.58M states
Percolator (bounded):                                ~4.2M states
Parallel Commits:                                    ~13.3M states
```

### Reducing State Space

**Techniques:**

1. **Smaller constants:** N=2 instead of N=3 (100× reduction)
2. **Tighter types:** `0..3` instead of `Int`
3. **Bounded collections:** `require len(msgs) < 10`
4. **Abstraction:** Model at right level (not implementation details)
5. **Symmetry reduction:** `--symmetry` flag (all processes identical)
6. **Partial order reduction:** `--por` flag (independent actions)
7. **Fast mode:** `--fast` (8 bytes/state, no traces)

**Example progression:**

```bash
# Start small
specl check spec.specl -c N=2 -c MaxTerm=1

# Scale up
specl check spec.specl -c N=2 -c MaxTerm=2

# Add partial order reduction
specl check spec.specl -c N=2 -c MaxTerm=2 --por

# Use fast mode for large spaces
specl check spec.specl -c N=3 -c MaxTerm=2 --por --fast

# Add symmetry if applicable
specl check spec.specl -c N=3 -c MaxTerm=2 --por --symmetry --fast
```

## Common Pitfalls & Fixes

### Empty Dict Type Inference

```specl
// ❌ Error: cannot unify dict[Int, Int] and Set[?0]
var state: Dict[Int, Int]
init { state = {} }

// ✅ Fix: Use empty range comprehension
init { state = {i: 0 for i in 1..0} }
```

**Reason:** `{}` is ambiguous — could be empty set or empty dict. Specl infers set by default.

### No has_key() Function

```specl
// ❌ Undefined variable: has_key
action AddKey(i: 0..N) {
    require not has_key(state, i)
    state = state | {i: 1}
}

// ✅ Fix: Pre-populate all keys, use value check
init { state = {i: 0 for i in 0..N} }  // 0 = not present
action AddKey(i: 0..N) {
    require state[i] == 0
    state = state | {i: 1}
}
```

**Reason:** Specl doesn't have `has_key()`. Use pre-populated dicts with sentinel values.

### require After Assignment

```specl
// ❌ Parse error
action Bad() {
    x = x + 1 and
    require y > 0
}

// ✅ Fix: All requires first
action Good() {
    require y > 0
    x = x + 1
}
```

**Reason:** Guards (`require`) must come before assignments in actions.

### Double Assignment

```specl
// ❌ Error: variable 'x' assigned multiple times
action Bad() {
    x = x + 1 and
    x = x - 1
}

// ✅ Fix: Use single assignment or multiple actions
action Good() {
    x = x  // no-op, or use proper logic
}
```

**Reason:** Each variable can only be assigned once per action.

### Range with Arithmetic in Parameters

```specl
// ❌ Invalid: Can't use arithmetic in range
action Act(i: 0..N+1) { ... }

// ✅ Fix: Define constant
const MAX_INDEX: Int
action Act(i: 0..MAX_INDEX) { ... }
```

**Reason:** Range expressions in parameters can't use arithmetic.

### `any` Used as Binder

```specl
// ❌ Error: `v` is not in scope
let v = any v in 0..N: state[v] == 2 in
state[v]

// ✅ Fix: Use quantifier for boolean only
require any v in 0..N: state[v] == 2
```

**Reason:** `any` is a boolean quantifier, not a binder. Can't use the bound variable outside.

### State Space Explosion

```specl
// ❌ May not finish: huge state space
specl check spec.specl -c N=5

// ✅ Fix: Start small, use reduction techniques
specl check spec.specl -c N=2 --por --fast
```

**Reason:** State spaces grow exponentially. Always start with N=2 or N=3.

### Invariant Too Strict for Async Systems

```specl
// ❌ May fail due to async timing
invariant CountMatchesState {
    counter == len({i in 0..N if state[i] == ACTIVE})
}

// ✅ Fix: Relax to fundamental property
invariant CountBounded {
    counter >= 0 and counter <= N
}

// Or allow timing lag
invariant CountConsistent {
    counter >= len({i in 0..N if state[i] == ACTIVE}) - 1
}
```

**Reason:** In asynchronous systems, intermediate states can violate strict synchronization invariants.

## CLI Flags Reference

| Flag | Effect | When to Use |
|------|--------|-------------|
| `-c KEY=VAL` | Set constant value | Always (e.g., `-c N=3`) |
| `--no-deadlock` | Don't report deadlocks | Protocols with quiescent states |
| `--fast` | Fingerprint-only (no traces, 8 bytes/state) | Large state spaces (>1M states) |
| `--por` | Partial order reduction | Independent processes/actions |
| `--symmetry` | Symmetry reduction | Identical processes |
| `--no-parallel` | Single-threaded | Debugging, deterministic output |
| `--threads N` | Set thread count | Fine-tune parallelism |
| `--max-states N` | Stop after N states | Testing, time limits |
| `--max-depth N` | Limit depth | Bounded verification |
| `--memory-limit N` | Max memory in MB | Resource limits |
| `--write` | (format) Write in place | Auto-formatting |

## Performance Tips

**Start small, verify correctness, then scale:**

1. Test with N=2, small ranges
2. Verify invariants hold
3. Increase N to 3
4. Add `--por` if needed
5. Add `--fast` for large spaces
6. Add `--symmetry` if applicable

**Monitor state space growth:**

```bash
specl check spec.specl -c N=2  # ~1K-100K states
specl check spec.specl -c N=3  # ~100K-10M states
specl check spec.specl -c N=4  # ~10M-1B states - use --fast
```

**Optimization checklist:**

- [ ] Used tightest possible types (0..5 not Int)
- [ ] Started with N=2
- [ ] Bounded message/event queues
- [ ] Modeled at appropriate abstraction level
- [ ] Used `--por` for independent actions
- [ ] Used `--symmetry` for symmetric processes
- [ ] Used `--fast` for state spaces > 1M

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
