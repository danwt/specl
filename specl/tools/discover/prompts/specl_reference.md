# Specl Language Reference

Specl is a specification language for model-checking concurrent and distributed systems.

## Structure

Every spec is a module with constants, variables, init, actions, and invariants:

```specl
module Counter

const MAX: Int

var count: 0..10

init { count = 0 }

action Increment() {
    require count < MAX
    count = count + 1
}

invariant InRange { count >= 0 and count <= MAX }
```

## Critical Rules

- `=` assigns next-state value (inside actions). `==` compares values.
- Variables not mentioned in an action stay unchanged (no UNCHANGED needed).
- `require` is a guard. If false, the action cannot fire.
- The checker explores ALL actions in ALL reachable states with ALL parameter combinations.

## Types

| Type | Example |
|------|---------|
| `Bool` | `true`, `false` |
| `Int` | `42`, `-7` |
| `0..10` | Inclusive range |
| `Set[T]` | `{1, 2, 3}` |
| `Seq[T]` | `[a, b, c]` |
| `Dict[K, V]` | `{k: 0 for k in 0..N}` |
| `Option[T]` | `Some(x)`, `None` |
| `(T1, T2)` | Tuples |

## Dicts

Create with comprehension, update with `|` (merge):

```specl
var state: Dict[Int, Int]
init { state = {p: 0 for p in 0..N} }
action Update(i: 0..N) { state = state | {i: 1} }
```

Multi-key update: `d = d | { a: va, b: vb }`

## Parameterized Actions

```specl
action Transfer(from: 0..N, to: 0..N, amount: 1..MAX) {
    require from != to
    require balance[from] >= amount
    balance = balance | { from: balance[from] - amount, to: balance[to] + amount }
}
```

## Quantifiers

```specl
all x in 0..N: balance[x] >= 0       // true for ALL x
any x in 0..N: role[x] == 2          // true for SOME x
```

## Operators

- Logic: `and`, `or`, `not`, `implies`
- Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Set: `in`, `not in`, `union`, `intersect`, `diff`, `subset_of`
- Sequence: `++` (concat), `head(s)`, `tail(s)`, `len(s)`
- Dict: `keys(d)`, `values(d)`
- Conditional: `if ... then ... else ...` (expression, always needs else)

## Set Comprehensions

```specl
{p in 0..N if state[p] == 1}           // filter
len({v in 0..N if voted[v]}) * 2 > N   // count + quorum
```

## Functions

Pure, no state modification:

```specl
func Max(a, b) { if a > b then a else b }
```

## Let Bindings

```specl
let x = expr in body
```

## Example: Simple Mutex

```specl
module Mutex

const N: Int

var locked: Bool
var holder: 0..N

init {
    locked = false
    and holder = 0
}

action Acquire(p: 0..N) {
    require not locked
    locked = true
    and holder = p
}

action Release(p: 0..N) {
    require locked and holder == p
    locked = false
}

invariant OneHolder {
    not locked or (all p in 0..N: all q in 0..N: (holder == p and holder == q) implies p == q)
}
```

## Example: G-Counter CRDT

```specl
module GCounter

const N: Int

var counters: Dict[Int, Dict[Int, Int]]

init {
    counters = {r: {i: 0 for i in 0..N} for r in 0..N}
}

action Increment(r: 0..N) {
    counters = counters | {r: counters[r] | {r: counters[r][r] + 1}}
}

action Merge(src: 0..N, dst: 0..N) {
    require src != dst
    let merged = {i: if counters[src][i] > counters[dst][i] then counters[src][i] else counters[dst][i] for i in 0..N} in
    counters = counters | {dst: merged}
}

func Value(r) {
    let s = {counters[r][i] for i in 0..N} in
    // sum not available - use a different approach for your designs
    0
}

invariant MergeIdempotent {
    all r in 0..N: all s in 0..N:
        let merged = {i: if counters[r][i] > counters[s][i] then counters[r][i] else counters[s][i] for i in 0..N} in
        let double_merged = {i: if merged[i] > counters[s][i] then merged[i] else counters[s][i] for i in 0..N} in
        merged == double_merged
}
```

## Key Constraints

- Range expressions in parameters can't use arithmetic: `0..V+1` is invalid. Use a `const` instead.
- State spaces grow exponentially. Use N=2 or N=3 and small bounds.
- `any` is a boolean quantifier, NOT a binder.
