# Dicts

Dicts are the workhorse data structure in Specl. They model per-process state, mappings, and any key-value structure.

## Creation

Create dicts with comprehensions:

```specl
var role: Dict[Int, Int]
var balance: Dict[Int, Int]

init {
    role = {p: 0 for p in 0..N}
    and balance = {a: 100 for a in 0..N}
}
```

This creates `{0: 0, 1: 0, 2: 0}` for `N=2`.

## Access

Access values by key:

```specl
role[i]                    // single key
votesGranted[i][j]         // nested dict
```

## Update with `|` (merge)

The `|` operator merges a dict into another, updating only the specified keys:

```specl
// Update one key
role = role | {i: 2}

// Update multiple keys
balance = balance | { from: balance[from] - amount, to: balance[to] + amount }
```

### Nested dict update

For nested dicts (e.g., `Dict[Int, Dict[Int, Bool]]`), update the inner dict:

```specl
votesGranted = votesGranted | {i: votesGranted[i] | {j: true}}
```

This updates `votesGranted[i][j]` to `true` without affecting other entries.

## Dict operations

| Operation | Syntax |
|-----------|--------|
| Access | `d[k]` |
| Merge/update | `d1 \| d2` |
| Keys | `keys(d)` |
| Values | `values(d)` |

## Empty dict initialization

`{}` is ambiguous — it could be an empty set or an empty dict. Specl defaults to set.

```specl
// WRONG: type error — {} inferred as empty set
var state: Dict[Int, Int]
init { state = {} }

// RIGHT: use empty range comprehension
init { state = {i: 0 for i in 1..0} }
```

The range `1..0` is empty, so this creates an empty dict with the correct type.

## No has_key()

Specl does not have a `has_key()` function. Instead, pre-populate all keys and use sentinel values:

```specl
// WRONG: has_key is undefined
require not has_key(state, i)

// RIGHT: pre-populate, check sentinel
init { state = {i: 0 for i in 0..N} }     // 0 = not present
action AddKey(i: 0..N) {
    require state[i] == 0
    state = state | {i: 1}
}
```

## Conditional comprehensions

Dict comprehensions can include conditions:

```specl
// Create dict with conditional values
var cache: Dict[Int, Int]
init {
    cache = {c: if c == 0 then 2 else 0 for c in 0..C}
}
```
