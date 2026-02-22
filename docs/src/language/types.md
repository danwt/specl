# Types

## Primitive types

| Type | Values | Notes |
|------|--------|-------|
| `Bool` | `true`, `false` | |
| `Int` | `..., -2, -1, 0, 1, 2, ...` | Unbounded integers |
| `Nat` | `0, 1, 2, ...` | Non-negative integers |
| `String` | `"red"`, `"blue"` | String literals |

## Range types

`L..H` — integers from `L` to `H` inclusive.

```specl
var count: 0..10        // values 0, 1, 2, ..., 10
var phase: 0..3         // values 0, 1, 2, 3
const N: 1..5           // N can be 1 through 5
```

Ranges can use constants:

```specl
const N: Int
var index: 0..N         // depends on the value of N at check time
```

Range expressions in parameters cannot use arithmetic. Use a constant instead:

```specl
// Invalid
action Act(i: 0..N+1) { ... }

// Valid
const LIMIT: Int
action Act(i: 0..LIMIT) { ... }
```

## Compound types

### `Set[T]`

Finite sets.

```specl
var voters: Set[Int]
init { voters = {} }                          // empty set
init { voters = {1, 2, 3} }                   // literal
init { voters = {x in 0..N if active[x]} }    // comprehension
```

### `Seq[T]`

Ordered sequences (0-indexed).

```specl
var log: Seq[Int]
init { log = [] }                  // empty
init { log = [1, 2, 3] }          // literal
```

### `Dict[K, V]`

Maps from keys to values. The primary data structure for modelling per-process state.

```specl
var role: Dict[Int, Int]
init { role = {p: 0 for p in 0..N} }    // comprehension
```

See the dedicated [Dicts](./dicts.md) page for full details.

### `Option[T]`

Optional values.

```specl
var leader: Option[Int]
init { leader = None }

action Elect(i: 0..N) {
    leader = Some(i)
}
```

### `(T1, T2)` — Tuples

```specl
var pair: (Int, Bool)
init { pair = (0, true) }
```

## Type aliases

Give a name to a type expression for readability:

```specl
type NodeId = 0..N
type Role = 0..2
type Log = Seq[Int]

var currentTerm: Dict[NodeId, Nat]
var role: Dict[NodeId, Role]
var log: Dict[NodeId, Log]
```
