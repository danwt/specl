# Tips and FAQ

## General tips

**Start small.** Begin with 2 processes and small bounds. State spaces grow exponentially — verify correctness first, then scale up.

**Use `--no-deadlock` for protocols.** Most distributed protocols have states where no action is enabled (all messages delivered, nothing to do). This is normal, not a bug.

**Read the trace.** When the checker finds a violation, each step shows the action, parameters, and resulting state. This is your primary debugging tool.

**Bounded model checking.** Constants like `MaxTerm=3` bound the exploration. OK with `MaxTerm=3` means no bug within that bound. Increase bounds for higher confidence.

**Use `--fast` for large state spaces.** Fingerprint-only mode uses 8 bytes/state. Can't produce traces, but tells you if a violation exists. If it finds one, re-run without `--fast` to get the trace.

**Use `--por` for independent processes.** Partial order reduction dramatically shrinks the state space when processes interact infrequently.

## State space scaling guide

| Constant change | Typical growth |
|-----------------|----------------|
| N: 2 -> 3 | 10-100x |
| N: 3 -> 4 | 100-1000x |
| MaxRound/MaxBallot: +1 | 5-50x |
| Values: +1 | 2-10x |

Typical sizes:

```
N=2, small bounds:    ~1K-100K states
N=3, small bounds:    ~100K-10M states
N=4, small bounds:    ~10M-1B states (use --fast)
```

## Common pitfalls

### Range expressions in parameters

Range expressions in parameters cannot use arithmetic:

```specl
// WRONG
action Act(i: 0..N+1) { ... }

// RIGHT: define a constant
const LIMIT: Int
action Act(i: 0..LIMIT) { ... }
```

### `any` is boolean, not a binder

`any` returns `true` or `false`. You cannot use the bound variable outside:

```specl
// WRONG: v not in scope
let v = any v in 0..N: state[v] == 2 in state[v]

// RIGHT: use fix to bind a value
let v = fix v in 0..N: state[v] == 2
```

### `implies` precedence in nested quantifiers

Use explicit parentheses:

```specl
// Potentially confusing
all i in 0..N: all j in 0..N: A and B implies C

// Clear
all i in 0..N: all j in 0..N: (A and B) implies C
```

### Empty dict type inference

`{}` is inferred as an empty set, not an empty dict:

```specl
// WRONG: type error
var state: Dict[Int, Int]
init { state = {} }

// RIGHT: empty range comprehension
init { state = {i: 0 for i in 1..0} }
```

### No has_key()

Pre-populate all keys and use sentinel values:

```specl
init { state = {i: 0 for i in 0..N} }     // 0 = absent
action AddKey(i: 0..N) {
    require state[i] == 0
    state = state | {i: 1}
}
```

### Double assignment

Each variable can only be assigned once per action:

```specl
// WRONG
action Bad() { x = 1 and x = 2 }

// Model atomically instead
action Good() { x = 2 }
```

### require after assignment

All `require` statements must come before any assignments:

```specl
// WRONG
action Bad() { x = x + 1 and require y > 0 }

// RIGHT
action Good() { require y > 0; x = x + 1 }
```
