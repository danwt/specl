# Functions and Let Bindings

## Functions

Functions are pure — they cannot modify state. Use them for reusable logic.

```specl
func LastLogTerm(l) { if len(l) == 0 then 0 else l[len(l) - 1] }
func Quorum(n) { (n / 2) + 1 }
func Max(a, b) { if a > b then a else b }
func Min(a, b) { if a <= b then a else b }
```

Functions can be called from actions, invariants, guards, and other functions:

```specl
action BecomeLeader(i: 0..N) {
    require len({k in 0..N if votesGranted[i][k]}) >= Quorum(N + 1)
    role = role | {i: 2}
}

invariant LogConsistency {
    all i in 0..N: all j in 0..N:
        LastLogTerm(log[i]) == LastLogTerm(log[j])
            implies len(log[i]) == len(log[j])
}
```

## Let bindings

Local definitions within expressions. Two forms:

### Expression-level `let ... in`

```specl
let x = len(log[i]) in
    if x == 0 then 0 else log[i][x - 1]
```

Can be nested:

```specl
let a = foo(x) in
let b = bar(y) in
    a + b
```

### In invariants

```specl
invariant Safe {
    all i in 0..N:
        let t = currentTerm[i] in
        t >= 0 and t <= MaxTerm
}
```

### In guards

```specl
action Act(i: 0..N) {
    let lastIdx = len(log[i]) - 1
    require lastIdx >= 0
    require log[i][lastIdx] == currentTerm[i]
    ...
}
```

Let bindings improve readability by naming intermediate values and avoiding repeated subexpressions.
