# Conditionals and Fix

## Conditional expressions

`if ... then ... else ...` is an expression — it always requires an `else` branch and returns a value.

```specl
let lastTerm = if len(log[i]) == 0 then 0 else log[i][len(log[i]) - 1]
```

```specl
var cache: Dict[Int, Int]
init {
    cache = {c: if c == 0 then 2 else 0 for c in 0..C}
}
```

```specl
invariant Safe {
    all i in 0..N:
        if role[i] == 2 then
            len({j in 0..N if votesGranted[i][j]}) * 2 > N + 1
        else
            true
}
```

Since `if/then/else` is an expression (not a statement), it can appear anywhere a value is expected: in dict comprehensions, function bodies, guards, invariants, and assignments.

## Fix expressions

`fix x in S: P(x)` picks a value from set `S` satisfying predicate `P`. The result is deterministic — the first satisfying element (in sorted order) is returned.

```specl
let leader = fix i in 0..N: role[i] == 2
```

Use `fix` when you need to bind a specific value to a variable, as opposed to `any` which only returns a boolean.

```specl
// any: boolean — does a leader exist?
require any i in 0..N: role[i] == 2

// fix: value — bind a specific leader
let leader = fix i in 0..N: role[i] == 2
```
