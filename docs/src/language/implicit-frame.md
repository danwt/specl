# Implicit Frame

Variables not mentioned in an action stay unchanged automatically. There is no `UNCHANGED` clause.

```specl
var x: 0..10
var y: 0..10
var z: 0..10

// Only x changes. y and z are preserved automatically.
action IncX() { x = x + 1 }
```

In TLA+, you would write `UNCHANGED <<y, z>>`. In Specl, this is implicit.

## Why this matters

Implicit frame semantics eliminate an entire class of bugs: forgetting to list a variable in `UNCHANGED`. In large specs with many variables, this is a common source of errors in TLA+. In Specl, it simply cannot happen.

## When a variable does change

A variable changes only when it appears on the left side of `=` in an action:

```specl
action Transfer(amount: 1..10) {
    require alice >= amount
    alice = alice - amount           // alice changes
    and bob = bob + amount           // bob changes
    // all other variables unchanged
}
```
