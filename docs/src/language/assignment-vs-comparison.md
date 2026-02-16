# Assignment vs Comparison

The single most important syntax rule in Specl:

- **`=`** assigns the next-state value (inside actions and init)
- **`==`** compares values (everywhere)

```specl
action SetX() { x = 5 }              // assign x to 5
invariant XIs5 { x == 5 }            // check if x equals 5
```

## In actions

`=` on the left side of a variable sets its next-state value:

```specl
action Inc() {
    count = count + 1              // next-state count = current count + 1
}
```

The right-hand side `count` reads the *current* state. The left-hand side `count` writes the *next* state. This is similar to TLA+'s `count' = count + 1`, but without the prime notation.

## In guards and invariants

`==` tests equality. It is a boolean expression:

```specl
action Act() {
    require role[i] == 2           // guard: only fire if role[i] is 2
    ...
}

invariant Safe { x == y }          // check: x equals y in every state
```

## Common mistake

Using `=` when you meant `==`, or vice versa:

```specl
// WRONG: this assigns x to 5, not checks equality
invariant Bad { x = 5 }

// RIGHT: this checks equality
invariant Good { x == 5 }
```

The type checker will catch many of these errors, but it's worth internalizing the distinction.
