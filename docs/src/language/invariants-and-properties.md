# Invariants and Properties

## Invariants

An invariant is a boolean expression that must hold in **every reachable state**. If the checker finds a state where the invariant is false, it reports a violation with the shortest trace.

```specl
invariant Bounded { count >= 0 and count <= MAX }

invariant ElectionSafety {
    all i in 0..N: all j in 0..N:
        (role[i] == 2 and role[j] == 2 and currentTerm[i] == currentTerm[j])
            implies i == j
}
```

### Checking specific invariants

Use `--check-only` to check only named invariants:

```bash
specl check spec.specl --check-only ElectionSafety
```

### Writing good invariants

- **Be specific.** `count >= 0` is weaker than `count >= 0 and count <= MAX`. The more precise the invariant, the more bugs it catches.
- **Check structural properties.** "At most one leader per term" catches more bugs than "leaders exist".
- **Avoid overly strict invariants for async systems.** In asynchronous systems, intermediate states may violate strict synchronization invariants. Invariants should express fundamental safety properties, not implementation-specific timing assumptions.

```specl
// Too strict for async — may fail due to message delays
invariant Bad { counter == len({i in 0..N if state[i] == 1}) }

// Better — express the fundamental property
invariant Good { counter >= 0 and counter <= N }
```

## Properties

`property` declarations parse and type-check but are **not yet implemented** in the model checker. They are intended for temporal properties.

```specl
property EventuallyLeader { eventually any i in 0..N: role[i] == 2 }
```

See [Not Yet Implemented](./not-yet-implemented.md) for the full list of parsed-but-unimplemented features.
