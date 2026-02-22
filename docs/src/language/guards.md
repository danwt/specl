# Guards

`require` is a precondition. If the condition is false, the action cannot fire — the checker moves on to try other actions.

```specl
action Eat(p: 0..2) {
    require philState[p] == 1
    require fork[p] == true and fork[(p + 2) % 3] == true
    philState = philState | { p: 2 }
    and fork = fork | { p: false, (p + 2) % 3: false }
}
```

## Ordering rule

All `require` statements must come **before** any assignments:

```specl
// WRONG: require after assignment
action Bad() {
    x = x + 1 and
    require y > 0              // PARSE ERROR
}

// RIGHT: all requires first
action Good() {
    require y > 0
    x = x + 1
}
```

## Multiple guards

You can use multiple `require` statements. They are implicitly AND'd:

```specl
action Act(i: 0..N) {
    require role[i] == 1
    require currentTerm[i] < MaxTerm
    require len(votes[i]) * 2 > N + 1
    // ... assignments ...
}
```

This is equivalent to a single `require` with `and`:

```specl
require role[i] == 1 and currentTerm[i] < MaxTerm and len(votes[i]) * 2 > N + 1
```

Multiple separate `require` statements are preferred for readability.

## Guards vs invariants

Guards and invariants are both boolean expressions, but they serve different purposes:

- **Guards** restrict when an action can fire. A false guard is normal — it means the action is not applicable in that state.
- **Invariants** must hold in every reachable state. A false invariant is a bug — the checker reports a violation with a trace.

## Guard indexing

The checker optimizes parameterized actions by analyzing which guard conjuncts depend on which parameters. If an early guard fails, inner parameter combinations are skipped. This is automatic and does not affect the semantics.
