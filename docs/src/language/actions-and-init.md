# Actions and Init

## Init block

The `init` block defines the initial state. Every variable must be assigned.

```specl
init {
    count = 0
    and active = true
    and role = {p: 0 for p in 0..N}
}
```

Use `and` between assignments in the init block. There is exactly one init block per module.

## Actions

Actions are state transitions. The checker explores all enabled actions in every reachable state.

```specl
action Inc() {
    require count < MAX
    count = count + 1
}
```

An action consists of:
1. **Guards** (`require` statements) — preconditions that must be true for the action to fire
2. **Assignments** (`=`) — next-state values for variables

All `require` statements must come before any assignments.

## Parameterized actions

Actions can take parameters. The checker tries **all valid parameter combinations** in every reachable state:

```specl
action Transfer(from: 0..N, to: 0..N, amount: 1..MAX) {
    require from != to
    require balance[from] >= amount
    balance = balance | { from: balance[from] - amount, to: balance[to] + amount }
}
```

With `N=2, MAX=5`, the checker explores every combination of `from` (0,1,2), `to` (0,1,2), and `amount` (1,2,3,4,5) in every state. This models nondeterminism — the checker handles all interleavings.

## Multiple variable updates

Use `and` to update multiple variables atomically:

```specl
action Reset() {
    x = 0
    and y = 0
    and z = 0
}
```

Each variable can only be assigned **once** per action:

```specl
// WRONG: double assignment
action Bad() {
    x = x + 1 and
    x = x - 1              // ERROR: variable 'x' assigned multiple times
}
```

## Implicit action composition

All actions are implicitly OR'd. The checker's next-state relation is: in every state, try all actions (with all parameter combinations), and follow each enabled one to its successor state. There is no explicit `Next == Action1 \/ Action2 \/ ...` like in TLA+.
