# Your First Spec

Here is a complete Specl specification — a bounded counter:

```specl
module Counter

const MAX: 0..10
var count: 0..10

init { count = 0 }

action Inc() { require count < MAX; count = count + 1 }
action Dec() { require count > 0; count = count - 1 }

invariant Bounded { count >= 0 and count <= MAX }
```

Save this as `counter.specl` and run:

```bash
specl check counter.specl -c MAX=3
```

```
Result: OK
  States explored: 4
  Max depth: 3
  Time: 0.00s
```

The checker explored all 4 reachable states (count = 0, 1, 2, 3) and verified the invariant in all of them.

## What each line means

- **`module Counter`** — every spec is a module with a name.
- **`const MAX: 0..10`** — a constant. Its value is set at check time with `-c MAX=3`. The type `0..10` means integers from 0 to 10 inclusive.
- **`var count: 0..10`** — a state variable. This is the state that the checker tracks.
- **`init { count = 0 }`** — the initial state. All variables must be assigned.
- **`action Inc()`** — a state transition. `require count < MAX` is a guard: the action can only fire when the condition is true. `count = count + 1` assigns the next-state value.
- **`action Dec()`** — another transition. The checker tries all enabled actions in every reachable state.
- **`invariant Bounded`** — a property that must hold in every reachable state. If violated, the checker produces the shortest trace to the violation.

## Key syntax rules

Two things to internalize immediately:

1. **`=` assigns, `==` compares.** Inside actions, `x = 5` sets the next-state value. In invariants and guards, `x == 5` tests equality.

2. **Implicit frame.** Variables not mentioned in an action stay unchanged. No `UNCHANGED` clause is needed. In the `Inc` action above, only `count` changes — if there were other variables, they would be preserved automatically.
