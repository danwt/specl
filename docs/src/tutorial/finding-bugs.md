# Finding Bugs

The real value of a model checker is not proving things correct — it's finding bugs you didn't know existed. Here's how that works in practice.

## A broken transfer protocol

```specl
module Transfer

var alice: 0..50
var bob: 0..50

init { alice = 10 and bob = 10 }

// BUG: adds money without taking from alice
action BrokenDeposit() { bob = bob + 5 }

action AliceToBob() {
    require alice >= 1
    alice = alice - 1 and bob = bob + 1
}

invariant MoneyConserved { alice + bob == 20 }
```

Run it:

```bash
specl check transfer.specl
```

```
Result: INVARIANT VIOLATION
  Invariant: MoneyConserved
  Trace (2 steps):
    0: init -> alice=10, bob=10
    1: BrokenDeposit -> alice=10, bob=15
```

The checker found the shortest path to the violation. The `BrokenDeposit` action creates money from nothing — exactly the kind of bug that a unit test might miss if it only tested `AliceToBob`.

## Reading traces

Each line in the trace shows:

1. **Step number** — 0 is always the initial state
2. **Action name** — which action fired (with parameters, if any)
3. **Resulting state** — the values of all variables after the action

The trace is **minimal**: the checker uses BFS, so it always finds the shortest path to any violation. This makes traces easy to read and reason about.

## Fixing the bug

The fix is straightforward — `BrokenDeposit` should deduct from Alice:

```specl
action Deposit() {
    require alice >= 5
    alice = alice - 5 and bob = bob + 5
}
```

Re-run and the checker reports `OK`.

## The pattern

1. Write a spec with the behavior you want to model
2. Write invariants that express what "correct" means
3. Run the checker
4. If it finds a violation, read the trace and fix the spec (or realize your invariant is wrong)
5. Iterate

This feedback loop is fast — for most specs the checker runs in under a second.
