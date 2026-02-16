# Dining Philosophers

The dining philosophers problem is a classic concurrency exercise: three philosophers sit around a table, each with a fork on either side. To eat, a philosopher needs both adjacent forks. The challenge is ensuring no two adjacent philosophers eat simultaneously.

## The spec

```specl
module DiningPhilosophers

// 0=thinking, 1=hungry, 2=eating
var philState: Dict[0..2, 0..2]
var fork: Dict[0..2, Bool]

init {
    philState = {p: 0 for p in 0..2}
    and fork = {f: true for f in 0..2}
}

action Hungry(p: 0..2) { require philState[p] == 0; philState = philState | { p: 1 } }

action Eat(p: 0..2) {
    require philState[p] == 1
    require fork[p] == true and fork[(p + 2) % 3] == true
    philState = philState | { p: 2 }
    and fork = fork | { p: false, (p + 2) % 3: false }
}

action Done(p: 0..2) {
    require philState[p] == 2
    philState = philState | { p: 0 }
    and fork = fork | { p: true, (p + 2) % 3: true }
}

invariant NoAdjacentEating {
    all p in 0..2: not (philState[p] == 2 and philState[(p + 1) % 3] == 2)
}
```

## Key language features demonstrated

### Parameterized actions

`action Hungry(p: 0..2)` — the checker tries this action with every value of `p` (0, 1, 2) in every reachable state. This models nondeterminism: any philosopher can become hungry at any time.

### Dict comprehensions

`{p: 0 for p in 0..2}` creates a dict `{0: 0, 1: 0, 2: 0}`. This is the standard way to initialize per-process state.

### Dict update with `|`

`philState = philState | { p: 2 }` updates only key `p`, leaving other entries unchanged. The `|` operator merges the right-hand dict into the left.

### Multi-key dict update

`fork = fork | { p: false, (p + 2) % 3: false }` updates two keys in a single expression.

### Modular arithmetic

`(p + 2) % 3` maps philosopher `p` to their left fork. For 3 philosophers arranged in a circle, this gives the correct wraparound.

## Running it

```bash
specl check dining-philosophers.specl --no-deadlock
```

`--no-deadlock` is needed because this spec can deadlock (all philosophers hungry, all forks taken). That's a real property of the dining philosophers problem — the spec is correct in modelling it.
