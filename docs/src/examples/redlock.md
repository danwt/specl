# Redlock

Redlock is Redis's distributed locking algorithm. This spec intentionally finds Martin Kleppmann's counterexample: when a client pauses (GC, network delay) while holding locks, the locks expire, another client acquires them, and both clients believe they hold the lock.

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/redlock.specl)

```specl
{{#include ../../../specl/examples/showcase/redlock.specl}}
```

## What to notice

- **Intentional violation.** Unlike other showcase specs, this one is *designed* to fail. The `MutualExclusion` invariant is violated — that's the point.
- **Time modelling.** Global time advances via `Tick()`, client local clocks advance via `ClockAdvance()`. A client that never fires `ClockAdvance` is effectively paused — modelling GC pauses or network delays.
- **The bug.** Client checks lock validity using `localClock` (line 118), but locks expire based on `globalTime`. If a client pauses (local clock falls behind global time), its locks expire while it still thinks they're valid.
- **Set operations.** `clientLocks[c] union {i}` for accumulating acquired locks, conditional dict comprehension for releasing all locks on failure.

```bash
specl check redlock.specl -c N=2 -c M=1 -c TTL=3 -c MaxTime=8
```

The checker finds the violation in 15 steps.
