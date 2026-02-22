# MESI Cache Coherence

The MESI protocol maintains cache coherence in multiprocessor systems. Each cache line is in one of four states: Modified, Exclusive, Shared, or Invalid. The spec verifies that no two caches hold the same value in conflicting states.

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/mesi.specl)

```specl
{{#include ../../../specl/examples/showcase/mesi.specl}}
```

## What to notice

- **Full dict comprehension with `if/then/else`.** The actions use conditional comprehensions to update all caches simultaneously — when one cache takes exclusive ownership, all others invalidate.
- **Hardware domain.** This models a real CPU cache protocol, demonstrating that Specl works for hardware verification, not just distributed systems.
- **Inherently small state space.** Even with many caches, there are only 4 states per cache line, keeping the state space manageable.

```bash
specl check mesi.specl -c C=2 -c V=1 --no-deadlock
```
