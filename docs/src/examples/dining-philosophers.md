# Dining Philosophers

Three philosophers sit around a circular table. Each needs both adjacent forks to eat. The spec verifies that no two adjacent philosophers can eat simultaneously.

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/dining-philosophers.specl)

```specl
{{#include ../../../specl/examples/showcase/dining-philosophers.specl}}
```

## What to notice

- **Modular arithmetic.** `(p + 2) % 3` maps each philosopher to their left fork. With 3 philosophers in a circle, philosopher 0's left fork is fork 2.
- **Multi-key dict update.** `fork = fork | { p: false, (p + 2) % 3: false }` updates two entries in one expression.
- **Deadlock expected.** This spec can deadlock (all philosophers hungry, no forks available). Use `--no-deadlock`.

```bash
specl check dining-philosophers.specl --no-deadlock
```
