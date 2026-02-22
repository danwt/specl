# Peterson's Mutual Exclusion

Peterson's algorithm is a classic solution for mutual exclusion between two processes using only shared memory (no hardware support).

## The algorithm

Each process signals intent via `flag[i]=true`, then yields priority by setting `turn=other`. A process enters the critical section only if the other's flag is false or it's this process's turn.

The key insight: setting `turn=other` **after** `flag=true` ensures that if both processes are interested, one will see `turn` pointing to itself.

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/peterson.specl)

```specl
{{#include ../../../specl/examples/showcase/peterson.specl}}
```

## What to notice

- **Program counter pattern.** `pc: Dict[0..1, 0..5]` with integer locations (0=idle through 5=exit) is a common way to model sequential protocols step by step.
- **Parameterized over processes.** Every action takes `p: 0..1`, so the checker explores both processes interleaved in all possible orderings.
- **The invariant is simple.** `not (pc[0] == 4 and pc[1] == 4)` — both processes cannot be in the critical section simultaneously.
- **17 states.** Small enough to visualize the full state graph with `--output dot`.

```bash
specl check peterson.specl --no-deadlock
```
