# Paxos Consensus

Single-decree Paxos (Synod protocol) from Lamport's "Paxos Made Simple". The spec verifies that if two ballots both achieve majority acceptance, they must have proposed the same value.

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/paxos.specl)

```specl
{{#include ../../../specl/examples/showcase/paxos.specl}}
```

## What to notice

- **`powerset` and nested quantifiers.** The `SafeAt` function iterates over all subsets of acceptors (`powerset(0..N)`) to find a quorum that satisfies the safety condition. This is the most complex expression in any showcase spec.
- **Set comprehensions for quorum check.** `len({a in 0..N if accepted[b][a]}) * 2 > N + 1` counts accepted votes.
- **Both BFS and symbolic.** This is the best example for exercising both verification modes: BFS at N=3 (3.35M states, ~9s), symbolic at N=10 (k-induction, ~90s).

```bash
specl check paxos.specl -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock
```
