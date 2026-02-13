# CRDT Design Task

Design a state-based CRDT (Conflict-free Replicated Data Type) for {data_type}.

## What is a CRDT?

A CRDT is a replicated data structure where:
1. Each replica holds a local copy of the state
2. Replicas can be updated independently (no coordination)
3. A merge function combines any two replica states
4. After sufficient merging, all replicas converge to the same state

## Requirements

Your design must satisfy these algebraic properties:

- **Merge Commutativity**: merge(a, b) produces the same result as merge(b, a)
- **Merge Idempotency**: merge(a, a) == a (merging with self is a no-op)
- **Convergence**: replicas that have received the same set of updates converge to identical states after merging

## Specl Model Structure

Model N replicas (use `const N: Int`). Each replica holds the CRDT state.

Required actions:
- **Update operations**: modify a single replica's state (e.g., Insert, Delete, Increment)
- **Merge(src, dst)**: merge replica src's state into replica dst

Required invariants:
- **MergeIdempotent**: for all pairs of replicas, merging is idempotent
- **MergeCommutative**: for all pairs, merge order doesn't matter (compute the merged result both ways and compare)

## Tips

- Use `Dict[Int, ...]` keyed by replica index for per-replica state
- Use dict merge `|` for updating individual replicas
- Keep the state space small: use small value ranges (0..3 or similar)
- Test with N=2 replicas and small bounds first
- Common CRDT metadata: version vectors, timestamps, tombstone sets
- The `require src != dst` guard prevents self-merges in Merge actions

## Target Data Type

{data_type_description}
