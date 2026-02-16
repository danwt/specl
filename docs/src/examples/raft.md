# Raft Consensus

Raft leader election and log replication, modelled after Vanlightly's async formulation. This is the most complex showcase spec at 386 lines, verifying ElectionSafety, LogMatching, and CommitSafety.

## The spec

[Source](https://github.com/danwt/specl/blob/main/specl/examples/showcase/raft.specl) (386 lines — view on GitHub for the full spec)

## Key features demonstrated

- **`Seq` and `Set[Seq[Int]]`** — logs are sequences, messages are sets of sequences
- **Message passing** — `msgs` is a `Set[Seq[Int]]` where each sequence encodes a message with fields `[type, src, dst, term, ...]`
- **Sequence operations** — `++` for log append, `len()`, slicing with `[0..k]`, `head()`, `tail()`
- **`union` / `diff`** — adding and consuming messages
- **Complex invariants** — ElectionSafety (at most one leader per term), LogMatching (prefix consistency), CommitSafety (committed entries are never lost)

## Running it

```bash
# Quick check (~1s)
specl check raft.specl -c N=1 -c MaxVal=0 -c MaxElections=2 \
    -c MaxRestarts=0 -c MaxLogLen=2 --no-deadlock

# Strenuous (~4 min, 166M states)
specl check raft.specl -c N=2 -c MaxVal=1 -c MaxElections=2 \
    -c MaxRestarts=0 -c MaxLogLen=3 --no-deadlock --fast
```

## What to notice

This spec exercises nearly every Specl language feature in a single real-world protocol. If you can read and understand this spec, you can write Specl fluently.
