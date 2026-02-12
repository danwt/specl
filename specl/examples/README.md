# Specl Examples

## Directory Structure

| Directory | Description |
|-----------|-------------|
| `easy/` | Beginner specs — small state spaces, simple invariants, learn the language |
| `realistic/` | Mid-complexity protocols — real algorithms with parameterized exploration |
| `benchmark/` | Production protocols — complex models translated from TLA+ literature |
| `semaphores/` | Classic concurrency — mutual exclusion, producer-consumer, barriers |

The sibling `benchmarks/` directory contains TLC comparison scripts (`.tla`, `.cfg`, `.sh`) for performance benchmarking against TLC — it has no `.specl` files.

## Showcase

The following specs are the best examples for learning, demonstrating, and stress-testing Specl. Each has been reviewed for protocol faithfulness, invariant coverage, and checkability.

### Consensus & Distributed Protocols

| Spec | Protocol | Check Command | States | Time |
|------|----------|---------------|--------|------|
| [Paxos](benchmark/02-paxos/paxos.specl) | Single-decree Paxos (Synod) | `specl check paxos.specl -c N=2 -c MaxBallot=2 -c V=1 --no-deadlock` | 11.6K | <1s |
| [Raft](benchmark/17-raft-vanlightly/raft.specl) | Raft consensus (async, faithful) | `specl check raft.specl -c N=1 -c MaxVal=0 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=2 --no-deadlock` | ~500K | ~5s |
| [CometBFT](benchmark/09-comet/comet.specl) | Tendermint BFT with Byzantine faults | `specl check comet.specl -c N=3 -c MaxRound=0 -c V=1 -c F=1 --no-deadlock` | 59.5K | <2s |
| [Simplex](realistic/simplex/simplex.specl) | Simplex consensus (TCC 2023) | `specl check simplex.specl -c N=2 -c MaxIter=2 -c V=1 --no-deadlock` | 277K | ~3s |
| [Narwhal-Tusk](realistic/narwhal_tusk.specl) | DAG-based BFT consensus | *not yet checkable (Set[Seq] types)* | — | — |

### Transactions & Replication

| Spec | Protocol | Check Command | States | Time |
|------|----------|---------------|--------|------|
| [Percolator](benchmark/14-percolator/percolator.specl) | Google Percolator (snapshot isolation) | `specl check percolator.specl -c C=1 -c K=1 -c MaxTs=4 --no-deadlock` | 3.3K | <1s |
| [Two-Phase Commit](realistic/TwoPhaseCommit.specl) | 2PC transaction coordinator | `specl check TwoPhaseCommit.specl -c MAX_RM=2 --no-deadlock` | ~1K | <1s |

### Hardware & Cache Coherence

| Spec | Protocol | Check Command | States | Time |
|------|----------|---------------|--------|------|
| [MESI](benchmark/11-mesi/mesi.specl) | MESI cache coherence | `specl check mesi.specl -c C=2 -c V=1 --no-deadlock` | 144 | <1s |

### Distributed Algorithms

| Spec | Protocol | Check Command | States | Time |
|------|----------|---------------|--------|------|
| [Chandy-Lamport](realistic/chandy-lamport/chandy-lamport.specl) | Consistent snapshot algorithm | `specl check chandy-lamport.specl -c N=2 -c MaxMsgs=2 --no-deadlock` | ~5K | <1s |
| [SWIM](realistic/swim/swim.specl) | Failure detection protocol | `specl check swim.specl -c N=3 -c K=1 -c MaxRound=4 --no-deadlock` | varies | <2s |

### Bug-Finding Demonstrations

| Spec | Protocol | Check Command | Bug Found |
|------|----------|---------------|-----------|
| [Redlock](benchmark/05-redlock/redlock.specl) | Redis distributed lock (Kleppmann attack) | `specl check redlock.specl -c N=2 -c M=1 -c TTL=3 -c MaxTime=8` | MutualExclusion violated in 15 steps |
| [SWIM](realistic/swim/swim.specl) | SWIM accuracy limitation | `specl check swim.specl -c N=3 -c K=1 -c MaxRound=4 --no-deadlock` | AccuracySafety violated in 7 steps |

## Showcase Details

### Paxos — Single-Decree Consensus

Lamport's foundational consensus algorithm. The `SafeAt` function captures the core safety argument: a value is safe at ballot `b` if a quorum has promised `b` and either no one voted below `b`, or the highest vote below `b` was for the same value. Uses `powerset()` for quorum enumeration. 2 invariants: Agreement (two majority-accepted ballots propose the same value) and Validity.

### Raft — Async Consensus with Log Replication

Translated from [Vanlightly's model-checking-optimized TLA+ spec](https://github.com/Vanlightly/raft-tlaplus). Models full async message passing with explicit message sets (request vote, append entries, responses). Covers elections, log replication, commit advancement, term stepping, and server restarts. 2 key invariants: NoLogDivergence (committed entries agree across servers) and LeaderHasAllAckedValues. Note: the simpler `benchmark/01-raft/` is a shared-memory simplification — use this one for faithful Raft verification.

### CometBFT — Byzantine Fault Tolerant Consensus

Models the Tendermint/CometBFT protocol with explicit Byzantine behavior (faulty validators can prevote, precommit, and propose arbitrarily). Correctly implements the locking mechanism: a validator prevotes for a proposal only if unlocked, locked on the same value, or a proof-of-lock exists (quorum prevotes in an earlier round). 1 invariant: Agreement (no two honest validators decide different values).

### Simplex — Modern Crash-Fault Consensus

From Chan & Pass (TCC 2023). Models the crash-fault variant with chain-linking (leaders must re-propose values from earlier real blocks), dummy block voting on timeout, and quorum-based finalization. 2 invariants: FinalizationSafety (pigeonhole argument from the paper) and Agreement.

### Percolator — Distributed Transactions

Based on PingCAP's TLA+ formalization of Google's Percolator protocol. Models the full 2-phase commit with snapshot isolation: start timestamp allocation, primary/secondary prewriting, commit, abort, and 4 variants of stale lock cleanup. 4 invariants: WriteConsistency, LockConsistency, AbortedConsistency, and SnapshotIsolation.

### MESI — Cache Coherence

Models the MESI protocol (Papamarcos & Patel, ISCA 1984) with atomic bus transactions. Covers all state transitions: reads from Invalid (with M-holder flush, E-holder downgrade, S-sharing, or exclusive load), writes (BusRdX from Invalid, BusUpgr from Shared, silent upgrade from Exclusive), and evictions. 4 invariants: SWMR, ExclusiveExclusive, SharedMatchesMemory, ExclusiveMatchesMemory.

### Redlock — Distributed Lock Bug Finding

Models Redis Redlock with Kleppmann's attack scenario. The key bug: validity checking uses the client's local clock (which can lag behind real time due to GC pauses or network delays) rather than the global clock. The model checker finds a 15-step counterexample where locks expire in real time but a paused client still believes it holds the lock.

### SWIM — Failure Detection Tradeoffs

Models the SWIM protocol with direct and indirect pinging. The `DirectTimeout` action can fire for alive targets (modeling network non-determinism), which means the protocol can falsely suspect alive nodes. The checker finds this accuracy violation in 7 steps, demonstrating SWIM's fundamental accuracy-completeness tradeoff. 3 invariants including a safety encoding of bounded completeness.

### Narwhal-Tusk — DAG-Based BFT Consensus

Models the Narwhal/Tusk protocol (Danezis et al., 2022) that separates data availability from consensus ordering. Narwhal constructs a DAG of certificates with quorum signatures; Tusk orders the DAG using a deterministic leader commit rule. 6 invariants: SignaturesValid, DAGValidity, NoEquivocation, CommitAgreement, CommittedHaveQuorum, CausalConsistency. Not yet checkable (uses `Set[Seq[Int]]` types) — serves as a design reference pending future type support.

### Chandy-Lamport — Consistent Snapshots

Models the consistent snapshot algorithm on a token-passing ring. Process 0 initiates by recording its state and sending markers on outgoing channels. Non-initiators record their state upon receiving the first marker. The initiator records channel messages between sending and receiving its own marker. 2 invariants: ConsistentSnapshot (exactly 1 token captured) and NoPhantomMessages.

## Scaling Guide

State spaces grow exponentially with constants. Start small:

| Constant increase | Typical state space growth |
|-------------------|---------------------------|
| N: 2 → 3 | 10-100x |
| N: 3 → 4 | 100-1000x |
| MaxRound/MaxBallot: +1 | 5-50x |
| Values: +1 | 2-10x |

For large configurations, use `--fast` (fingerprint-only, 10x less memory) or `--por` (partial order reduction for independent actions). For specs with unbounded types, use `--smart` (symbolic checking).

**Note on types:** Many showcase specs use `Dict[Int, ...]` which the type checker considers unbounded. The tool auto-selects symbolic checking (`--smart`) for these. Specs with bounded types like `Dict[0..N, ...]` (e.g., Two-Phase Commit) can use BFS directly. The Narwhal-Tusk spec uses `Set[Seq[Int]]` which neither BFS nor symbolic currently supports — it serves as a design reference pending future type support.
