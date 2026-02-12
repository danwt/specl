# Specl Examples

## Directory Structure

| Directory | Description |
|-----------|-------------|
| `showcase/` | Curated protocol specs — real distributed systems, reviewed for faithfulness |
| `other/` | Additional specs — toys, stress tests, semaphores, simplified models |

The sibling `benchmarks/` directory contains TLC comparison scripts (`.tla`, `.cfg`, `.sh`) for performance benchmarking against TLC — it has no `.specl` files.

## Showcase Audit

Each showcase spec has been audited for **protocol faithfulness** (does it model the real algorithm?) and **meaningful parameterization** (are constants set high enough to exercise the interesting behavior?).

### Verification Results

Specs verified at minimum meaningful parameters:

| Spec | Protocol | Check Command | States | Time |
|------|----------|---------------|--------|------|
| [Paxos](showcase/paxos.specl) | Single-decree Paxos (Synod) | `-c N=2 -c MaxBallot=3 -c V=2 --no-deadlock --fast` | 316K | 6s |
| [CometBFT](showcase/comet.specl) | Tendermint BFT | `-c N=3 -c MaxRound=0 -c V=1 -c F=1 --no-deadlock --fast` | 56K | 2s |
| [Simplex](showcase/simplex.specl) | Simplex consensus (TCC 2023) | `-c N=2 -c MaxIter=2 -c V=1 --no-deadlock --fast` | 277K | 3s |
| [MESI](showcase/mesi.specl) | Cache coherence (ISCA 1984) | `-c C=5 -c V=3 --no-deadlock --fast` | 376 | <1s |
| [Two-Phase Commit](showcase/TwoPhaseCommit.specl) | 2PC coordinator | `-c MAX_RM=3 --no-deadlock --fast` | 1.6K | <1s |

Specs with genuinely large state spaces (>5 min at meaningful params, full CPU):

| Spec | Protocol | Meaningful Params | Notes |
|------|----------|-------------------|-------|
| [Raft](showcase/raft.specl) | Raft (Vanlightly) | `-c N=2 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3` | 3 servers, elections + log replication |
| [Paxos](showcase/paxos.specl) | Single-decree Paxos | `-c N=3 -c MaxBallot=3 -c V=2` | 4 acceptors, competing ballots |
| [CometBFT](showcase/comet.specl) | Tendermint BFT | `-c N=3 -c MaxRound=1 -c V=1 -c F=1` | 4 validators, view changes |
| [Simplex](showcase/simplex.specl) | Simplex consensus | `-c N=2 -c MaxIter=3 -c V=1` | 3 players, 4 iterations |
| [Percolator](showcase/percolator.specl) | Google Percolator | `-c C=2 -c K=2 -c MaxTs=8` | 3 clients, 3 keys, snapshot isolation |
| [Narwhal-Tusk](showcase/narwhal_tusk.specl) | DAG-based BFT | `-c N=3 -c F=1 -c MAX_ROUND=2` | 4 validators, quorum certs |

Bug-finding demonstrations (intentional violations):

| Spec | Protocol | Check Command | Bug Found |
|------|----------|---------------|-----------|
| [Redlock](showcase/redlock.specl) | Redis distributed lock | `-c N=2 -c M=1 -c TTL=3 -c MaxTime=8` | MutualExclusion violated (Kleppmann attack) |
| [SWIM](showcase/swim.specl) | Failure detection | `-c N=3 -c K=1 -c MaxRound=4 --no-deadlock` | AccuracySafety violated (accuracy-completeness tradeoff) |

### Faithfulness Assessment

**Fully faithful (well-modeled, interesting state spaces):**
- **Paxos** — Exact powerset quorum enumeration. Agreement + Validity invariants.
- **Raft** — Based on Vanlightly's peer-reviewed TLA+ spec. Full async message passing with 4 message types.
- **CometBFT** — Byzantine validators, locking mechanism, prevote/precommit phases. Requires F>=1 for meaningful BFT (F=0 is degenerate: quorum=1).
- **Simplex** — Chain-linking, dummy block voting, quorum-based finalization per the TCC 2023 paper.
- **Percolator** — Based on PingCAP's TLA+ formalization. Full 2-phase commit with snapshot isolation and 4 cleanup actions.
- **Redlock** — Clock drift, lock expiry, majority acquisition. The bug IS the point.
- **SWIM** — Direct/indirect pinging with non-deterministic timeouts. Violation demonstrates real protocol tradeoff.

**Faithful but inherently small:**
- **MESI** — Correct model of all state transitions, but cache coherence has few states per core (4 states x V values). Even C=10 V=5 has only hundreds of states.
- **TwoPhaseCommit** — Clean model, but 2PC is a simple protocol. Good introductory example.

**Partially faithful:**
- **Narwhal-Tusk** — No Byzantine behavior modeled. Implicit references (all certs from previous round rather than explicit references). 6 structural invariants. Useful as a design reference but not a complete BFT verification.

**Known issues:**
- **Chandy-Lamport** — Suspected checker bug: deadlocks at depth 2 when ReceiveToken should be enabled (sequence operations in FIFO channels). The spec itself appears correct; the issue is in action guard evaluation. **Pending investigation.**

### Key Observations

1. **Most showcase specs produce genuinely large state spaces** at meaningful parameters. Six specs didn't finish BFS in 5+ minutes with full CPU utilization, demonstrating specl's viability for real protocol verification.

2. **CometBFT with F=0 is meaningless** — Quorum = 2*0+1 = 1, so any single validator forms a quorum and Agreement is trivially violated. Always use F>=1.

3. **Raft N=1 is too small** — 2 servers can't demonstrate elections or quorum. Use N>=2 (3 servers).

## Scaling Guide

State spaces grow exponentially with constants. Start small:

| Constant increase | Typical state space growth |
|-------------------|---------------------------|
| N: 2 → 3 | 10-100x |
| N: 3 → 4 | 100-1000x |
| MaxRound/MaxBallot: +1 | 5-50x |
| Values: +1 | 2-10x |

Use `--fast` (fingerprint-only, 10x less memory) for large state spaces. Use `--por` for specs with independent actions. For specs with unbounded types (`Dict[Int, ...]`), the tool auto-selects symbolic checking; force BFS with `--fast` or `--por`.
