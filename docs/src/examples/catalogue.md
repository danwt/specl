# Full Catalogue

The repository contains 100+ verified specifications in [`specl/examples/`](https://github.com/danwt/specl/tree/main/specl/examples). The [showcase](./showcase.md) contains 8 curated examples. Below is the full catalogue organized by domain.

## Consensus

| Spec | Description |
|------|-------------|
| paxos | Single-decree Paxos (Lamport) |
| epaxos | Egalitarian Paxos (Moraru et al.) |
| multipaxos-reconfig | Multi-Paxos with reconfiguration |
| flexible-paxos | Flexible Paxos (quorum intersection) |
| raft | Raft consensus (Vanlightly async model) |
| raft-simplified | Simplified Raft (leader election only) |
| pbft | Practical Byzantine Fault Tolerance |
| simplex | Simplex consensus |
| crash-consensus | Consensus with crash failures |
| viewstamped-replication | Viewstamped Replication |
| nbac | Non-blocking atomic commitment |

## Distributed Transactions

| Spec | Description |
|------|-------------|
| two-phase-commit | Classic 2PC |
| three-phase-commit | 3PC (non-blocking variant) |
| percolator | Google Percolator (snapshot isolation) |
| parallel-commits | CockroachDB parallel commit protocol |
| two-phase-locking | 2PL concurrency control |
| snapshot-isolation | Snapshot isolation protocol |
| mvcc | Multi-version concurrency control |
| timestamp-ordering | Timestamp-based CC |
| occ | Optimistic concurrency control |
| saga | Saga pattern (compensating transactions) |
| stm | Software transactional memory |

## Mutual Exclusion & Locking

| Spec | Description |
|------|-------------|
| peterson | Peterson's algorithm (2 processes) |
| dekker | Dekker's algorithm |
| bakery | Lamport's bakery algorithm |
| lamport-mutex | Lamport's distributed mutex |
| ricart-agrawala | Ricart-Agrawala mutex |
| maekawa | Maekawa's quorum-based mutex |
| ticket-lock | Ticket lock |
| test-and-set | TAS lock |
| mcs-lock | MCS queue lock |
| clh-lock | CLH queue lock |
| redlock | Redis distributed lock (finds Kleppmann's bug) |

## CRDTs

| Spec | Description |
|------|-------------|
| g-counter | Grow-only counter |
| pn-counter | Positive-negative counter |
| or-set | Observed-remove set |
| lww-register | Last-writer-wins register |
| crdt-flag | Enable/disable CRDT flag |
| crdt-set | G-Set and 2P-Set |

## Broadcast & Communication

| Spec | Description |
|------|-------------|
| reliable-broadcast | Reliable broadcast |
| causal-broadcast | Causal ordering broadcast |
| fifo-broadcast | FIFO broadcast |
| atomic-broadcast | Atomic (total order) broadcast |
| gossip | Gossip protocol |

## Cache Coherence

| Spec | Description |
|------|-------------|
| mesi | MESI protocol |
| moesi | MOESI protocol |

## Clock Synchronization

| Spec | Description |
|------|-------------|
| lamport-clocks | Lamport logical clocks |
| vector-clocks | Vector clocks |
| cristian-clock-sync | Cristian's algorithm |
| berkeley-clock-sync | Berkeley algorithm |

## Replication & Consistency

| Spec | Description |
|------|-------------|
| chain-replication | Chain replication |
| primary-backup | Primary-backup replication |
| abd | ABD shared register |
| cas-register | CAS register |
| log-replication | Log replication protocol |
| optimistic-replication | Optimistic replication |
| anti-entropy | Anti-entropy protocol |
| read-repair | Read repair |
| sloppy-quorum | Sloppy quorum |

## Failure Detection & Recovery

| Spec | Description |
|------|-------------|
| swim | SWIM protocol |
| phi-accrual | Phi accrual failure detector |
| split-brain-resolver | Split-brain resolution |
| termination-detection | Termination detection |
| leader-election | Leader election |
| bully-election | Bully algorithm |

## Concurrent Data Structures

| Spec | Description |
|------|-------------|
| ms-queue | Michael-Scott queue |
| treiber-stack | Treiber stack |
| work-stealing | Work-stealing deque |
| flat-combining | Flat combining |
| hazard-pointers | Hazard pointers (safe memory reclamation) |
| epoch-reclamation | Epoch-based reclamation |
| aba-problem | ABA problem demonstration |

## Classic Concurrency

| Spec | Description |
|------|-------------|
| dining-philosophers | Dining philosophers |
| reader-writer | Reader-writer lock |
| bounded-buffer | Bounded buffer |
| barrier | Synchronization barrier |
| sleeping-barber | Sleeping barber |
| dining-savages | Dining savages |
| cigarette-smokers | Cigarette smokers |
| priority-inversion | Priority inversion |
| double-checked-locking | Double-checked locking |

## Infrastructure Patterns

| Spec | Description |
|------|-------------|
| token-bucket | Token bucket rate limiter |
| circuit-breaker | Circuit breaker |
| exponential-backoff | Exponential backoff |
| lease | Distributed lease |
| reactor | Reactor pattern |
| map-reduce | Map-reduce |
| outbox | Transactional outbox |
| idempotent-receiver | Idempotent receiver |
| wal | Write-ahead log |
| group-commit | Group commit |
| bulkhead | Bulkhead pattern |

## Hashing & Routing

| Spec | Description |
|------|-------------|
| consistent-hashing | Consistent hashing |
| rendezvous-hashing | Rendezvous (HRW) hashing |

## Semaphore Puzzles

| Spec | Description |
|------|-------------|
| sem-barbershop | Barbershop problem |
| sem-barrier | Barrier synchronization |
| sem-dining_philosophers | Dining philosophers (semaphore) |
| sem-h2o | H2O molecule formation |
| sem-mutex | Basic mutex |
| sem-producer_consumer | Producer-consumer |
| sem-queue | Bounded queue |
| sem-readers_writers | Readers-writers |
| sem-rendezvous | Rendezvous |
| sem-santa_claus | Santa Claus problem |
| sem-unisex_bathroom | Unisex bathroom |
