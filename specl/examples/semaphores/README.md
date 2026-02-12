# Semaphore Puzzles from "The Little Book of Semaphores"

This directory contains Specl models of classic concurrency problems from Allen B. Downey's [The Little Book of Semaphores](https://greenteapress.com/semaphores/).

## About the Book

**The Little Book of Semaphores** (2nd Edition, v2.2.1) by Allen B. Downey is a free textbook on synchronization and concurrent programming. It presents a collection of progressively harder synchronization puzzles, each with hints and solutions.

- **PDF**: https://greenteapress.com/semaphores/LittleBookOfSemaphores.pdf
- **Author**: Allen B. Downey (Olin College)
- **License**: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

## Examples

### 1. Rendezvous ([rendezvous.specl](rendezvous.specl))

**Section 3.3 (pages 12-15)**

**Problem:** Two threads must synchronize such that thread A's first statement happens before thread B's second statement, and vice versa.

**Solution:** Uses two semaphores (aArrived, bArrived) initialized to 0. Each thread signals when it arrives and waits for the other.

**Verification:**
```bash
specl check rendezvous.specl --no-deadlock
# Expected: OK (17 states, depth 8)
```

**Key Concepts:**
- Bidirectional signaling
- Symmetric solution (both threads run same code structure)
- Rendezvous pattern (neither proceeds until both arrive)

---

### 2. Mutex ([mutex.specl](mutex.specl))

**Section 3.4 (pages 16-19)**

**Problem:** Enforce mutual exclusion for a critical section accessed by N threads.

**Solution:** Uses a binary semaphore (mutex) initialized to 1. Threads wait() before entering the critical section and signal() after exiting.

**Verification:**
```bash
specl check mutex.specl -c N=3 --no-deadlock
# Expected: OK with MutualExclusion invariant holding
```

**Key Concepts:**
- Critical section protection
- Binary semaphore as a lock
- Symmetric solution (scales to any N)
- Prevention of race conditions

---

### 3. Barrier ([barrier.specl](barrier.specl))

**Section 3.6 (pages 21-29)**

**Problem:** N threads must all reach a rendezvous point before any can proceed to a critical section.

**Solution:** Uses a counter (protected by mutex) and a turnstile semaphore. The Nth thread opens the turnstile, then each thread passes through and signals the next.

**Verification:**
```bash
specl check barrier.specl -c N=4 --no-deadlock
# Expected: OK with BarrierConstraint holding
```

**Key Concepts:**
- N-thread synchronization
- Turnstile pattern (wait + signal creates chain)
- Generalization of 2-thread rendezvous
- Common bug: forgetting to signal after waiting (causes deadlock)

---

### 4. H₂O / Water Molecule ([h2o.specl](h2o.specl))

**Section 5.6 (pages 143-147)**

**Problem:** Oxygen and hydrogen threads must combine into complete H₂O molecules (1 oxygen + 2 hydrogen). All three threads in a molecule must bond() together before any threads from the next molecule can bond.

**Solution:** Threads arrive and increment counters. When a complete set is available (2H + 1O), one thread releases all three from queues. They bond at a barrier before proceeding.

**Verification:**
```bash
specl check h2o.specl -c NUM_O=1 -c NUM_H=2 --no-deadlock
# Expected: OK (31 states, depth 14) - forms 1 molecule

specl check h2o.specl -c NUM_O=2 -c NUM_H=4 --no-deadlock
# Expected: OK - forms 2 molecules
```

**Key Concepts:**
- Resource grouping (correct stoichiometry)
- Barrier synchronization
- Thread conservation (accounting for threads in all states)
- Complex state machine (7 states per thread type)

---

### 5. Dining Philosophers ([dining_philosophers.specl](dining_philosophers.specl))

**Section 4.4 (pages 87-93)**

**Problem:** Five philosophers sit at a round table with one fork between each pair. Each philosopher needs TWO forks to eat. Prevent deadlock and starvation.

**Naive solution deadlocks:** If all philosophers pick up their right fork simultaneously, they deadlock waiting for the left fork.

**Solution (Footman):** Limit to N-1 philosophers at the table using a footman semaphore initialized to 4. This guarantees at least one fork is available, breaking the circular wait.

**Verification:**
```bash
specl check dining_philosophers.specl -c N=5 --no-deadlock --fast
# Expected: OK - no deadlocks with footman solution
```

**Key Concepts:**
- Famous deadlock problem (Dijkstra, 1965)
- Circular wait condition
- Deadlock prevention via resource restriction
- Alternative solutions: asymmetry, resource hierarchy

---

## Running the Examples

All examples can be checked with the `specl` command-line tool:

```bash
# Install Specl (requires Rust)
cargo install --path crates/specl-cli

# Check a specific example
specl check examples/semaphores/rendezvous.specl --no-deadlock

# Check with specific constants
specl check examples/semaphores/barrier.specl -c N=3 --no-deadlock

# Use --fast for large state spaces (faster, but no counterexample traces)
specl check examples/semaphores/dining_philosophers.specl -c N=5 --fast --no-deadlock
```

## Why Specl for Semaphore Puzzles?

Specl is an **exhaustive model checker** - it explores **every reachable state** to verify safety properties. This makes it ideal for semaphore puzzles:

### ✅ Advantages

1. **Finds minimal counterexamples:** When bugs exist (like the rendezvous deadlock), Specl finds the shortest path to the bug
2. **Proves correctness:** When it says "OK", you know ALL states are safe
3. **Small state spaces:** Classic puzzles have small configurations (2-5 threads), making exhaustive search tractable
4. **Natural modeling:** Semaphore problems are state machines - perfect fit for Specl

### 🎯 What We Verify

Each model verifies:
- **Safety properties:** No deadlocks, no race conditions, correct resource allocation
- **Synchronization constraints:** Required orderings hold (e.g., A1 before B2)
- **Resource bounds:** Counters and semaphores stay within limits
- **Progress:** Threads can complete successfully

## Learning Path

Recommended order for learning:

1. **mutex.specl** - Simplest: binary semaphore, N threads, one resource
2. **rendezvous.specl** - Two threads, bidirectional signaling
3. **barrier.specl** - N threads, turnstile pattern
4. **h2o.specl** - Complex: resource grouping, multiple thread types
5. **dining_philosophers.specl** - Famous: deadlock, circular wait

## Common Patterns

These examples demonstrate fundamental concurrency patterns:

| Pattern | Examples | Key Technique |
|---------|----------|---------------|
| **Signaling** | Rendezvous | Signal arrival, wait for other |
| **Mutual Exclusion** | Mutex | Binary semaphore as lock |
| **Barrier** | Barrier, H₂O | Wait for group, then proceed together |
| **Turnstile** | Barrier | wait() + signal() creates chain |
| **Resource Restriction** | Dining Philosophers | Limit concurrency to prevent deadlock |
| **Counting** | Barrier, H₂O | Track arrivals with protected counter |

## Further Exploration

Other interesting problems from the book to try:

- **Producer-Consumer** (Section 4.1, p.55) - Bounded buffer with producers and consumers
- **Readers-Writers** (Section 4.2, p.65) - Multiple readers OR one writer
- **Cigarette Smokers** (Section 4.5, p.101) - Resource matching problem
- **Barbershop** (Section 5.2, p.121) - FIFO queue with capacity
- **Santa Claus** (Section 5.5, p.137) - Group synchronization with elves and reindeer

## References

1. Downey, Allen B. *The Little Book of Semaphores* (2nd Edition, v2.2.1), 2016.
   https://greenteapress.com/semaphores/
2. Dijkstra, Edsger W. "Cooperating sequential processes", 1965.
3. Andrews, Gregory R. *Concurrent Programming: Principles and Practice*, 1991.

## Contributing

Have you modeled another puzzle from the book? Contributions welcome! Please ensure:
- Full puzzle description from the book (with page numbers)
- Link to the PDF
- Clear invariants and verification instructions
- Comments explaining the solution approach

---

**Happy model checking!** 🚀
