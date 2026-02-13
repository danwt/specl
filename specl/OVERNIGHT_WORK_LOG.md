# Overnight Work Log — Feb 13-14 2026

## Scope
Working through milestones from `/Users/danwt/Documents/repos/demo-state-enumerating-mc/research/next-milestone/`.

## Non-goals (user specified)
- GPU acceleration
- Liveness/fairness/temporal properties
- Disk storage / distributed mode
- Cranelift/LLVM compilation

## Priority order
1. JSON output mode (`--output json`) — essential for LLM harness
2. Simulation mode (`specl simulate`) — quick UX win
3. Lint command (`specl lint`) — fast syntax/type check
4. Swarm verification (`--swarm N`) — low effort, high impact
5. Micro-optimizations (hash_var specialization, FPSet tuning)
6. Bloom filter (`--fast --bloom`)
7. ITF trace export (`--format itf`)
8. Profiling mode (`--profile`)
9. LLM discovery harness (Python tool)

## Progress

### Task 1: JSON output mode
- Status: DONE
- Added `--output json` flag to `specl check`
- Structured JSON for all outcomes: ok, invariant_violation, deadlock, state_limit_reached, memory_limit_reached, error, unknown, not_inductive
- Full state traces with named variables and typed values (dicts → objects, sets → arrays, etc.)
- Works with both BFS and symbolic checking modes
- Errors (parse/type/compile/check) emitted as JSON when in JSON mode
- Fixed tracing to write to stderr (was incorrectly on stdout)

### Task 2: Simulate command
- Status: DONE
- `specl simulate spec.specl --steps 100 --seed 42`
- Random walk: picks one enabled action per step, checks invariants
- Supports `--output json` for LLM harness
- Added `simulate()` method to Explorer, `SimulateOutcome` type

### Task 3: Lint command
- Status: DONE
- `specl lint spec.specl` — parse + typecheck + compile in ~1ms
- Supports `--output json` with structured error messages
- Validates constants if provided

### Task 4: Swarm verification
- Status: DONE
- `specl check --swarm 4` — N independent BFS instances with shuffled action orders
- Each worker uses fingerprint-only mode for low memory
- First violation stops all workers, triggers trace reconstruction
- Added `action_shuffle_seed` to CheckConfig, `stop_flag` to Explorer
- Tested: finds EPaxos bug in 0.3s with 4 workers

### Task 5: Micro-optimizations
- Status: DONE
- **hash_var specialization**: Splitmix64-style direct arithmetic for Int/Bool (skip AHasher construction). Constant XOR seed prevents zero-hash for val=0.
- **AtomicFPSet lower load factor**: Grow at 37.5% instead of 50%, reducing average probe length from ~2.0 to ~1.6.
- **CAS spin-backoff**: Added `std::hint::spin_loop()` on CAS failure in AtomicFPSet::insert for reduced contention.
- All 38 existing tests pass. EPaxos bug still correctly found.

### Task 6: ITF trace export
- Status: DONE
- `specl check --output itf` and `specl simulate --output itf`
- Full Apalache-compatible Informal Trace Format encoding
- Type mapping: Int → `{"#bigint": "N"}`, Set → `{"#set": [...]}`, Dict → `{"#map": [[k,v],...]}`, Tuple → `{"#tup": [...]}`, Seq → array, Record → object, Option → variant
- Metadata includes format version, source, result kind, violated invariant
- Works with check, simulate, and swarm commands

### Blockers / Questions for Daniel
(None yet)
