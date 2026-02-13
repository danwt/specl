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

### Blockers / Questions for Daniel
(None yet)
