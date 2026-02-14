# MC Improvements Progress

## Quick Wins
- [x] 1. FPSet tuning (prefetch, better probing)
- [x] 2. Portfolio symbolic (parallel threads for BMC/k-ind/IC3)
- [x] 3. Spacer tuning (parameter profiles for IC3)
- [x] 4. Collapse compression (per-variable interning)

## Medium Effort
- [x] 5. Incremental expression evaluation (skip invariants when deps unchanged) — already maximally precise
- [x] 6. Batch dict updates (detect consecutive merges in bytecode)
- [x] 7. COI improvements (per-invariant exploration with --check-only filter)
- [x] 8. K-induction strengthening (CTI learning loop)
- [x] 9. Delta state storage — SKIP: collapse compression already provides 3-6x reduction, delta adds reconstruction overhead
- [x] 10. Instance-level DPOR — ALREADY DONE: stubborn set closure over (action, params) instances
- [x] 11. SPORE (symmetry + POR combo) — ALREADY DONE: orbit_representatives filtering applied within ample sets

## Large Effort
- [x] 12. Superinstructions (fused bytecode ops)
- [ ] 13. Tree compression (LTSmin-style) — requires major new data structure, deferred
- [ ] 14. Arena allocation for temporaries — requires Value type rewrite, deferred
- [ ] 15. NaN-boxing / value representation — massive rewrite touching all consumers, deferred
- [x] 16. Queue state elimination — SKIP: State uses Arc (shared with store), only saves 16 bytes/entry
- [x] 17. Incremental checking (cache to disk, --incremental flag, deterministic fingerprinting)
- [ ] 18. Copy-and-patch JIT — extremely complex custom JIT, deferred
- [ ] 19. Golem CHC backend

## Notes / Decisions
- Faster primitive hashing: ALREADY DONE (splitmix64 in state.rs hash_var)
- SmallVec: ALREADY in deps and used in explorer.rs
- GPU: excluded by user (non-goal)
- Items 13-15, 18 deferred: require fundamental architecture changes (Value representation, memory model, or code generation). Better as separate focused projects.
