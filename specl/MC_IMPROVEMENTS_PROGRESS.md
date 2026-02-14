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
- [ ] 8. K-induction strengthening (CTI learning loop)
- [ ] 9. Delta state storage (store diffs from parent)

## Large Effort
- [ ] 10. Instance-level DPOR
- [ ] 11. SPORE (symmetry + POR combo)
- [x] 12. Superinstructions (fused bytecode ops)
- [ ] 13. Tree compression (LTSmin-style)
- [ ] 14. Arena allocation for temporaries
- [ ] 15. NaN-boxing / value representation
- [ ] 16. Queue state elimination (store fp+metadata only)
- [ ] 17. Incremental checking (cache to disk, re-check deltas)
- [ ] 18. Copy-and-patch JIT
- [ ] 19. Golem CHC backend

## Notes / Decisions
- Faster primitive hashing: ALREADY DONE (splitmix64 in state.rs hash_var)
- SmallVec: ALREADY in deps and used in explorer.rs
- GPU: excluded by user (non-goal)
