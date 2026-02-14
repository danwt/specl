# Formal Verification Model Checkers as AI/LLM Backends (Feb 2026)

Research conducted February 14, 2026.

Comprehensive survey of systems where formal verification model checkers, SMT solvers, bounded model checkers, or property checkers serve as backends in AI-powered vulnerability detection and code verification.

## Architecture Patterns

Every system found falls into one of these patterns:

### Pattern A: Counterexample-Guided Repair Loop (most common, most effective)
```
LLM generates code/spec -> Model checker verifies ->
  Fail: counterexample fed back to LLM -> LLM revises -> repeat
  Pass: done
```
Used by: ESBMC-AI, Certora AI Composer, LaM4Inv, LEMUR, Dafny annotator, Alloy repair, UCLID5, AutoVerus, MSG.

### Pattern B: LLM Generates Properties, FM Validates
```
LLM generates candidate properties/invariants -> FM backend filters/validates ->
  Valid properties assembled -> FM re-verifies composite
```
Used by: PropertyGPT, SmartInv, ESBMC-ibmc, LaM4Inv (for invariant assembly).

### Pattern C: FM Provides Ground Truth Context to LLM
```
Static analyzer/model checker produces program facts ->
  Facts provided as context to LLM -> LLM reasons with grounded information
```
Used by: Slither-MCP, Aderyn MCP, GPTScan, LLMDFA, Buttercup, ATLANTIS.

### Pattern D: Self-Evolving Data Flywheel
```
Verifier as binary oracle (correct/incorrect) ->
  Correct outputs become training data -> Fine-tune LLM -> repeat
```
Used by: SAFE, AlphaVerus.

### Pattern E: LLM as SMT Heuristic Guide
```
LLM provides candidate instantiations -> SMT solver validates soundly ->
  SAT: problem solved / UNSAT: generate exclusion clauses -> iterate
```
Used by: AquaForte.

---

## 1. Direct LLM + Bounded Model Checker Systems

### ESBMC-AI (Pattern A) -- AST 2025
ESBMC bounded model checker (Z3/Boolector) verifies C code, generates counterexamples with full execution traces, feeds them to GPT-4o for repair.

**Key result:** 80-90% fix rate with counterexample feedback vs 31-37% without.

Per-vulnerability fix rates (50,000 C programs from FormAI):
- Buffer overflow on scanf: 90.4%
- Array bounds (lower): 95.6%
- Division by zero: 86.5%
- NULL pointer deref: 80.4%
- Arithmetic overflow on add: 70.3%
- Array bounds (upper): 41.0%
- Memory leaks: 48.7%

- https://arxiv.org/abs/2305.14752

### ESBMC-ibmc (Pattern B) -- ASE 2024 Distinguished Paper
Replaces loop subgraphs in CFG with LLM-generated invariants. First-order theorem prover validates invariant correctness before BMC uses them. Transforms unbounded-loop programs into loop-free variants.

Competitive with SeaHorn and VeriAbs. Verifies programs they cannot.

- https://dl.acm.org/doi/abs/10.1145/3691620.3695512

### LaM4Inv (Patterns A+B) -- ASE 2024
LLM generates multiple candidate invariants. BMC (CBMC/ESBMC/UAutomizer) identifies valid predicates, assembles composites, SMT solvers check. Feedback from failures incorporated into next prompt.

**Key insight:** LLMs rarely produce the correct complete invariant in one shot, but almost always produce all individual predicates across multiple responses. BMC serves as filter/assembler.

**Result:** 309/316 programs verified (vs 218 baseline). Average 3.7 LLM proposals needed.

- https://github.com/SoftWiser-group/LaM4Inv

### LEMUR (Pattern A) -- ICLR 2024 + 2025 successors
Tight generate-and-check loop between LLM and Z3 SMT solver. Z3 validates or returns counterexamples as repair hints.

**Result:** 100% on Code2Inv (133/133), up from 107/133 with GPT-4. 1-2 proposals per instance, 14-55 seconds.

LEMUR also provides a formal calculus (transition rules) with soundness proof for the LLM-reasoner interaction. First framework to handle programs with more than one loop via learning-based verification.

On SV-COMP: LEMUR(GPT4) solved 25/47 challenging benchmarks. UAUTOMIZER and ESBMC each solved only 1/47.

- https://arxiv.org/abs/2508.00419
- https://github.com/wu-haoze/Lemur-program-verification

### 4/delta Bound -- Formal Convergence Framework (Dec 2025)
Models LLM-verifier interaction as absorbing Markov chain with four stages: CodeGen -> Compilation -> InvariantSynth -> SMTSolving.

**Theorem:** E[iterations] <= 4/delta for any non-zero success probability delta.

Three operational regions:
- Marginal (delta < 0.3): high variance, needs dynamic calibration
- Practical (0.3 <= delta <= 0.6): optimal for real-world
- High-Performance (delta > 0.6): fast convergence, safety-critical

Empirical delta values from real systems: GPT-4 code repair delta=0.543, CodeLlama-34b invariant generation delta=0.360, Baldur proof synthesis delta=0.479, AssertLLM specification synthesis delta=0.880.

Validated with 90,000 Monte Carlo trials.

- https://arxiv.org/abs/2512.02080
- https://github.com/jamesdhope/markov-chain-4-llm-bounds-proof

### SpecVerify (RE 2025)
Claude 3.5 Sonnet + ESBMC for automated formal verification of cyber-physical systems from Lockheed Martin benchmark. 46.5% verification accuracy, comparable to NASA's CoCoSim but with lower false positives.

- https://arxiv.org/html/2507.04857

---

## 2. Smart Contract / Web3 Systems

### PropertyGPT (Patterns B+A) -- NDSS 2025 Distinguished Paper
The most direct LLM + formal verification for smart contracts. 8-step pipeline:
1. Embed 623 human-written properties (from 23 Certora audit projects) into vector DB
2. Embed subject contract code, retrieve similar references (dot product, threshold 0.8)
3. GPT-4 generates candidate properties via in-context learning
4. Compilation + static analysis feedback for iterative revision (up to 9 attempts, 87% success)
5. Weighted ranking: `Score = 0.134*X_raw + 0.556*X_summary + 0.141*Y_raw + 0.168*Y_summary`
6. Z3 + custom BMC prover (38K lines C++) formally verifies properties

PSL extends Solidity with invariants, pre/post-conditions (Hoare logic), and cross-function rules. Supports `old(v)` for temporal variables.

**Results:** 80% recall, 64% precision, F1=0.71. Detected 26/37 CVEs. Found 12 zero-day vulnerabilities, $8,256 in bug bounties. Outperforms GPTScan (5 CVEs), Slither (1 CVE), Mythril (3 CVEs), Manticore (0 CVEs).

- https://arxiv.org/abs/2405.02580
- https://github.com/Pr0pertyGPT/PropertyGPT

### Certora AI Composer (Pattern A) -- Dec 2025
Iterative loop: Claude Sonnet generates Solidity from CVL specs -> Certora Prover verifies -> counterexamples fed back on failure. Human-in-the-loop Debug Console. RAG from CVL manual.

**Certora Prover internals:**
1. Decompiler: EVM/eBPF/WASM bytecode -> TAC (Three-Address Code)
2. Static analysis: abstract interpretation for sound invariants
3. VC Generator: mathematical constraints for property violations
4. SMT solver suite: Z3, CVC5, Yices, Vampire
5. Pointer analysis + method summarization for modularity

NOT strictly BMC -- SMT-based verification of full program semantics with user-guided loop bounds. Can prove universal properties (all executions correct).

Open-source alpha. Requires Python 3.12+, Docker, Claude API key, Certora Prover.

- https://github.com/Certora/AIComposer
- https://docs.certora.com/en/latest/docs/cvl/index.html

### SmartInv (Pattern B) -- IEEE S&P 2024
Fine-tuned foundation model with "Tier of Thought" prompting across multiple contract modalities. 3.5x more bug-critical invariants, 4x more bugs in 150x less time. 119 zero-days from 89,621 contracts, 5 confirmed high-severity.

- https://arxiv.org/abs/2411.09217

### LLMs as Verification Oracles (Sep 2025)
Empirical evaluation of GPT-5 as alternative to Certora Prover and SolCMC for property validity prediction. Reasoning LLMs are "surprisingly effective" but lack soundness guarantees. Certora over-approximates reachable states (spurious counterexamples); LLMs provide more detailed trace explanations.

- https://arxiv.org/abs/2509.19153

---

## 3. Move Prover + AI

### MSG: Agentic Specification Generator for Move (Georgia Tech, 2025)
Four independent ClauseGen agents (aborts_if, modifies, ensures, loop invariants) + Specification Ensembler. Move Prover serves as verification oracle in counterexample-guided loop (up to 5 rounds).

Static interprocedural analysis identifies structs, constants, callees for context.

**Results (o3-mini):**
- 84% successful spec generation (300/357 Aptos core functions)
- 876 clauses, matched 82% of expert-written conditions
- 33.2% novel clauses that human experts missed
- Agentic (84%) vs all-in-one (53.5%); with Move Prover feedback (84%) vs without (70.9%)

- https://github.com/sslab-gatech/MSG
- https://arxiv.org/html/2509.24515

---

## 4. SMT Solver Enhancement via LLMs

### AquaForte (Pattern E) -- Jan 2026
LLM generates candidate function instantiations for QUFNIRA (undecidable theory). Fed to Z3/CVC5 which maintains soundness.

**Result:** Z3 +80% (785 vs 436 instances), CVC5 +183.6% (641 vs 226). Striking asymmetry: 3.6x on SAT, minimal on UNSAT. LLMs propose solutions well but can't prove exhaustive absence.

- https://arxiv.org/abs/2601.04675

### Sphinx: LLM-Guided SMT Solver Fuzzing
LLMs synthesize reusable formula generators from SMT theory grammars. Found 45 real bugs in Z3 and CVC5, 43 confirmed, 40 fixed.

- https://arxiv.org/html/2508.20340

---

## 5. Halmos, Kontrol, K Framework

### Halmos (a16z)
Symbolic testing for EVM contracts. Z3 (primary), CVC5, Yices backends. Bounded symbolic execution. Lazy branching. Storage layout reconstruction.

v0.3.0 (Oct 2025): stateful invariant testing, up to 32x faster. Used to formally verify Ethereum Pectra upgrade system contracts.

**No LLM integration as of Feb 2026.** However, LLM-generated Foundry tests can target Halmos for symbolic execution.

- https://github.com/a16z/halmos

### Kontrol (Runtime Verification / K Framework)
KEVM formal semantics + Foundry integration. Compositional symbolic execution. Used for Optimism pausability verification.

**No public AI/LLM integration as of Feb 2026.** Blog mentions detection pipeline combining "custom Slither-based detectors, LLMs, Kontrol, and Forge" but no published system.

- https://github.com/runtimeverification/kontrol

---

## 6. General Software Verification

### Dafny + LLM
- **dafny-annotator:** Multi-model (Claude Opus 4.5 + GPT-5.2) achieves 98.2% on 110 programs, 8 repair iterations. Fine-tuned LLaMA 8B: 50.6%. Synthetic data via DafnySynth ($10 API cost).
  - https://github.com/metareflection/dafny-annotator
- **DafnyPro (POPL 2026):** Diff-checker + pruner + hint-augmentation. Claude Sonnet 3.5: 86% on DafnyBench (+16pp SOTA). Fine-tuned Qwen 14B: 70%.
  - https://arxiv.org/abs/2601.05385
- **Dafny MCP Server:** MCP server for Dafny verification with Claude.
  - https://github.com/namin/dafny-mcp
- **VeriCoding (Sep 2025):** 12,504 specs. Dafny 82%, Verus 44%, Lean 27%.
  - https://arxiv.org/abs/2509.22908

### Verus/Rust Verification
- **AutoVerus (OOPSLA 2025, Microsoft Research):** Multi-agent network (~10 agents) mimicking three expert phases. Uses Lynette (AST analysis on Verus parser). GPT-4o/DeepSeek-R1: 90%+ on 150 tasks (vs 45% direct prompting). >50% solved in <30s.
  - https://arxiv.org/abs/2409.13082
- **SAFE (ICLR 2025):** Self-evolving spec + proof generation. DeepSeekCoder: 79.14% on VerusBench (GPT-4o: 11.51%). 19,017 specs, 9,706 verified functions.
  - https://arxiv.org/abs/2410.15756
- **AlphaVerus (ICML 2025, CMU, Distinguished Artifact):** Self-improving translation + Treefinement tree search. LLaMA-3.1-70B: 38% HumanEval-Verified, 65.7% MBPP. 100x less data than SAFE.
  - https://arxiv.org/abs/2412.06176

### Lean 4 Theorem Proving
- **Hilbert (Apple, NeurIPS 2025):** Dual LLM (informal reasoner + formal prover) + recursive decomposition. 99.2% miniF2F, 70% PutnamBench (422% over best public baseline).
  - https://github.com/apple/ml-hilbert
- **APOLLO (NeurIPS 2025):** Model-agnostic agentic framework. 84.9% miniF2F (sub-8B). Cuts sample complexity 1-2 orders of magnitude.
  - https://github.com/aziksh-ospanov/APOLLO
- **DeepSeek-Prover V2:** Recursive subgoal decomposition + RL. 88.9% miniF2F, 49/658 PutnamBench.
  - https://arxiv.org/abs/2504.21801
- **Lean Copilot:** LLM inference natively in Lean. 74.2% proof steps automated (vs 40.1% aesop).
  - https://github.com/lean-dojo/LeanCopilot

### TLA+ / Distributed Systems
- **LMGPA (Dec 2025):** LLM generates normalized claim decompositions for TLAPS provers. 119 theorems benchmark.
  - https://arxiv.org/abs/2512.09758
- **RAG + TLAPS (Jan 2025):** GPT-4o + ChromaDB for proof generation with retrieval over verified examples. Handles intermediate complexity; struggles with highly complex theorems.
  - https://arxiv.org/html/2501.03073
- **SysMoBench:** LLM-generated TLA+ specs. 8.3% safety violations but 41.9% liveness violations -- LLMs struggle with temporal reasoning and fairness.
  - https://arxiv.org/abs/2509.23130
- **Bespoke TLA+ Transpilation:** Claude generates C++ from TLA+ specs, TLC model checker validates.

### Alloy
- **Alloy spec repair (Springer ESE, 2025):** Dual-agent + auto-prompting with Alloy Analyzer feedback. 1,974 defective models, 106,596 repair attempts.
  - https://link.springer.com/article/10.1007/s10664-025-10687-1
- **LLM Alloy formula synthesis (Feb 2025):** o3-mini/DeepSeek R1 synthesize complete Alloy formulas from natural language.
  - https://arxiv.org/pdf/2502.15441
- **LLM Alloy test generation (Oct 2025):** GPT-5 generates test cases for specs. >95% syntax correctness, >90% oracle conformance.
  - https://arxiv.org/pdf/2510.23350

### IRIS (ICLR 2025, Pattern C)
LLM mines taint sources/sinks -> CodeQL data-flow analysis -> LLM filters false positives. 55 vulns (vs 27 CodeQL alone). Found 4 previously unknown vulns.
- https://arxiv.org/abs/2405.17238
- https://github.com/iris-sast/iris

### LLMDFA (NeurIPS 2024)
LLM synthesizes code delegating to SMT solvers for path feasibility. 87.1% precision, 80.8% recall.
- https://github.com/chengpeng-wang/LLMDFA

### UCLID5 Auto-Formalization (UC Berkeley, 2025)
LLM generates UCLID5 models from natural language. UCLID5 engine (BMC + SMT) validates. Coverage-based feedback.
- https://www2.eecs.berkeley.edu/Pubs/TechRpts/2025/EECS-2025-115.html

---

## 7. Notable Gaps (No LLM Integration as of Feb 2026)

- **Halmos** (a16z): No LLM-in-the-loop, just used as a target for tests
- **SPIN model checker**: No LLM + Promela work
- **nuXmv / IC3/PDR**: No LLM integration
- **K Framework / KEVM**: Only passing mentions, no published system
- **Boolector**: Only indirectly via ESBMC

---

## 8. Key Survey Papers

- **"The Fusion of Large Language Models and Formal Methods for Trustworthy AI Agents: A Roadmap"** (Dec 2024) -- most comprehensive survey. Bidirectional taxonomy: FMs for LLMs and LLMs for FMs.
  - https://arxiv.org/abs/2412.06512
- **Martin Kleppmann: "AI will make formal verification go mainstream"** (Dec 2025) -- argues LLMs reduce FM cost from "23 lines of proof per line of code" to near-automatic. AI-generated code needs FM as quality gate.
  - https://martin.kleppmann.com/2025/12/08/ai-formal-verification.html
