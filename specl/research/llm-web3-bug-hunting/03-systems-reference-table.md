# LLM + Formal Verification Systems Reference Table (Feb 2026)

## Smart Contract / Web3 Systems

| System | FM Backend | LLM | Pattern | Key Result | Paper |
|--------|-----------|-----|---------|------------|-------|
| PropertyGPT | Z3 + custom BMC (38K LoC C++) | GPT-4 | B+A | 26/37 CVEs, 12 zero-days, $8.2K bounties | NDSS 2025 |
| Certora AI Composer | Certora Prover (Z3/CVC5/Yices/Vampire) | Claude Sonnet | A | Open-source alpha Dec 2025 | -- |
| SmartInv | Custom checker | Fine-tuned FM | B | 119 zero-days from 89,621 contracts | IEEE S&P 2024 |
| GPTScan | Static analysis | GPT-4 | C | >90% precision (tokens), 70% recall | ICSE 2024 |
| MSG (Move) | Move Prover (Boogie/Z3) | o3-mini | A | 84% spec gen, 33% novel clauses | 2025 |
| SolAgent | Forge + Slither | Multi-agent LLM | A | 64.39% Pass@1 | 2025 |
| Slither-MCP | Slither static analysis | Any (via MCP) | C | Grounds LLM in program facts | Nov 2025 |
| Aderyn MCP | Aderyn static analysis | Any (via MCP) | C | 100+ vulnerability patterns | 2025 |
| LLM Verif. Oracles | vs Certora/SolCMC | GPT-5 | -- | "Surprisingly effective" | Sep 2025 |

## BMC / SMT Systems (General Software)

| System | FM Backend | LLM | Pattern | Key Result | Paper |
|--------|-----------|-----|---------|------------|-------|
| ESBMC-AI | ESBMC (Z3/Boolector) | GPT-4o | A | 80-90% fix rate (vs 31-37% without) | AST 2025 |
| ESBMC-ibmc | ESBMC (modified BMC) | GPT-4-class | B | ASE 2024 Distinguished Paper | ASE 2024 |
| LaM4Inv | CBMC/ESBMC + SMT | Multiple | A+B | 309/316 invariants (vs 218) | ASE 2024 |
| LEMUR | Z3 SMT solver | O1/O3-mini | A | 133/133 Code2Inv (100%) | ICLR 2024+ |
| AquaForte | Z3, CVC5 | GPT-4.1 | E | +80% Z3, +184% CVC5 | Jan 2026 |
| LLMDFA | SMT solvers | LLM | C | 87.1% precision, 80.8% recall | NeurIPS 2024 |
| IRIS | CodeQL | GPT-4 | C | 55 vulns (vs 27 CodeQL) | ICLR 2025 |
| SpecVerify | ESBMC | Claude 3.5 Sonnet | A | 46.5% on Lockheed Martin benchmark | RE 2025 |
| ATLANTIS | Symbolic exec + fuzzing | Multiple | A+C | Won DARPA AIxCC, 43 vulns | Aug 2025 |

## Program Verification (Dafny, Verus, Alloy, TLA+, UCLID5)

| System | FM Backend | LLM | Pattern | Key Result | Paper |
|--------|-----------|-----|---------|------------|-------|
| dafny-annotator | Dafny/Boogie/Z3 | Claude Opus 4.5 + GPT-5.2 | A | 98.2% success (110 programs) | 2025 |
| DafnyPro | Dafny/Z3 | Claude Sonnet 3.5 | A | 86% DafnyBench (+16pp SOTA) | POPL 2026 |
| AutoVerus | Verus/Z3 | GPT-4o/DeepSeek-R1 | A | 90%+ of 150 tasks | OOPSLA 2025 |
| SAFE | Verus/Z3 | DeepSeekCoder (fine-tuned) | D | 79.14% VerusBench | ICLR 2025 |
| AlphaVerus | Verus | LLaMA-3.1-70B | D | 38% HumanEval-Verified | ICML 2025 |
| Alloy repair | Alloy Analyzer | Multiple | A | 1,974 defective models | ESE 2025 |
| LMGPA | TLAPS | Multiple | A | 119 theorems | Dec 2025 |
| SysMoBench | TLC (TLA+) | Multiple | -- | 41.9% liveness violations | Sep 2025 |
| UCLID5 auto-form | UCLID5 (BMC+SMT) | LLM | A | Coverage-based refinement | UC Berkeley 2025 |

## Theorem Proving (Lean 4)

| System | FM Backend | LLM | Pattern | Key Result | Paper |
|--------|-----------|-----|---------|------------|-------|
| Hilbert | Lean 4 | Dual LLM (Apple) | A | 99.2% miniF2F, 70% PutnamBench | NeurIPS 2025 |
| APOLLO | Lean 4 | o3/o4-mini, Goedel | A | 84.9% miniF2F (sub-8B) | NeurIPS 2025 |
| DeepSeek-Prover V2 | Lean 4 | DeepSeek-671B | A+D | 88.9% miniF2F | 2025 |
| Lean Copilot | Lean 4 | ReProver + LLMs | A | 74.2% steps automated | 2024 |

## Formal Verification Benchmarks

| Benchmark | Domain | Size | Best Result |
|-----------|--------|------|-------------|
| VeriCoding | Dafny/Verus/Lean | 12,504 specs | 82% Dafny, 44% Verus, 27% Lean |
| InvBench | SV-COMP invariants | 226 instances | 29.2% speedup (fine-tuned Qwen) |
| SysMoBench | TLA+ system models | 11 systems | 8.3% safety violations, 41.9% liveness |
| Code2Inv | Loop invariants | 133 tasks | 100% (LEMUR) |
| miniF2F | Math proofs (Lean) | standard | 99.2% (Hilbert) |
| PutnamBench | Math proofs (Lean) | 660 problems | 70% (Hilbert) |
| DafnyBench | Dafny verification | standard | 86% (DafnyPro) |
| VerusBench | Rust verification | 150 tasks | 90%+ (AutoVerus) |

## Commercial Products

| Product | FM Backend | LLM Integration | URL |
|---------|-----------|-----------------|-----|
| Certora AI Composer | Certora Prover (SMT) | Claude in iterative loop | github.com/Certora/AIComposer |
| CertiK | Custom FM engine (BISSOL) | AI + FM hybrid | certik.com |
| Slither-MCP | Slither static analysis | Any LLM via MCP | github.com/trailofbits/slither-mcp |
| Aderyn MCP | Aderyn static analysis | Any LLM via MCP | github.com/Cyfrin/aderyn |
| SmartContract.us | Slither + Mythril | Claude | smartcontract.us |
| Diffblue Cover | CBMC-derived | AI test generation | diffblue.com |
| Runtime Verification | Kontrol (KEVM) | Mentions LLM pipeline | runtimeverification.com |
| Dafny MCP | Dafny verifier | Claude via MCP | github.com/namin/dafny-mcp |

## Key Theoretical Results

| Result | Claim | Paper |
|--------|-------|-------|
| 4/delta bound | LLM-verifier loop converges in E[4/delta] iterations | arXiv:2512.02080 |
| LEMUR calculus | Soundness proof for LLM-reasoner deductive interaction | ICLR 2024 |
| AquaForte asymmetry | LLMs help SAT 3.6x but not UNSAT -- can propose but not prove absence | arXiv:2601.04675 |
| SysMoBench liveness gap | LLMs miss fairness assumptions, 41.9% liveness violations vs 8.3% safety | arXiv:2509.23130 |
| Kleppmann thesis | AI will reduce FM cost from "23 proof lines per code line" to near-automatic | Dec 2025 blog |
