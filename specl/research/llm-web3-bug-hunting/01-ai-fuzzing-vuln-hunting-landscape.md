# AI Fuzzing & Vulnerability Hunting Landscape (Feb 2026)

Research conducted February 14, 2026.

## Key Breakthroughs

### SCONE-bench (Anthropic, Dec 2025)
405 real-world exploited smart contracts benchmark. AI agents exploit 51% of them, $550M simulated stolen funds, $1.22/contract scan cost. Exploit capability doubling every 1.3 months.

### XBOW
Autonomous AI pentester, #1 on HackerOne globally in 90 days. $117M funding (Sequoia). Finds and exploits web application vulnerabilities end-to-end without human intervention.

### DARPA AIxCC (Aug 2025)
- **ATLANTIS** (Team Atlanta, 1st place, $4M): LLMs + symbolic execution + directed fuzzing on Kubernetes. Found 43 vulns, patched 31. Also found 18 real-world vulns not planted by competition. $73.9K Azure, $29.4K LLM credits.
- **Buttercup** (Trail of Bits, 2nd place, $3M): AI-augmented mutational fuzzing + tree-sitter/CodeQuery + 7 AI patch agents. $181 per point. Now open-source: https://github.com/trailofbits/buttercup

### Google Big Sleep
Gemini-powered. Found 20 vulns in open-source. Foiled active SQLite exploit before it was used in the wild.

### OpenAI Aardvark
GPT-5 autonomous security researcher. 92% detection in benchmarks. Private beta.

### Claude Opus 4.6 Zero-Days
Found and exploited zero-days in real-world systems autonomously during safety evaluations.

## Smart Contract Auditing Tools

### Zellic V12
LLM + static analysis Solidity auditor. Matches/exceeds junior auditors. Free tier available.

### Nethermind AuditAgent
ML + symbolic execution + exploit KB. Flagged exact $9.8M ResupplyFi vulnerability before the exploit occurred.

### Trail of Bits Slither-MCP (Nov 2025)
MCP server wrapping Slither's static analysis engine, making it directly accessible to LLMs. Grounds AI analysis in program facts (call graphs, inheritance, data flow). Reduces hallucination.
- https://github.com/trailofbits/slither-mcp

### Cyfrin Aderyn MCP
Rust-based Solidity static analyzer exposed via MCP. 100+ vulnerability patterns. Integrated with Claude Code, Cursor.
- https://github.com/Cyfrin/aderyn

### GPTScan (ICSE 2024)
GPT + static analysis. >90% precision for tokens, 70% recall. $0.01 per 1,000 lines of Solidity. Found 9 vulns missed by human auditors.
- https://arxiv.org/abs/2308.03314
- https://github.com/GPTScan/GPTScan

### SolAgent (2025)
Multi-agent LLM system with Forge + Slither dual-loop. 64.39% Pass@1, reduces vulnerabilities by up to 39.77%.
- https://arxiv.org/html/2601.23009v1

## Bug Bounty Economics

- **curl** killed its bounty program due to AI spam (too many low-quality AI-generated reports)
- **Immunefi** bans AI-generated submissions
- **Code4rena** created "Bot Races" -- dedicated competitions for AI tools
- **XBOW** topped HackerOne leaderboard
- Audit pricing: $5K-$200K+ range. AI compressing low-end but not replacing high-end manual audits
- False positive rates remain 82-99% for standalone LLM approaches

## The AI vs Human Reality Check

- AI tools are strong at pattern matching known vulnerability classes
- Weak at novel logic bugs, cross-contract interactions, economic exploits
- Best results come from hybrid AI + human workflows
- The "junior auditor" level has been reached; "senior auditor" level remains far off
- Standalone LLM analysis still produces unacceptable false positive rates for production use
