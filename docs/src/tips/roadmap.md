# Roadmap

## Parsed but not yet in model checker

These features parse and type-check. They will be implemented in the model checker in future releases.

- **Temporal operators** — `always`, `eventually`, `leads_to`. Compile to IR but blocked at model checking. Will enable liveness verification.
- **Fairness declarations** — `fairness weak Action`, `fairness strong Action`. Parsed but not used by the checker. Required for meaningful liveness checking.
- **`enabled(Action)` and `changes(var)`** — parsed, not evaluated. Will enable stuttering-sensitive properties.

## Not yet implemented

- **Module composition** — `EXTENDS` / `INSTANCE` (TLA+-style module imports). Currently each spec is a single module.
- **Recursive functions** — functions cannot call themselves.

## Planned optimizations

- **Cranelift JIT** — compile guards and effects to native code via Cranelift. Estimated 3-10x additional speedup over the current bytecode VM.
- **Swarm verification** — N independent search instances with randomized action orderings. Effective for finding bugs in very large state spaces without exhaustive exploration.
- **Compiled verifier** — SPIN-style approach: generate Rust source code from the spec, compile with `rustc`, `dlopen` the result. Maximum performance for production verification runs.
