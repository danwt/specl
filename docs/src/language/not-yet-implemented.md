# Not Yet Implemented

The following features parse and type-check but are **not yet supported** by the model checker. Using them will not cause errors, but they will have no effect on verification.

## Temporal operators

```specl
always P                  // P holds in every state of every behavior
eventually P              // P holds in some state of every behavior
P leads_to Q              // whenever P holds, Q eventually holds
```

These compile to the IR but are blocked at the model checking stage. The checker currently performs safety checking only (invariants).

## Fairness declarations

```specl
fairness weak Action      // Action fires infinitely often if always enabled
fairness strong Action    // Action fires infinitely often if enabled infinitely often
```

Parsed and stored, but not used by the checker.

## Enabled and changes

```specl
enabled(Action)           // true if Action is enabled in the current state
changes(var)              // true if var changes in this transition
```

Parsed and type-checked, but not evaluated.

## Module composition

`EXTENDS` and `INSTANCE` (TLA+-style module composition) are not yet supported. Each spec is a single module.

## Recursive functions

Functions cannot currently call themselves.

## Planned future features

- **Cranelift JIT** — compile guards and effects to native code via Cranelift for an estimated 3-10x additional speedup
- **Compiled verifier** — SPIN-style: generate Rust source, compile with `rustc`, `dlopen` the result
