# Module Structure

Every Specl specification is a module. A module contains declarations in this order:

```specl
module Name

const C: Int              // constants, set at check time
var x: 0..10              // state variables with type bounds

type NodeId = 0..N        // type aliases (optional)

init { x = 0 }            // initial state (exactly one)

action Step() { ... }     // state transitions (one or more)

func Helper(a) { ... }    // pure functions (optional)

invariant Safe { ... }    // safety properties (one or more)
```

## Module name

The `module` declaration must be the first non-comment line. The name is for documentation only — it does not affect the checker.

```specl
module TwoPhaseCommit
```

## Declaration order

Within a module, declarations can appear in any order. Constants, variables, types, init, actions, functions, and invariants can be interleaved. The convention above is just a stylistic recommendation.

## Comments

Line comments use `//`. Block comments use `/* ... */`.

```specl
// This is a line comment

/* This is a
   block comment */
```
