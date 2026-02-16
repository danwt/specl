# Quantifiers

## Universal quantifier: `all`

True if the predicate holds for every value in the range:

```specl
all x in 0..N: balance[x] >= 0                    // all balances non-negative
all i in 0..N: all j in 0..N: ...                  // nested: all pairs
```

## Existential quantifier: `any`

True if the predicate holds for at least one value:

```specl
any x in 0..N: role[x] == 2                       // some process is leader
```

## Usage

Quantifiers work in invariants, guards, and any expression:

```specl
invariant AllPositive { all x in 0..N: balance[x] >= 0 }

action NeedLeader() {
    require any i in 0..N: role[i] == 2
    ...
}
```

## `any` is boolean only

`any` is a boolean quantifier — it returns `true` or `false`. You **cannot** use the bound variable outside the quantifier body:

```specl
// WRONG: v is not in scope outside the quantifier
let v = any v in 0..N: state[v] == 2 in
state[v]

// RIGHT: use any for boolean checks only
require any v in 0..N: state[v] == 2
```

To pick a specific value satisfying a predicate, use `choose`:

```specl
let v = choose v in 0..N: state[v] == 2
```

## Precedence with `implies`

When nesting `all` quantifiers with `implies`, use parentheses to be explicit:

```specl
// Potentially confusing precedence
all i in 0..N: all j in 0..N:
    role[i] == 2 and role[j] == 2 and currentTerm[i] == currentTerm[j]
        implies i == j

// Explicit parentheses (recommended)
all i in 0..N: all j in 0..N:
    (role[i] == 2 and role[j] == 2 and currentTerm[i] == currentTerm[j])
        implies (i == j)
```
