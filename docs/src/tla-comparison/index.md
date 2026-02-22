# TLA+ Comparison

Specl is a modern replacement for TLA+/TLC. If you're coming from TLA+, this page maps the concepts.

## Syntax mapping

| TLA+ | Specl | Notes |
|------|-------|-------|
| `x' = x + 1` | `x = x + 1` | No primed variables |
| `x = y` (equality) | `x == y` | `=` is assignment in Specl |
| `UNCHANGED <<y, z>>` | *(implicit)* | Variables not mentioned stay unchanged |
| `/\` | `and` | Logical AND |
| `\/` | `or` | Logical OR |
| `~` | `not` | Logical NOT |
| `=>` | `implies` | Implication |
| `<=>` | `iff` | If and only if |
| `\in` | `in` | Set membership |
| `\notin` | `not in` | Set non-membership |
| `\A x \in S: P(x)` | `all x in S: P(x)` | Universal quantifier |
| `\E x \in S: P(x)` | `any x in S: P(x)` | Existential quantifier |
| `CHOOSE x \in S: P(x)` | `fix x in S: P(x)` | Deterministic choice |
| `[f EXCEPT ![k] = v]` | `f \| { k: v }` | Dict update |
| `[f EXCEPT ![k][j] = v]` | `f \| {k: f[k] \| {j: v}}` | Nested dict update |
| `{x \in S : P(x)}` | `{x in S if P(x)}` | Set comprehension |
| `SUBSET S` | `powerset(S)` | Powerset |
| `UNION S` | `union_all(S)` | Flatten set of sets |
| `S \cup T` | `S union T` | Set union |
| `S \cap T` | `S intersect T` | Set intersection |
| `S \ T` | `S diff T` | Set difference |
| `S \subseteq T` | `S subset_of T` | Subset test |
| `Cardinality(S)` | `len(S)` | Set/sequence size |
| `Head(s)` | `head(s)` | First element |
| `Tail(s)` | `tail(s)` | All but first |
| `Len(s)` | `len(s)` | Sequence length |
| `s \o t` | `s ++ t` | Sequence concatenation |
| `Append(s, x)` | `s ++ [x]` | Append |
| `SubSeq(s, lo, hi)` | `s[lo..hi]` | Subsequence |
| `Init == ...` | `init { ... }` | Initial state |
| `Next == A \/ B \/ C` | *(implicit)* | All actions OR'd automatically |
| `DOMAIN f` | `keys(f)` | Function/dict domain |
| `IF p THEN a ELSE b` | `if p then a else b` | Conditional expression |
| `LET x == expr IN body` | `let x = expr in body` | Let binding |

## Key differences

### No primed variables

TLA+ uses `x'` for the next-state value. Specl uses `=`:

```
TLA+:   Next == x' = x + 1 /\ y' = y
Specl:  action Step() { x = x + 1 }    // y unchanged implicitly
```

### No UNCHANGED

In TLA+, every action must explicitly list unchanged variables:

```
TLA+:   Inc == x' = x + 1 /\ UNCHANGED <<y, z, w>>
Specl:  action Inc() { x = x + 1 }
```

Forgetting a variable in `UNCHANGED` is a common TLA+ bug. Specl eliminates this class of errors entirely.

### No explicit Next

TLA+ requires an explicit `Next` formula that disjoins all actions:

```
TLA+:   Next == Inc \/ Dec \/ Reset
Specl:  // Not needed — all actions are implicitly OR'd
```

### `=` vs `==`

TLA+ uses `=` for both assignment and equality (context determines meaning). Specl separates them: `=` assigns, `==` compares.

### Word-based operators

TLA+ uses symbolic operators (`/\`, `\/`, `~`, `\in`). Specl uses words (`and`, `or`, `not`, `in`).

## Translating TLA+ to Specl

Use the built-in translator:

```bash
specl translate spec.tla -o spec.specl
```

The translator handles most TLA+ syntax. Manual adjustments may be needed for:

- Module composition (`EXTENDS`, `INSTANCE`) — not yet supported
- Recursive operators — not yet supported
- TLA+ idioms that don't map directly (e.g., function sets `[S -> T]`)
