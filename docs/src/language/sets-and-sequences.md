# Sets and Sequences

## Sets

Finite, unordered collections with no duplicates.

### Literals and comprehensions

```specl
{1, 2, 3}                                    // literal
{}                                            // empty set
{p in 0..N if state[p] == 1}                  // comprehension (filter)
```

### Set operations

| Operation | Syntax | Result |
|-----------|--------|--------|
| Membership | `x in S` | `Bool` |
| Non-membership | `x not in S` | `Bool` |
| Union | `S1 union S2` | `Set[T]` |
| Intersection | `S1 intersect S2` | `Set[T]` |
| Difference | `S1 diff S2` | `Set[T]` |
| Subset | `S1 subset_of S2` | `Bool` |
| Size | `len(S)` | `Int` |
| Powerset | `powerset(S)` | `Set[Set[T]]` |
| Flatten | `union_all(S)` | flattens `Set[Set[T]]` to `Set[T]` |

### Counting pattern

Use comprehensions with `len` to count:

```specl
// Count processes in a given state
len({p in 0..N if role[p] == 2})

// Quorum check
len({v in 0..N if voted[v]}) * 2 > N + 1
```

## Sequences

Ordered collections (0-indexed).

### Literals

```specl
[]                     // empty
[1, 2, 3]             // literal
```

### Sequence operations

| Operation | Syntax | Result |
|-----------|--------|--------|
| Index | `s[i]` | element at position `i` |
| Length | `len(s)` | `Int` |
| Head | `head(s)` | first element |
| Tail | `tail(s)` | all but first |
| Concat | `s1 ++ s2` | `Seq[T]` |
| Slice | `s[lo..hi]` | subsequence from `lo` to `hi` |
| Append | `s ++ [x]` | append element `x` |
| Prepend | `[x] ++ s` | prepend element `x` |

### Message passing with sequences

A common pattern is to encode messages as sequences with typed fields:

```specl
var msgs: Set[Seq[Int]]

// Message: [type, src, dst, payload]
action Send(src: 0..N, dst: 0..N) {
    msgs = msgs union {[1, src, dst, currentTerm[src]]}
}

action Receive(src: 0..N, dst: 0..N, term: Int) {
    require [1, src, dst, term] in msgs
    // process...
}
```

### Log operations

Sequences are used for logs in consensus protocols:

```specl
var log: Dict[Int, Seq[Int]]

// Append entry
log = log | {i: log[i] ++ [value]}

// Last element
let lastTerm = if len(log[i]) == 0 then 0 else log[i][len(log[i]) - 1]

// Truncate (keep first k entries)
log = log | {i: log[i][0..k]}
```
