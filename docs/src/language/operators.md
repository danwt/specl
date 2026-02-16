# Operators

## Complete operator reference

### Logical operators

| Operator | Meaning | Example |
|----------|---------|---------|
| `and` | Logical AND | `x > 0 and y > 0` |
| `or` | Logical OR | `x > 0 or y > 0` |
| `not` | Logical NOT | `not active` |
| `implies` | Implication | `(x > 0) implies (y > 0)` |
| `iff` | If and only if | `x == 0 iff y == 0` |

### Comparison operators

| Operator | Meaning |
|----------|---------|
| `==` | Equal |
| `!=` | Not equal |
| `<` | Less than |
| `<=` | Less than or equal |
| `>` | Greater than |
| `>=` | Greater than or equal |

### Arithmetic operators

| Operator | Meaning |
|----------|---------|
| `+` | Addition |
| `-` | Subtraction |
| `*` | Multiplication |
| `/` | Integer division |
| `%` | Modulo |

### Set operators

| Operator | Meaning | Type |
|----------|---------|------|
| `in` | Membership | `T, Set[T] -> Bool` |
| `not in` | Non-membership | `T, Set[T] -> Bool` |
| `union` | Union | `Set[T], Set[T] -> Set[T]` |
| `intersect` | Intersection | `Set[T], Set[T] -> Set[T]` |
| `diff` | Difference | `Set[T], Set[T] -> Set[T]` |
| `subset_of` | Subset test | `Set[T], Set[T] -> Bool` |

### Sequence operators

| Operator/Function | Meaning | Type |
|-------------------|---------|------|
| `++` | Concatenation | `Seq[T], Seq[T] -> Seq[T]` |
| `s[i]` | Index access | `Seq[T], Int -> T` |
| `s[lo..hi]` | Slice | `Seq[T], Int, Int -> Seq[T]` |

### Built-in functions

| Function | Meaning | Type |
|----------|---------|------|
| `len(x)` | Length/size | `Seq[T] -> Int` or `Set[T] -> Int` |
| `head(s)` | First element | `Seq[T] -> T` |
| `tail(s)` | All but first | `Seq[T] -> Seq[T]` |
| `keys(d)` | Dict keys | `Dict[K,V] -> Set[K]` |
| `values(d)` | Dict values | `Dict[K,V] -> Set[V]` |
| `powerset(s)` | All subsets | `Set[T] -> Set[Set[T]]` |
| `union_all(s)` | Flatten sets | `Set[Set[T]] -> Set[T]` |

### Dict operators

| Operator | Meaning |
|----------|---------|
| `d[k]` | Access value at key `k` |
| `d1 \| d2` | Merge (d2 values override d1) |
