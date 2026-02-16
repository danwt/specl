# Constants and Variables

## Constants

Constants are values fixed for a given check run. Set them with `-c` on the command line.

```specl
const N: Int
const MAX: 0..10
const TIMEOUT: Nat
```

```bash
specl check spec.specl -c N=3 -c MAX=5 -c TIMEOUT=10
```

Constants can be used in type expressions, action parameters, and any expression throughout the spec.

## Variables

Variables are the state that the model checker tracks. Each variable has a name and a type.

```specl
var count: 0..10
var active: Bool
var log: Seq[Int]
var role: Dict[Int, Int]
```

### Type bounds matter

The type of a variable determines the possible values the checker considers. Use the tightest bounds possible to keep the state space small.

```specl
// Tight — state space: 6 values per variable
var phase: 0..5

// Loose — state space: unbounded, may not terminate
var phase: Int
```

### Initial values

Every variable must be assigned in the `init` block.

```specl
init {
    count = 0
    and active = true
    and log = []
    and role = {p: 0 for p in 0..N}
}
```

Use `and` to assign multiple variables. Use `;` between statements in init blocks when needed.
