# Traffic Light Controller

This example models a traffic light intersection and verifies that conflicting directions never have green simultaneously.

## The spec

```specl
module TrafficLight

// 0=red, 1=yellow, 2=green
var northSouth: 0..2
var eastWest: 0..2

init { northSouth = 0 and eastWest = 2 }

action NSGreen() { require northSouth == 0; require eastWest == 0; northSouth = 2 }
action NSYellow() { require northSouth == 2; northSouth = 1 }
action NSRed() { require northSouth == 1; northSouth = 0 }
action EWGreen() { require eastWest == 0; require northSouth == 0; eastWest = 2 }
action EWYellow() { require eastWest == 2; eastWest = 1 }
action EWRed() { require eastWest == 1; eastWest = 0 }

invariant NoBothGreen { not (northSouth == 2 and eastWest == 2) }
invariant SafeGreen {
    (northSouth == 2) implies (eastWest == 0)
    and (eastWest == 2) implies (northSouth == 0)
}
```

## How the guards enforce safety

The key insight is in `NSGreen` and `EWGreen`: each requires the *other* direction to be red (`== 0`) before going green. The checker verifies this by exploring every possible sequence of light changes and confirming no interleaving violates the invariants.

## Running it

```bash
specl check traffic-light.specl
```

The state space is small (only 9 reachable states from the 3x3 grid of light combinations), but the checker proves that no sequence of transitions can ever reach a state where both directions are green.

## What this teaches

- **Guards as safety mechanism.** The `require` statements are not just preconditions — they define the allowed transitions. The checker verifies that the guard structure is sufficient to maintain the invariants.
- **Multiple invariants.** `NoBothGreen` is a simple prohibition; `SafeGreen` is a stronger property using `implies`. Both are checked in every reachable state.
- **Encoding enums as integers.** `0=red, 1=yellow, 2=green` is a common Specl pattern. Use comments to document the mapping.
