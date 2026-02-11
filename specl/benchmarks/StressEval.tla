---- MODULE StressEval ----
\* Stress test: Expression evaluation
\* Many arithmetic operations per state transition

EXTENDS Integers

VARIABLES x, y

Init == x = 0 /\ y = 0

Step ==
    \* Heavy computation in guard
    /\ (x * x + y * y) < 20000
    /\ (x + y) * 2 < 400
    /\ x * 3 + y * 2 < 500
    \* Heavy computation in effect
    /\ x' = (x + 1) % 100
    /\ y' = (y + x) % 100

Next == Step

Spec == Init /\ [][Next]_<<x, y>>

Bound == x < 100 /\ y < 100
====
