---- MODULE Counter ----
EXTENDS Integers
VARIABLE count

Init == count = 0
Inc == count < 5 /\ count' = count + 1
Dec == count > 0 /\ count' = count - 1
Next == Inc \/ Dec

Bounded == count >= 0 /\ count <= 5
====
