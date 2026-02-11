---- MODULE StressHash ----
\* Stress test: State hashing and storage
\* Large state with many variables - 11^5 = 161,051 states

EXTENDS Integers

VARIABLES a, b, c, d, e

Init == a = 0 /\ b = 0 /\ c = 0 /\ d = 0 /\ e = 0

IncA == a < 10 /\ a' = a + 1 /\ UNCHANGED <<b, c, d, e>>
IncB == b < 10 /\ b' = b + 1 /\ UNCHANGED <<a, c, d, e>>
IncC == c < 10 /\ c' = c + 1 /\ UNCHANGED <<a, b, d, e>>
IncD == d < 10 /\ d' = d + 1 /\ UNCHANGED <<a, b, c, e>>
IncE == e < 10 /\ e' = e + 1 /\ UNCHANGED <<a, b, c, d>>

Next == IncA \/ IncB \/ IncC \/ IncD \/ IncE

Spec == Init /\ [][Next]_<<a, b, c, d, e>>

Bound == a <= 10 /\ b <= 10 /\ c <= 10 /\ d <= 10 /\ e <= 10
====
