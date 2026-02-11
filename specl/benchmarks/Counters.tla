---- MODULE Counters ----
\* N-Counter Benchmark
\* State space: (MAX+1)^(N+1) states
\* N is highest index, so 0..N gives N+1 counters

EXTENDS Integers

CONSTANTS N, MAX

VARIABLES counters

Init == counters = [i \in 0..N |-> 0]

Increment(i) ==
    /\ counters[i] < MAX
    /\ counters' = [counters EXCEPT ![i] = counters[i] + 1]

Reset(i) ==
    /\ counters[i] > 0
    /\ counters' = [counters EXCEPT ![i] = 0]

Next == \E i \in 0..N: Increment(i) \/ Reset(i)

Spec == Init /\ [][Next]_counters

AllInRange == \A i \in 0..N: counters[i] >= 0 /\ counters[i] <= MAX
====
