------------------------ MODULE multipaxosreconfig ------------------------
(* Multi-Paxos with reconfiguration
   From: Lamport "Paxos Made Simple" + Van Renesse & Altinbuken
   N+1 acceptors, MaxBallot+1 ballots, MaxSlot+1 slots
   Values 0..V regular, V+1 = reconfig command
   Config 0: {0..N}, Config 1: {1..N}
   WINDOW = 1: reconfig in slot s activates at s+1 *)

EXTENDS Integers, FiniteSets

CONSTANTS N, MaxBallot, MaxSlot, V

VARIABLES maxBal, maxVBal, maxVal, proposed, accepted, decided

vars == <<maxBal, maxVBal, maxVal, proposed, accepted, decided>>

Acceptors == 0..N
Ballots == 0..MaxBallot
Slots == 0..MaxSlot

InConfig(a, cfg) == IF cfg = 0 THEN TRUE ELSE a >= 1

MemberCount(cfg) == IF cfg = 0 THEN N + 1 ELSE N

ConfigForSlot(s) ==
    IF \E s2 \in Slots : s2 + 1 <= s /\ decided[s2] = V + 1
    THEN 1 ELSE 0

SafeAt(b, s, v) ==
    LET cfg == ConfigForSlot(s) IN
    \E Q \in SUBSET Acceptors :
        /\ \A a \in Q : InConfig(a, cfg)
        /\ Cardinality(Q) * 2 > MemberCount(cfg)
        /\ \A a \in Q : maxBal[a] >= b
        /\ \/ \A a \in Q : maxVBal[a][s] = -1
           \/ \E c \in Ballots :
                /\ c < b
                /\ \A a \in Q : maxVBal[a][s] <= c
                /\ \E a \in Q : maxVBal[a][s] = c /\ maxVal[a][s] = v

Init ==
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> [s \in Slots |-> -1]]
    /\ maxVal = [a \in Acceptors |-> [s \in Slots |-> -1]]
    /\ proposed = [b \in Ballots |-> [s \in Slots |-> -1]]
    /\ accepted = [b \in Ballots |-> [s \in Slots |-> [a \in Acceptors |-> FALSE]]]
    /\ decided = [s \in Slots |-> -1]

Promise(b, a) ==
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED <<maxVBal, maxVal, proposed, accepted, decided>>

Propose(b, s, v) ==
    /\ proposed[b][s] = -1
    /\ v >= 0 /\ v <= V + 1
    /\ SafeAt(b, s, v)
    /\ v # V + 1 \/ ~\E s2 \in Slots :
         decided[s2] = V + 1
         \/ (s2 # s /\ \E b2 \in Ballots : proposed[b2][s2] = V + 1)
    /\ proposed' = [proposed EXCEPT ![b] = [proposed[b] EXCEPT ![s] = v]]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, accepted, decided>>

Accept(b, s, a) ==
    /\ proposed[b][s] # -1
    /\ maxBal[a] <= b
    /\ InConfig(a, ConfigForSlot(s))
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = [maxVBal[a] EXCEPT ![s] = b]]
    /\ maxVal' = [maxVal EXCEPT ![a] = [maxVal[a] EXCEPT ![s] = proposed[b][s]]]
    /\ accepted' = [accepted EXCEPT ![b] = [accepted[b] EXCEPT ![s] =
         [accepted[b][s] EXCEPT ![a] = TRUE]]]
    /\ UNCHANGED <<proposed, decided>>

Decide(s, b) ==
    /\ decided[s] = -1
    /\ proposed[b][s] # -1
    /\ LET cfg == ConfigForSlot(s) IN
       Cardinality({a \in Acceptors : accepted[b][s][a] /\ InConfig(a, cfg)}) * 2
         > MemberCount(cfg)
    /\ decided' = [decided EXCEPT ![s] = proposed[b][s]]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, accepted>>

Next ==
    \/ \E b \in Ballots, a \in Acceptors : Promise(b, a)
    \/ \E b \in Ballots, s \in Slots, v \in 0..(V+1) : Propose(b, s, v)
    \/ \E b \in Ballots, s \in Slots, a \in Acceptors : Accept(b, s, a)
    \/ \E s \in Slots, b \in Ballots : Decide(s, b)

Spec == Init /\ [][Next]_vars

(* Agreement *)
Agreement ==
    \A s \in Slots : \A b1 \in Ballots : \A b2 \in Ballots :
        LET cfg == ConfigForSlot(s) IN
        (Cardinality({a \in Acceptors : accepted[b1][s][a] /\ InConfig(a, cfg)}) * 2
           > MemberCount(cfg)
         /\ Cardinality({a \in Acceptors : accepted[b2][s][a] /\ InConfig(a, cfg)}) * 2
           > MemberCount(cfg))
        => proposed[b1][s] = proposed[b2][s]

(* Validity *)
Validity ==
    \A s \in Slots : decided[s] # -1 => (decided[s] >= 0 /\ decided[s] <= V + 1)

(* Decided consistency *)
DecidedConsistency ==
    \A s \in Slots : \A b1 \in Ballots : \A b2 \in Ballots :
        (decided[s] # -1 /\ proposed[b1][s] # -1 /\ proposed[b2][s] # -1
         /\ Cardinality({a \in Acceptors : accepted[b1][s][a]}) * 2 > N + 1
         /\ Cardinality({a \in Acceptors : accepted[b2][s][a]}) * 2 > N + 1)
        => proposed[b1][s] = proposed[b2][s]

=====================================================================
