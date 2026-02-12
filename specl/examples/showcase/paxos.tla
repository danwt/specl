---------------------------- MODULE paxos ----------------------------
(* Single-decree Paxos (Synod protocol)
   From: Lamport, "The Part-Time Parliament" / "Paxos Made Simple"
   Safety formulation based on Lamport's Voting/Paxos TLA+ specs
   N+1 acceptors (0..N), ballots 0..MaxBallot, values 0..V *)

EXTENDS Integers, FiniteSets

CONSTANTS N, MaxBallot, V

VARIABLES maxBal, maxVBal, maxVal, proposed, accepted

vars == <<maxBal, maxVBal, maxVal, proposed, accepted>>
Acceptors == 0..N
Ballots == 0..MaxBallot
Values == 0..V

(* A value v is safe to propose at ballot b *)
SafeAt(b, v) ==
    \E Q \in SUBSET Acceptors :
        /\ Cardinality(Q) * 2 > N + 1
        /\ \A a \in Q : maxBal[a] >= b
        /\ \/ \A a \in Q : maxVBal[a] = -1
           \/ \E c \in Ballots :
                /\ c < b
                /\ \A a \in Q : maxVBal[a] <= c
                /\ \E a \in Q : maxVBal[a] = c /\ maxVal[a] = v

Init ==
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> -1]
    /\ proposed = [b \in Ballots |-> -1]
    /\ accepted = [b \in Ballots |-> [a \in Acceptors |-> FALSE]]

(* Acceptor a promises ballot b *)
Promise(b, a) ==
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED <<maxVBal, maxVal, proposed, accepted>>

(* Proposer proposes value v for ballot b *)
Propose(b, v) ==
    /\ proposed[b] = -1
    /\ SafeAt(b, v)
    /\ proposed' = [proposed EXCEPT ![b] = v]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, accepted>>

(* Acceptor a votes for the proposed value in ballot b *)
Accept(b, a) ==
    /\ proposed[b] # -1
    /\ maxBal[a] <= b
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal' = [maxVal EXCEPT ![a] = proposed[b]]
    /\ accepted' = [accepted EXCEPT ![b] = [accepted[b] EXCEPT ![a] = TRUE]]
    /\ UNCHANGED proposed

Next ==
    \/ \E b \in Ballots, a \in Acceptors : Promise(b, a)
    \/ \E b \in Ballots, v \in Values : Propose(b, v)
    \/ \E b \in Ballots, a \in Acceptors : Accept(b, a)

Spec == Init /\ [][Next]_vars

(* Agreement: any two majority-accepted ballots have the same value *)
Agreement ==
    \A b1 \in Ballots : \A b2 \in Ballots :
        (Cardinality({a \in Acceptors : accepted[b1][a]}) * 2 > N + 1
         /\ Cardinality({a \in Acceptors : accepted[b2][a]}) * 2 > N + 1)
        => proposed[b1] = proposed[b2]

(* Validity: any proposed value is in the valid range *)
Validity ==
    \A b \in Ballots : proposed[b] # -1 => (proposed[b] >= 0 /\ proposed[b] <= V)

=====================================================================
