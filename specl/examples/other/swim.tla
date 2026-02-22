---------------------------- MODULE swim ----------------------------
(* SWIM failure detection protocol
   From: Das, Gupta, Sturgis, "SWIM: Scalable Weakly-consistent
         Infection-style Membership Protocol" (2002)
   N+1 nodes (0..N), K indirect ping helpers per probe
   MaxRound bounds protocol rounds *)

EXTENDS Integers, FiniteSets

CONSTANTS N, K, MaxRound

VARIABLES alive, view, round, prober, target,
          directResult, indirectResult, helpersAsked, askedHelper

vars == <<alive, view, round, prober, target,
          directResult, indirectResult, helpersAsked, askedHelper>>

Nodes == 0..N
Rounds == 0..MaxRound

Init ==
    /\ alive = [i \in Nodes |-> TRUE]
    /\ view = [i \in Nodes |-> [j \in Nodes |-> 0]]
    /\ round = 0
    /\ prober = [r \in Rounds |-> -1]
    /\ target = [r \in Rounds |-> -1]
    /\ directResult = [r \in Rounds |-> 0]
    /\ indirectResult = [r \in Rounds |-> 0]
    /\ helpersAsked = [r \in Rounds |-> 0]
    /\ askedHelper = [r \in Rounds |-> [i \in Nodes |-> FALSE]]

(* Node i crashes (node 0 never crashes) *)
Crash(i) ==
    /\ alive[i]
    /\ i # 0
    /\ alive' = [alive EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<view, round, prober, target,
                   directResult, indirectResult, helpersAsked, askedHelper>>

(* Alive node i starts probing node j in the current round *)
StartProbe(i, j) ==
    /\ round <= MaxRound
    /\ prober[round] = -1
    /\ i # j
    /\ alive[i]
    /\ view[i][j] # 2
    /\ prober' = [prober EXCEPT ![round] = i]
    /\ target' = [target EXCEPT ![round] = j]
    /\ UNCHANGED <<alive, view, round,
                   directResult, indirectResult, helpersAsked, askedHelper>>

(* Direct ping succeeds (target is alive and reachable) *)
DirectAck ==
    /\ prober[round] # -1
    /\ directResult[round] = 0
    /\ alive[target[round]]
    /\ directResult' = [directResult EXCEPT ![round] = 1]
    /\ UNCHANGED <<alive, view, round, prober, target,
                   indirectResult, helpersAsked, askedHelper>>

(* Direct ping times out (non-deterministic) *)
DirectTimeout ==
    /\ prober[round] # -1
    /\ directResult[round] = 0
    /\ directResult' = [directResult EXCEPT ![round] = 2]
    /\ UNCHANGED <<alive, view, round, prober, target,
                   indirectResult, helpersAsked, askedHelper>>

(* Ask helper h to probe the target *)
IndirectPing(h) ==
    /\ directResult[round] = 2
    /\ indirectResult[round] = 0
    /\ helpersAsked[round] < K
    /\ h # prober[round]
    /\ h # target[round]
    /\ alive[h]
    /\ ~askedHelper[round][h]
    /\ helpersAsked' = [helpersAsked EXCEPT ![round] = helpersAsked[round] + 1]
    /\ askedHelper' = [askedHelper EXCEPT ![round] = [askedHelper[round] EXCEPT ![h] = TRUE]]
    /\ UNCHANGED <<alive, view, round, prober, target,
                   directResult, indirectResult>>

(* Indirect ping succeeds *)
IndirectAck ==
    /\ directResult[round] = 2
    /\ indirectResult[round] = 0
    /\ helpersAsked[round] > 0
    /\ alive[target[round]]
    /\ indirectResult' = [indirectResult EXCEPT ![round] = 1]
    /\ UNCHANGED <<alive, view, round, prober, target,
                   directResult, helpersAsked, askedHelper>>

(* Indirect ping times out *)
IndirectTimeout ==
    /\ directResult[round] = 2
    /\ indirectResult[round] = 0
    /\ helpersAsked[round] >= K
    /\ indirectResult' = [indirectResult EXCEPT ![round] = 2]
    /\ UNCHANGED <<alive, view, round, prober, target,
                   directResult, helpersAsked, askedHelper>>

(* Prober marks target as suspected *)
Suspect ==
    /\ directResult[round] = 2
    /\ indirectResult[round] = 2
    /\ view[prober[round]][target[round]] = 0
    /\ view' = [view EXCEPT ![prober[round]] = [view[prober[round]] EXCEPT ![target[round]] = 1]]
    /\ UNCHANGED <<alive, round, prober, target,
                   directResult, indirectResult, helpersAsked, askedHelper>>

(* Prober confirms target is alive *)
ConfirmAlive ==
    /\ \/ directResult[round] = 1
       \/ indirectResult[round] = 1
    /\ view[prober[round]][target[round]] # 2
    /\ view' = [view EXCEPT ![prober[round]] = [view[prober[round]] EXCEPT ![target[round]] = 0]]
    /\ UNCHANGED <<alive, round, prober, target,
                   directResult, indirectResult, helpersAsked, askedHelper>>

(* Suspected node promoted to Failed *)
DeclareFailed(i, j) ==
    /\ i # j
    /\ alive[i]
    /\ view[i][j] = 1
    /\ view' = [view EXCEPT ![i] = [view[i] EXCEPT ![j] = 2]]
    /\ UNCHANGED <<alive, round, prober, target,
                   directResult, indirectResult, helpersAsked, askedHelper>>

(* Advance to next round *)
AdvanceRound ==
    /\ round < MaxRound
    /\ prober[round] # -1
    /\ directResult[round] # 0
    /\ directResult[round] = 1 \/ indirectResult[round] # 0
    /\ round' = round + 1
    /\ UNCHANGED <<alive, view, prober, target,
                   directResult, indirectResult, helpersAsked, askedHelper>>

(* Node i learns from node j about node k's higher suspicion status *)
Gossip(i, j, k) ==
    /\ alive[i] /\ alive[j]
    /\ i # j
    /\ i # k
    /\ view[j][k] > view[i][k]
    /\ view' = [view EXCEPT ![i] = [view[i] EXCEPT ![k] = view[j][k]]]
    /\ UNCHANGED <<alive, round, prober, target,
                   directResult, indirectResult, helpersAsked, askedHelper>>

Next ==
    \/ \E i \in Nodes : Crash(i)
    \/ \E i \in Nodes, j \in Nodes : StartProbe(i, j)
    \/ DirectAck
    \/ DirectTimeout
    \/ \E h \in Nodes : IndirectPing(h)
    \/ IndirectAck
    \/ IndirectTimeout
    \/ Suspect
    \/ ConfirmAlive
    \/ \E i \in Nodes, j \in Nodes : DeclareFailed(i, j)
    \/ AdvanceRound
    \/ \E i \in Nodes, j \in Nodes, k \in Nodes : Gossip(i, j, k)

Spec == Init /\ [][Next]_vars

(* No self-suspicion: a live node never marks itself as suspected or failed *)
NoSelfSuspicion ==
    \A i \in Nodes : alive[i] => view[i][i] = 0

(* Strong accuracy: alive nodes are never marked Failed by any alive node *)
(* This MAY be violated due to non-deterministic DirectTimeout *)
AccuracySafety ==
    \A i \in Nodes : \A j \in Nodes :
        (alive[i] /\ alive[j]) => view[i][j] # 2

(* Bounded completeness *)
BoundedCompleteness ==
    (round = MaxRound /\ prober[MaxRound] # -1)
    => (\A i \in Nodes : \A j \in Nodes :
            (alive[i] /\ ~alive[j]) => view[i][j] >= 1)

=====================================================================
