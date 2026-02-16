--------------------------- MODULE simplex ---------------------------
(* Simplex consensus — crash-fault variant (single-shot consensus)
   From: Chan & Pass, "Simplex Consensus" (TCC 2023)
   N+1 players (0..N), f < (N+1)/2 may crash, no Byzantine behavior
   Leader of iteration h: h % (N + 1)
   Notarization: leader's proposal alone suffices (crash = no equivocation)
   Dummy blocks need >n/2 votes; Finalization needs >n/2 finalize messages *)

EXTENDS Integers, FiniteSets

CONSTANTS N, MaxIter, V

VARIABLES iter, proposed, dummyVote, finMsg, decided

vars == <<iter, proposed, dummyVote, finMsg, decided>>
Players == 0..N
Iters == 0..MaxIter
Values == 0..V

Init ==
    /\ iter = [i \in Players |-> 0]
    /\ proposed = [h \in Iters |-> -1]
    /\ dummyVote = [h \in Iters |-> [i \in Players |-> FALSE]]
    /\ finMsg = [h \in Iters |-> [i \in Players |-> FALSE]]
    /\ decided = [i \in Players |-> -1]

(* Leader of iteration h proposes value v.
   Chain-linking: must re-propose value from any earlier real block *)
LeaderPropose(h, v) ==
    /\ proposed[h] = -1
    /\ iter[h % (N + 1)] = h
    /\ \A h2 \in Iters : (h2 < h /\ proposed[h2] # -1) => v = proposed[h2]
    /\ proposed' = [proposed EXCEPT ![h] = v]
    /\ UNCHANGED <<iter, dummyVote, finMsg, decided>>

(* Player i votes for dummy block at iteration h (timeout) *)
VoteDummy(h, i) ==
    /\ iter[i] = h
    /\ dummyVote[h][i] = FALSE
    /\ dummyVote' = [dummyVote EXCEPT ![h] = [dummyVote[h] EXCEPT ![i] = TRUE]]
    /\ UNCHANGED <<iter, proposed, finMsg, decided>>

(* Player i advances to next iteration *)
AdvanceIter(i) ==
    /\ iter[i] < MaxIter
    /\ \/ proposed[iter[i]] # -1
       \/ Cardinality({j \in Players : dummyVote[iter[i]][j]}) * 2 > N + 1
    /\ iter' = [iter EXCEPT ![i] = iter[i] + 1]
    /\ UNCHANGED <<proposed, dummyVote, finMsg, decided>>

(* Player i sends finalize for iteration h *)
SendFinalize(h, i) ==
    /\ iter[i] > h
    /\ proposed[h] # -1
    /\ dummyVote[h][i] = FALSE
    /\ finMsg[h][i] = FALSE
    /\ finMsg' = [finMsg EXCEPT ![h] = [finMsg[h] EXCEPT ![i] = TRUE]]
    /\ UNCHANGED <<iter, proposed, dummyVote, decided>>

(* Player i decides upon seeing >n/2 finalize messages for iteration h *)
Decide(i, h) ==
    /\ decided[i] = -1
    /\ proposed[h] # -1
    /\ Cardinality({j \in Players : finMsg[h][j]}) * 2 > N + 1
    /\ decided' = [decided EXCEPT ![i] = proposed[h]]
    /\ UNCHANGED <<iter, proposed, dummyVote, finMsg>>

Next ==
    \/ \E h \in Iters, v \in Values : LeaderPropose(h, v)
    \/ \E h \in Iters, i \in Players : VoteDummy(h, i)
    \/ \E i \in Players : AdvanceIter(i)
    \/ \E h \in Iters, i \in Players : SendFinalize(h, i)
    \/ \E i \in Players, h \in Iters : Decide(i, h)

Spec == Init /\ [][Next]_vars

(* Finalization safety: trivially true by pigeonhole, kept as documentation *)
FinalizationSafety ==
    \A h \in Iters :
        Cardinality({i \in Players : finMsg[h][i]}) * 2 > N + 1
        => Cardinality({j \in Players : dummyVote[h][j]}) * 2 <= N + 1

(* Agreement: no two players decide different values *)
Agreement ==
    \A i \in Players : \A j \in Players :
        (decided[i] # -1 /\ decided[j] # -1)
        => decided[i] = decided[j]

=====================================================================
