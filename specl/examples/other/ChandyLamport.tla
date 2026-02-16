------------------------ MODULE ChandyLamport ------------------------
(* Chandy-Lamport consistent snapshot algorithm
   From: Chandy & Lamport, "Distributed Snapshots: Determining Global
         States of Distributed Systems" (1985)
   Underlying computation: token passing ring (single token circulates)
   N+1 processes in a ring (0..N), MaxMsgs bounds channel capacity
   Message types: 0=Token, 1=Marker *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, MaxMsgs

VARIABLES channel, hasToken, snapState, recorded,
          channelRecording, channelRecord, initiated

vars == <<channel, hasToken, snapState, recorded,
          channelRecording, channelRecord, initiated>>

Procs == 0..N

Pred(i) == (i + N) % (N + 1)
Succ(i) == (i + 1) % (N + 1)

Init ==
    /\ channel = [i \in Procs |-> <<>>]
    /\ hasToken = [i \in Procs |-> i = 0]
    /\ snapState = [i \in Procs |-> 0]
    /\ recorded = [i \in Procs |-> -1]
    /\ channelRecording = [i \in Procs |-> FALSE]
    /\ channelRecord = [i \in Procs |-> <<>>]
    /\ initiated = FALSE

(* Process i sends token to successor *)
SendToken(i) ==
    /\ hasToken[i]
    /\ Len(channel[i]) < MaxMsgs
    /\ hasToken' = [hasToken EXCEPT ![i] = FALSE]
    /\ channel' = [channel EXCEPT ![i] = Append(channel[i], 0)]
    /\ UNCHANGED <<snapState, recorded, channelRecording, channelRecord, initiated>>

(* Process i receives token from predecessor *)
ReceiveToken(i) ==
    /\ Len(channel[Pred(i)]) > 0
    /\ Head(channel[Pred(i)]) = 0
    /\ channel' = [channel EXCEPT ![Pred(i)] = Tail(channel[Pred(i)])]
    /\ hasToken' = [hasToken EXCEPT ![i] = TRUE]
    /\ channelRecord' = [channelRecord EXCEPT ![i] =
        IF channelRecording[i] THEN Append(channelRecord[i], 0)
        ELSE channelRecord[i]]
    /\ UNCHANGED <<snapState, recorded, channelRecording, initiated>>

(* Process 0 initiates the snapshot *)
InitiateSnapshot ==
    /\ ~initiated
    /\ snapState[0] = 0
    /\ Len(channel[0]) < MaxMsgs
    /\ initiated' = TRUE
    /\ snapState' = [snapState EXCEPT ![0] = 1]
    /\ recorded' = [recorded EXCEPT ![0] = IF hasToken[0] THEN 1 ELSE 0]
    /\ channel' = [channel EXCEPT ![0] = Append(channel[0], 1)]
    /\ channelRecording' = [channelRecording EXCEPT ![0] = TRUE]
    /\ UNCHANGED <<hasToken, channelRecord>>

(* Non-initiator process i receives first marker *)
ReceiveMarker(i) ==
    /\ i # 0
    /\ Len(channel[Pred(i)]) > 0
    /\ Head(channel[Pred(i)]) = 1
    /\ snapState[i] = 0
    /\ Len(channel[i]) < MaxMsgs
    /\ channel' = [channel EXCEPT ![Pred(i)] = Tail(channel[Pred(i)]),
                                   ![i] = Append(channel[i], 1)]
    /\ snapState' = [snapState EXCEPT ![i] = 2]
    /\ recorded' = [recorded EXCEPT ![i] = IF hasToken[i] THEN 1 ELSE 0]
    /\ UNCHANGED <<hasToken, channelRecording, channelRecord, initiated>>

(* Initiator (process 0) receives marker back *)
InitiatorComplete ==
    /\ snapState[0] = 1
    /\ Len(channel[Pred(0)]) > 0
    /\ Head(channel[Pred(0)]) = 1
    /\ channel' = [channel EXCEPT ![Pred(0)] = Tail(channel[Pred(0)])]
    /\ snapState' = [snapState EXCEPT ![0] = 2]
    /\ channelRecording' = [channelRecording EXCEPT ![0] = FALSE]
    /\ UNCHANGED <<hasToken, recorded, channelRecord, initiated>>

Next ==
    \/ \E i \in Procs : SendToken(i)
    \/ \E i \in Procs : ReceiveToken(i)
    \/ InitiateSnapshot
    \/ \E i \in Procs : ReceiveMarker(i)
    \/ InitiatorComplete

Spec == Init /\ [][Next]_vars

(* Snapshot token count *)
SnapshotTokenCount ==
    Cardinality({i \in Procs : recorded[i] = 1})
    + Cardinality({i \in Procs : Len(channelRecord[i]) > 0})

(* Consistent snapshot: when all done, exactly 1 token *)
ConsistentSnapshot ==
    (\A i \in Procs : snapState[i] = 2) => SnapshotTokenCount = 1

(* No phantom messages: channel records only contain token messages *)
NoPhantomMessages ==
    \A i \in Procs : \A k \in 1..MaxMsgs :
        (k <= Len(channelRecord[i])) => channelRecord[i][k] = 0

=====================================================================
