---------------------------- MODULE pbft -----------------------------
(* Practical Byzantine Fault Tolerance - normal case + view change
   From: Castro & Liskov, "Practical Byzantine Fault Tolerance" (OSDI 1999)
   N+1 replicas (0..N), F Byzantine faults, N+1 >= 3F+1
   Simplified: bounded views/seqs, crash-only faults *)

EXTENDS Integers, FiniteSets

CONSTANTS N, F, MaxView, MaxSeq, V

VARIABLES view, status, prePrepared, prepared, committed,
          executed, crashed, vcSent, nvSent

vars == <<view, status, prePrepared, prepared, committed,
          executed, crashed, vcSent, nvSent>>

Replicas == 0..N
Views == 0..MaxView
Seqs == 0..MaxSeq
Values == 0..V

Primary(v) == v % (N + 1)

PrepareCount(v, seq, val) ==
    Cardinality({r \in Replicas : prepared[v][seq][r] /\ prePrepared[v][seq] = val})

CommitCount(v, seq, val) ==
    Cardinality({r \in Replicas : committed[v][seq][r] /\ prePrepared[v][seq] = val})

VCCount(v) ==
    Cardinality({r \in Replicas : vcSent[v][r]})

Init ==
    /\ view = [r \in Replicas |-> 0]
    /\ status = [r \in Replicas |-> 0]
    /\ prePrepared = [v \in Views |-> [s \in Seqs |-> -1]]
    /\ prepared = [v \in Views |-> [s \in Seqs |-> [r \in Replicas |-> FALSE]]]
    /\ committed = [v \in Views |-> [s \in Seqs |-> [r \in Replicas |-> FALSE]]]
    /\ executed = [r \in Replicas |-> [s \in Seqs |-> -1]]
    /\ crashed = [r \in Replicas |-> FALSE]
    /\ vcSent = [v \in Views |-> [r \in Replicas |-> FALSE]]
    /\ nvSent = [v \in Views |-> FALSE]

Crash(r) ==
    /\ ~crashed[r]
    /\ Cardinality({i \in Replicas : crashed[i]}) < F
    /\ crashed' = [crashed EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<view, status, prePrepared, prepared, committed, executed, vcSent, nvSent>>

PrePrepare(v, seq, val) ==
    /\ ~crashed[Primary(v)]
    /\ view[Primary(v)] = v
    /\ status[Primary(v)] = 0
    /\ prePrepared[v][seq] = -1
    /\ prePrepared' = [prePrepared EXCEPT ![v] = [prePrepared[v] EXCEPT ![seq] = val]]
    /\ UNCHANGED <<view, status, prepared, committed, executed, crashed, vcSent, nvSent>>

SendPrepare(r, v, seq) ==
    /\ ~crashed[r]
    /\ r # Primary(v)
    /\ view[r] = v
    /\ status[r] = 0
    /\ prePrepared[v][seq] # -1
    /\ ~prepared[v][seq][r]
    /\ prepared' = [prepared EXCEPT ![v] = [prepared[v] EXCEPT ![seq] = [prepared[v][seq] EXCEPT ![r] = TRUE]]]
    /\ UNCHANGED <<view, status, prePrepared, committed, executed, crashed, vcSent, nvSent>>

PrimaryPrepare(v, seq) ==
    /\ ~crashed[Primary(v)]
    /\ view[Primary(v)] = v
    /\ status[Primary(v)] = 0
    /\ prePrepared[v][seq] # -1
    /\ ~prepared[v][seq][Primary(v)]
    /\ prepared' = [prepared EXCEPT ![v] = [prepared[v] EXCEPT ![seq] = [prepared[v][seq] EXCEPT ![Primary(v)] = TRUE]]]
    /\ UNCHANGED <<view, status, prePrepared, committed, executed, crashed, vcSent, nvSent>>

SendCommit(r, v, seq) ==
    /\ ~crashed[r]
    /\ view[r] = v
    /\ status[r] = 0
    /\ prePrepared[v][seq] # -1
    /\ PrepareCount(v, seq, prePrepared[v][seq]) >= 2 * F
    /\ ~committed[v][seq][r]
    /\ committed' = [committed EXCEPT ![v] = [committed[v] EXCEPT ![seq] = [committed[v][seq] EXCEPT ![r] = TRUE]]]
    /\ UNCHANGED <<view, status, prePrepared, prepared, executed, crashed, vcSent, nvSent>>

Execute(r, v, seq) ==
    /\ ~crashed[r]
    /\ executed[r][seq] = -1
    /\ prePrepared[v][seq] # -1
    /\ CommitCount(v, seq, prePrepared[v][seq]) >= 2 * F + 1
    /\ executed' = [executed EXCEPT ![r] = [executed[r] EXCEPT ![seq] = prePrepared[v][seq]]]
    /\ UNCHANGED <<view, status, prePrepared, prepared, committed, crashed, vcSent, nvSent>>

StartViewChange(r, v) ==
    /\ ~crashed[r]
    /\ view[r] = v
    /\ v < MaxView
    /\ ~vcSent[v + 1][r]
    /\ status' = [status EXCEPT ![r] = 1]
    /\ vcSent' = [vcSent EXCEPT ![v + 1] = [vcSent[v + 1] EXCEPT ![r] = TRUE]]
    /\ UNCHANGED <<view, prePrepared, prepared, committed, executed, crashed, nvSent>>

SendNewView(v) ==
    /\ v > 0
    /\ ~nvSent[v]
    /\ ~crashed[Primary(v)]
    /\ VCCount(v) >= 2 * F + 1
    /\ nvSent' = [nvSent EXCEPT ![v] = TRUE]
    /\ UNCHANGED <<view, status, prePrepared, prepared, committed, executed, crashed, vcSent>>

EnterNewView(r, v) ==
    /\ ~crashed[r]
    /\ v > 0
    /\ nvSent[v]
    /\ view[r] < v
    /\ view' = [view EXCEPT ![r] = v]
    /\ status' = [status EXCEPT ![r] = 0]
    /\ UNCHANGED <<prePrepared, prepared, committed, executed, crashed, vcSent, nvSent>>

Next ==
    \/ \E r \in Replicas : Crash(r)
    \/ \E v \in Views, seq \in Seqs, val \in Values : PrePrepare(v, seq, val)
    \/ \E r \in Replicas, v \in Views, seq \in Seqs : SendPrepare(r, v, seq)
    \/ \E v \in Views, seq \in Seqs : PrimaryPrepare(v, seq)
    \/ \E r \in Replicas, v \in Views, seq \in Seqs : SendCommit(r, v, seq)
    \/ \E r \in Replicas, v \in Views, seq \in Seqs : Execute(r, v, seq)
    \/ \E r \in Replicas, v \in Views : StartViewChange(r, v)
    \/ \E v \in Views : SendNewView(v)
    \/ \E r \in Replicas, v \in Views : EnterNewView(r, v)

Spec == Init /\ [][Next]_vars

(* Agreement: no two non-crashed replicas execute different values for same seq *)
Agreement ==
    \A r1 \in Replicas : \A r2 \in Replicas : \A s \in Seqs :
        (~crashed[r1] /\ ~crashed[r2]
         /\ executed[r1][s] # -1 /\ executed[r2][s] # -1)
        => executed[r1][s] = executed[r2][s]

(* Validity: executed values are in valid range *)
Validity ==
    \A r \in Replicas : \A s \in Seqs :
        executed[r][s] # -1 => (executed[r][s] >= 0 /\ executed[r][s] <= V)

=====================================================================
