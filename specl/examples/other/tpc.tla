---------------------------- MODULE tpc ----------------------------
(* Two-Phase Commit with coordinator crash
   From: Gray & Lamport, "Consensus on Transaction Commit" (2006)
   N+1 resource managers (0..N) *)

EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES rmState, tmState, tmPrepared, tmCrashed

vars == <<rmState, tmState, tmPrepared, tmCrashed>>
RMs == 0..N

Init ==
    /\ rmState = [r \in RMs |-> 0]
    /\ tmState = 0
    /\ tmPrepared = {}
    /\ tmCrashed = FALSE

(* RM r votes YES by moving to Prepared *)
RMPrepare(r) ==
    /\ rmState[r] = 0
    /\ rmState' = [rmState EXCEPT ![r] = 1]
    /\ UNCHANGED <<tmState, tmPrepared, tmCrashed>>

(* RM r unilaterally aborts (only from Working state) *)
RMChooseToAbort(r) ==
    /\ rmState[r] = 0
    /\ rmState' = [rmState EXCEPT ![r] = 3]
    /\ UNCHANGED <<tmState, tmPrepared, tmCrashed>>

(* TM receives prepared message from RM r *)
TMRcvPrepared(r) ==
    /\ ~tmCrashed
    /\ tmState = 0
    /\ rmState[r] = 1
    /\ tmPrepared' = tmPrepared \union {r}
    /\ UNCHANGED <<rmState, tmState, tmCrashed>>

(* TM commits: all RMs have prepared *)
TMCommit ==
    /\ ~tmCrashed
    /\ tmState = 0
    /\ \A r \in RMs : r \in tmPrepared
    /\ tmState' = 1
    /\ UNCHANGED <<rmState, tmPrepared, tmCrashed>>

(* TM aborts *)
TMAbort ==
    /\ ~tmCrashed
    /\ tmState = 0
    /\ tmState' = 2
    /\ UNCHANGED <<rmState, tmPrepared, tmCrashed>>

(* RM r learns the commit decision *)
RMRcvCommit(r) ==
    /\ tmState = 1
    /\ rmState' = [rmState EXCEPT ![r] = 2]
    /\ UNCHANGED <<tmState, tmPrepared, tmCrashed>>

(* RM r learns the abort decision *)
RMRcvAbort(r) ==
    /\ tmState = 2
    /\ rmState' = [rmState EXCEPT ![r] = 3]
    /\ UNCHANGED <<tmState, tmPrepared, tmCrashed>>

(* Coordinator crashes (can happen while TM is in Init) *)
CoordinatorCrash ==
    /\ ~tmCrashed
    /\ tmState = 0
    /\ tmCrashed' = TRUE
    /\ UNCHANGED <<rmState, tmState, tmPrepared>>

Next ==
    \/ \E r \in RMs : RMPrepare(r)
    \/ \E r \in RMs : RMChooseToAbort(r)
    \/ \E r \in RMs : TMRcvPrepared(r)
    \/ TMCommit
    \/ TMAbort
    \/ \E r \in RMs : RMRcvCommit(r)
    \/ \E r \in RMs : RMRcvAbort(r)
    \/ CoordinatorCrash

Spec == Init /\ [][Next]_vars

(* Agreement: no RM committed while another aborted *)
Agreement ==
    \A i \in RMs : \A j \in RMs :
        ~(rmState[i] = 2 /\ rmState[j] = 3)

(* Validity: if TM committed, all RMs were prepared (not still working) *)
CommitValidity ==
    tmState = 1 => \A r \in RMs : rmState[r] # 0

(* Consistency: if TM aborted, no RM committed *)
AbortConsistency ==
    tmState = 2 => \A r \in RMs : rmState[r] # 2

=====================================================================
