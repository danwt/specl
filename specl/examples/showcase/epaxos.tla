---------------------------- MODULE epaxos -----------------------------
(* Faithful model of one EPaxos consensus instance with 3 replicas.

   Command leader: replica 0. Fast quorum: {0, 1}. Classic quorum: any 2 of 3.

   Models the full instance lifecycle: pre-accept, fast commit, accept
   propagation, recovery (with fast-path detection), and slow commit.
   The value being agreed on represents the dependency set for a command:
   0 = no dependencies, 1 = has dependencies.

   UseFix toggles the Sutra 2019 correction:
     UseFix=0: Recovery compares bal (inflated by prepares) - BUG, finds violation.
     UseFix=1: Recovery compares vbal (actual acceptance ballot) - FIX, passes.

   Run with TLC:
     java -jar tla2tools.jar -deadlock -config epaxos_bug.cfg epaxos
     java -jar tla2tools.jar -deadlock -config epaxos_fix.cfg epaxos *)

EXTENDS Integers

CONSTANTS MaxBal, NB, UseFix

VARIABLES status, bal, vbal, val, next_bal, initial_val

vars == <<status, bal, vbal, val, next_bal, initial_val>>

Replicas == 0..2

Init ==
    /\ status = [r \in Replicas |-> 0]
    /\ bal = [r \in Replicas |-> 0]
    /\ vbal = [r \in Replicas |-> 0]
    /\ val = [r \in Replicas |-> 0]
    /\ next_bal = 1
    /\ initial_val = 0

(* Command leader (r0) initiates pre-accept with value v. *)
LeaderPreAccept(v) ==
    /\ status[0] = 0
    /\ bal[0] = 0
    /\ status' = [status EXCEPT ![0] = 1]
    /\ val' = [val EXCEPT ![0] = v]
    /\ initial_val' = v
    /\ UNCHANGED <<bal, vbal, next_bal>>

(* Fast quorum member (r1) responds to pre-accept.
   May reply with different deps due to local conflicts. *)
FastQuorumPreAccept(v) ==
    /\ status[0] >= 1
    /\ status[1] = 0
    /\ bal[1] = 0
    /\ status' = [status EXCEPT ![1] = 1]
    /\ val' = [val EXCEPT ![1] = v]
    /\ UNCHANGED <<bal, vbal, next_bal, initial_val>>

(* Fast-path commit: fast quorum {0, 1} agrees at ballot 0. *)
FastCommit(r) ==
    /\ r <= 1
    /\ status[r] >= 1
    /\ status[r] # 3
    /\ bal[r] = 0
    /\ status[0] >= 1 /\ status[1] >= 1
    /\ val[0] = val[1]
    /\ bal[0] = 0 /\ bal[1] = 0
    /\ status' = [status EXCEPT ![r] = 3]
    /\ UNCHANGED <<bal, vbal, val, next_bal, initial_val>>

(* Process a Prepare from some recovery attempt.
   Inflates bal without changing vbal, status, or value. *)
ReceivePrepare(r) ==
    /\ next_bal <= MaxBal
    /\ next_bal > bal[r]
    /\ status[r] # 3
    /\ bal' = [bal EXCEPT ![r] = next_bal]
    /\ next_bal' = next_bal + 1
    /\ UNCHANGED <<status, vbal, val, initial_val>>

(* Recovery value decision logic.
   BUG/FIX: "both accepted" comparison uses bal (UseFix=0) or vbal (UseFix=1). *)
RecoveryVal(leader, other, pick) ==
    \* Committed: adopt
    IF status[other] = 3 THEN val[other]
    \* Both accepted: highest ballot wins
    ELSE IF status[leader] = 2 /\ status[other] = 2 THEN
        IF UseFix = 1 THEN
            IF vbal[leader] > vbal[other] THEN val[leader]
            ELSE IF vbal[other] > vbal[leader] THEN val[other]
            ELSE val[leader]
        ELSE
            IF bal[leader] > bal[other] THEN val[leader]
            ELSE IF bal[other] > bal[leader] THEN val[other]
            ELSE val[leader]
    \* One accepted: adopt
    ELSE IF status[other] = 2 THEN val[other]
    ELSE IF status[leader] = 2 THEN val[leader]
    \* Fast-path detection: if any pre-accept matches initial_val,
    \* the fast path might have committed - adopt conservatively.
    ELSE IF (status[leader] = 1 /\ val[leader] = initial_val)
            \/ (status[other] = 1 /\ val[other] = initial_val)
        THEN initial_val
    \* No fast-path evidence: pre-accept tie-breaking
    ELSE IF status[leader] = 1 /\ status[other] = 1 THEN
        IF val[leader] = val[other] THEN val[leader] ELSE pick
    ELSE IF status[leader] = 1 THEN val[leader]
    ELSE IF status[other] = 1 THEN val[other]
    ELSE pick

(* Recovery: leader collects state from quorum {leader, other} and decides. *)
Recovery(leader, other, pick) ==
    /\ leader # other
    /\ next_bal <= MaxBal
    /\ next_bal > bal[leader]
    /\ next_bal > bal[other]
    /\ status[leader] # 3
    /\ status[leader] >= 1 \/ status[other] >= 1
    /\ val' = [val EXCEPT ![leader] = RecoveryVal(leader, other, pick)]
    /\ status' = [status EXCEPT ![leader] = 2]
    /\ bal' = [bal EXCEPT ![leader] = next_bal, ![other] = next_bal]
    /\ vbal' = [vbal EXCEPT ![leader] = next_bal]
    /\ next_bal' = next_bal + 1
    /\ UNCHANGED initial_val

(* Phase 2: propagate accepted value to another replica. *)
Accept(src, dst) ==
    /\ src # dst
    /\ status[src] = 2
    /\ status[dst] # 3
    /\ vbal[src] = bal[src]
    /\ bal[src] >= bal[dst]
    /\ status' = [status EXCEPT ![dst] = 2]
    /\ bal' = [bal EXCEPT ![dst] = bal[src]]
    /\ vbal' = [vbal EXCEPT ![dst] = vbal[src]]
    /\ val' = [val EXCEPT ![dst] = val[src]]
    /\ UNCHANGED <<next_bal, initial_val>>

(* Slow-path commit: quorum of 2 accepted replicas agree. *)
SlowCommit(r) ==
    /\ status[r] = 2
    /\ vbal[r] = bal[r]
    /\ \E r2 \in Replicas :
        r2 # r /\ status[r2] >= 2 /\ vbal[r2] = vbal[r] /\ val[r2] = val[r]
    /\ status' = [status EXCEPT ![r] = 3]
    /\ UNCHANGED <<bal, vbal, val, next_bal, initial_val>>

Next ==
    \/ \E v \in 0..1 : LeaderPreAccept(v)
    \/ \E v \in 0..1 : FastQuorumPreAccept(v)
    \/ \E r \in Replicas : FastCommit(r)
    \/ \E r \in Replicas : ReceivePrepare(r)
    \/ \E leader \in Replicas : \E other \in Replicas : \E pick \in 0..1 :
        Recovery(leader, other, pick)
    \/ \E src \in Replicas : \E dst \in Replicas : Accept(src, dst)
    \/ \E r \in Replicas : SlowCommit(r)

Spec == Init /\ [][Next]_vars

Agreement ==
    \A r1 \in Replicas : \A r2 \in Replicas :
        (status[r1] = 3 /\ status[r2] = 3) => val[r1] = val[r2]

=====================================================================
