---------------------------- MODULE epaxos -----------------------------
(* Egalitarian Paxos (EPaxos) - core consensus with fast/slow paths
   From: Moraru, Andersen & Kaminsky (SOSP 2013)
   R+1 replicas (0..R), each owns instances in its column.
   MaxInst+1 instances per replica (0..MaxInst).
   All commands interfere (conservative). Crash-free. *)

EXTENDS Integers, FiniteSets

CONSTANTS R, MaxInst, Cmd

VARIABLES instCmd, instDeps, instSeq, instStatus,
          crtInst, preAcceptReplied, preAcceptAgreed, acceptReplied

vars == <<instCmd, instDeps, instSeq, instStatus,
          crtInst, preAcceptReplied, preAcceptAgreed, acceptReplied>>

Replicas == 0..R
Instances == 0..MaxInst
Commands == 0..Cmd

FastQuorum == (3 * (R + 1)) \div 4 + 1
SlowQuorum == (R + 1) \div 2 + 1

Init ==
    /\ instCmd = [o \in Replicas |-> [s \in Instances |-> -1]]
    /\ instDeps = [o \in Replicas |-> [s \in Instances |->
         [do2 \in Replicas |-> [ds \in Instances |-> FALSE]]]]
    /\ instSeq = [o \in Replicas |-> [s \in Instances |-> 0]]
    /\ instStatus = [o \in Replicas |-> [s \in Instances |-> 0]]
    /\ crtInst = [o \in Replicas |-> 0]
    /\ preAcceptReplied = [o \in Replicas |-> [s \in Instances |->
         [r \in Replicas |-> FALSE]]]
    /\ preAcceptAgreed = [o \in Replicas |-> [s \in Instances |->
         [r \in Replicas |-> FALSE]]]
    /\ acceptReplied = [o \in Replicas |-> [s \in Instances |->
         [r \in Replicas |-> FALSE]]]

Propose(leader, slot, cmd) ==
    /\ crtInst[leader] = slot
    /\ instStatus[leader][slot] = 0
       /\ instCmd' = [instCmd EXCEPT ![leader] = [instCmd[leader] EXCEPT ![slot] = cmd]]
       /\ instDeps' = [instDeps EXCEPT ![leader] = [instDeps[leader] EXCEPT ![slot] =
            [do2 \in Replicas |-> [ds \in Instances |->
              instStatus[do2][ds] # 0 /\ ~(do2 = leader /\ ds = slot)]]]]
       /\ instSeq' = [instSeq EXCEPT ![leader] = [instSeq[leader] EXCEPT ![slot] = 1]]
       /\ instStatus' = [instStatus EXCEPT ![leader] = [instStatus[leader] EXCEPT ![slot] = 1]]
       /\ crtInst' = [crtInst EXCEPT ![leader] = slot + 1]
       /\ preAcceptReplied' = [preAcceptReplied EXCEPT ![leader] =
            [preAcceptReplied[leader] EXCEPT ![slot] =
              [preAcceptReplied[leader][slot] EXCEPT ![leader] = TRUE]]]
       /\ preAcceptAgreed' = [preAcceptAgreed EXCEPT ![leader] =
            [preAcceptAgreed[leader] EXCEPT ![slot] =
              [preAcceptAgreed[leader][slot] EXCEPT ![leader] = TRUE]]]
       /\ UNCHANGED acceptReplied

PreAcceptReply(replica, owner, slot) ==
    /\ replica # owner
    /\ instStatus[owner][slot] = 1
    /\ ~preAcceptReplied[owner][slot][replica]
    /\ LET hasExtraDep == \E do2 \in Replicas : \E ds \in Instances :
            instStatus[do2][ds] # 0 /\ ~(do2 = owner /\ ds = slot)
            /\ ~instDeps[owner][slot][do2][ds]
       IN
       /\ preAcceptReplied' = [preAcceptReplied EXCEPT ![owner] =
            [preAcceptReplied[owner] EXCEPT ![slot] =
              [preAcceptReplied[owner][slot] EXCEPT ![replica] = TRUE]]]
       /\ preAcceptAgreed' = [preAcceptAgreed EXCEPT ![owner] =
            [preAcceptAgreed[owner] EXCEPT ![slot] =
              [preAcceptAgreed[owner][slot] EXCEPT ![replica] = ~hasExtraDep]]]
    /\ UNCHANGED <<instCmd, instDeps, instSeq, instStatus, crtInst, acceptReplied>>

FastPathCommit(owner, slot) ==
    /\ instStatus[owner][slot] = 1
    /\ Cardinality({r \in Replicas : preAcceptAgreed[owner][slot][r]}) >= FastQuorum
    /\ instStatus' = [instStatus EXCEPT ![owner] = [instStatus[owner] EXCEPT ![slot] = 3]]
    /\ UNCHANGED <<instCmd, instDeps, instSeq, crtInst,
                   preAcceptReplied, preAcceptAgreed, acceptReplied>>

StartSlowPath(owner, slot) ==
    /\ instStatus[owner][slot] = 1
    /\ Cardinality({r \in Replicas : preAcceptReplied[owner][slot][r]}) >= SlowQuorum
    /\ Cardinality({r \in Replicas : preAcceptAgreed[owner][slot][r]}) < FastQuorum
    /\ instDeps' = [instDeps EXCEPT ![owner] = [instDeps[owner] EXCEPT ![slot] =
         [do2 \in Replicas |-> [ds \in Instances |->
           instDeps[owner][slot][do2][ds]
           \/ (instStatus[do2][ds] # 0 /\ ~(do2 = owner /\ ds = slot))]]]]
    /\ instStatus' = [instStatus EXCEPT ![owner] = [instStatus[owner] EXCEPT ![slot] = 2]]
    /\ UNCHANGED <<instCmd, instSeq, crtInst,
                   preAcceptReplied, preAcceptAgreed, acceptReplied>>

AcceptReply(replica, owner, slot) ==
    /\ replica # owner
    /\ instStatus[owner][slot] = 2
    /\ ~acceptReplied[owner][slot][replica]
    /\ acceptReplied' = [acceptReplied EXCEPT ![owner] =
         [acceptReplied[owner] EXCEPT ![slot] =
           [acceptReplied[owner][slot] EXCEPT ![replica] = TRUE]]]
    /\ UNCHANGED <<instCmd, instDeps, instSeq, instStatus, crtInst,
                   preAcceptReplied, preAcceptAgreed>>

SlowPathCommit(owner, slot) ==
    /\ instStatus[owner][slot] = 2
    /\ Cardinality({r \in Replicas : acceptReplied[owner][slot][r]}) + 1 >= SlowQuorum
    /\ instStatus' = [instStatus EXCEPT ![owner] = [instStatus[owner] EXCEPT ![slot] = 3]]
    /\ UNCHANGED <<instCmd, instDeps, instSeq, crtInst,
                   preAcceptReplied, preAcceptAgreed, acceptReplied>>

Next ==
    \/ \E leader \in Replicas, slot \in Instances, cmd \in Commands : Propose(leader, slot, cmd)
    \/ \E replica \in Replicas, owner \in Replicas, slot \in Instances :
         PreAcceptReply(replica, owner, slot)
    \/ \E owner \in Replicas, slot \in Instances : FastPathCommit(owner, slot)
    \/ \E owner \in Replicas, slot \in Instances : StartSlowPath(owner, slot)
    \/ \E replica \in Replicas, owner \in Replicas, slot \in Instances :
         AcceptReply(replica, owner, slot)
    \/ \E owner \in Replicas, slot \in Instances : SlowPathCommit(owner, slot)

Spec == Init /\ [][Next]_vars

(* No committed instance has empty command *)
Nontriviality ==
    \A o \in Replicas : \A s \in Instances :
        instStatus[o][s] = 3 => instCmd[o][s] # -1

(* For any two committed instances, at least one is in the other's deps *)
CommittedVisibility ==
    \A o1 \in Replicas : \A s1 \in Instances : \A o2 \in Replicas : \A s2 \in Instances :
        (instStatus[o1][s1] = 3 /\ instStatus[o2][s2] = 3
         /\ ~(o1 = o2 /\ s1 = s2)
         /\ instCmd[o1][s1] # -1 /\ instCmd[o2][s2] # -1)
        => (instDeps[o1][s1][o2][s2] \/ instDeps[o2][s2][o1][s1])

=====================================================================
