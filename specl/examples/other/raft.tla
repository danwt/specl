---------------------------- MODULE raft -----------------------------
(* Raft consensus algorithm - leader election and log replication
   From: Ongaro & Ousterhout, "In Search of an Understandable Consensus Algorithm"
   N+1 servers (0..N) *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, MaxTerm, MaxLogLen

VARIABLES currentTerm, role, votedFor, votesGranted, log, commitIndex

vars == <<currentTerm, role, votedFor, votesGranted, log, commitIndex>>
Servers == 0..N

(* Role encoding: 0=Follower, 1=Candidate, 2=Leader *)

LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)]

Min(a, b) == IF a <= b THEN a ELSE b

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ role = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> -1]
    /\ votesGranted = [s \in Servers |-> [t \in Servers |-> FALSE]]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]

(* Server i starts an election *)
Timeout(i) ==
    /\ role[i] # 2
    /\ currentTerm[i] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ role' = [role EXCEPT ![i] = 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = [t \in Servers |-> t = i]]
    /\ UNCHANGED <<log, commitIndex>>

(* Candidate i gets vote from server j (atomic RPC) *)
RequestVote(i, j) ==
    /\ i # j
    /\ role[i] = 1
    /\ currentTerm[i] >= currentTerm[j]
    /\ currentTerm[j] < currentTerm[i] \/ votedFor[j] = -1 \/ votedFor[j] = i
    \* Election restriction (section 5.4.1)
    /\ \/ LastLogTerm(log[i]) > LastLogTerm(log[j])
       \/ LastLogTerm(log[i]) = LastLogTerm(log[j]) /\ Len(log[i]) >= Len(log[j])
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ role' = [role EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN 0 ELSE role[j]]
    /\ votedFor' = [votedFor EXCEPT ![j] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = [votesGranted[i] EXCEPT ![j] = TRUE]]
    /\ UNCHANGED <<log, commitIndex>>

(* Candidate i becomes leader with majority votes.
   Uses persistent votesGranted rather than global votedFor state,
   so votes aren't lost when voters advance to higher terms via UpdateTerm *)
BecomeLeader(i) ==
    /\ role[i] = 1
    /\ Cardinality({k \in Servers : votesGranted[i][k]}) * 2 > N + 1
    /\ role' = [role EXCEPT ![i] = 2]
    /\ UNCHANGED <<currentTerm, votedFor, votesGranted, log, commitIndex>>

(* Leader i appends client entry to own log *)
ClientRequest(i) ==
    /\ role[i] = 2
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, role, votedFor, votesGranted, commitIndex>>

(* Leader i replicates one entry to follower j.
   Also propagates leaderCommit: follower advances commitIndex to
   min(leaderCommit, new log length), matching Raft section 5.3 *)
AppendEntries(i, j) ==
    /\ i # j
    /\ role[i] = 2
    /\ currentTerm[i] >= currentTerm[j]
    /\ Len(log[j]) < Len(log[i])
    \* Prefix consistency: j's log matches i's log up to j's length
    /\ IF Len(log[j]) = 0 THEN TRUE
       ELSE log[j][Len(log[j])] = log[i][Len(log[j])]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ role' = [role EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN 0 ELSE role[j]]
    /\ votedFor' = [votedFor EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN -1 ELSE votedFor[j]]
    /\ log' = [log EXCEPT ![j] = Append(log[j], log[i][Len(log[j]) + 1])]
    /\ commitIndex' = [commitIndex EXCEPT ![j] =
        IF commitIndex[i] <= commitIndex[j] THEN commitIndex[j]
        ELSE Min(commitIndex[i], Len(log[j]) + 1)]
    /\ UNCHANGED <<votesGranted>>

(* Follower i rolls back last log entry when it conflicts with leader j *)
RollbackLog(i, j) ==
    /\ i # j
    /\ role[j] = 2
    /\ currentTerm[j] >= currentTerm[i]
    /\ Len(log[i]) > 0
    \* Follower's log is NOT a prefix of leader's: either longer or mismatched
    /\ IF Len(log[i]) > Len(log[j]) THEN TRUE
       ELSE log[i][Len(log[i])] # log[j][Len(log[i])]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ role' = [role EXCEPT ![i] = IF currentTerm[i] < currentTerm[j] THEN 0 ELSE role[i]]
    /\ votedFor' = [votedFor EXCEPT ![i] = IF currentTerm[i] < currentTerm[j] THEN -1 ELSE votedFor[i]]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i]) - 1)]
    /\ UNCHANGED <<votesGranted, commitIndex>>

(* Leader i advances commit index to k.
   Note: majority check reads global log state (over-approximation vs real matchIndex).
   This is safe for model checking — explores more states than the real system. *)
AdvanceCommitIndex(i, k) ==
    /\ role[i] = 2
    /\ k > 0
    /\ k > commitIndex[i]
    /\ k <= Len(log[i])
    \* Only commit entries from current term (section 5.4.2)
    /\ log[i][k] = currentTerm[i]
    \* Majority have matching entry at position k
    /\ Cardinality({j \in Servers : Len(log[j]) >= k /\ log[j][k] = log[i][k]}) * 2 > N + 1
    /\ commitIndex' = [commitIndex EXCEPT ![i] = k]
    /\ UNCHANGED <<currentTerm, role, votedFor, votesGranted, log>>

(* Server i discovers server j has a higher term, steps down *)
UpdateTerm(i, j) ==
    /\ i # j
    /\ currentTerm[j] > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ role' = [role EXCEPT ![i] = 0]
    /\ votedFor' = [votedFor EXCEPT ![i] = -1]
    /\ UNCHANGED <<votesGranted, log, commitIndex>>

Next ==
    \/ \E i \in Servers : Timeout(i)
    \/ \E i \in Servers, j \in Servers : RequestVote(i, j)
    \/ \E i \in Servers : BecomeLeader(i)
    \/ \E i \in Servers : ClientRequest(i)
    \/ \E i \in Servers, j \in Servers : AppendEntries(i, j)
    \/ \E i \in Servers, j \in Servers : RollbackLog(i, j)
    \/ \E i \in Servers, k \in 0..MaxLogLen : AdvanceCommitIndex(i, k)
    \/ \E i \in Servers, j \in Servers : UpdateTerm(i, j)

Spec == Init /\ [][Next]_vars

(* Election safety: at most one leader per term *)
ElectionSafety ==
    \A i \in Servers : \A j \in Servers :
        (role[i] = 2 /\ role[j] = 2 /\ currentTerm[i] = currentTerm[j])
        => i = j

(* Log matching: if two servers have the same term at the same index,
   all preceding entries must also match *)
LogMatching ==
    \A i \in Servers : \A j \in Servers : \A k \in 0..MaxLogLen :
        (k < Len(log[i]) /\ k < Len(log[j]) /\ log[i][k+1] = log[j][k+1])
        => (IF k = 0 THEN TRUE ELSE log[i][k] = log[j][k])

(* Commit safety: if two servers have both committed up to index k,
   they must agree on the entry at that position *)
CommitSafety ==
    \A i \in Servers : \A j \in Servers : \A k \in 1..MaxLogLen :
        (commitIndex[i] >= k /\ commitIndex[j] >= k)
        => log[i][k] = log[j][k]

=====================================================================
