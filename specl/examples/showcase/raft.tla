---- MODULE RaftSpecl ----
(*
 * Raft specification structurally identical to specl/examples/showcase/raft.specl.
 * For apples-to-apples performance comparison between specl BFS and TLC BFS.
 *
 * Differences from Vanlightly's TLA+ that make state spaces match specl:
 *   - Messages as sets of integer tuples (not bags of records)
 *   - 4 separate message sets (reqVoteReqs, reqVoteResps, aeReqs, aeResps)
 *   - Log split into logTerm and logValue (not sequence of records)
 *   - votesGranted as [Server -> [Server -> BOOLEAN]]
 *   - AdvanceCommitIndex parameterized with maximality guard
 *   - UpdateTerm split into 4 actions (one per message type)
 *   - acked uses integers (-1=Nil, 0=submitted, 1=committed)
 *   - Server IDs are integers 0..N
 *)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N, MaxVal, MaxElections, MaxRestarts, MaxLogLen

Server == 0..N
Values == 0..MaxVal

\* Per-server state
VARIABLE currentTerm
VARIABLE state           \* 0=Follower, 1=Candidate, 2=Leader
VARIABLE votedFor        \* -1 = Nil
VARIABLE logTerm         \* logTerm[i] = sequence of terms (1-based)
VARIABLE logValue        \* logValue[i] = sequence of values (1-based)
VARIABLE commitIndex

\* Candidate state
VARIABLE votesGranted    \* [Server -> [Server -> BOOLEAN]]

\* Leader state
VARIABLE nextIndex
VARIABLE matchIndex
VARIABLE pendingResponse

\* Auxiliary
VARIABLE acked           \* -1=Nil, 0=submitted, 1=committed
VARIABLE electionCtr
VARIABLE restartCtr

\* Message sets (separate per type, as sets of integer tuples)
VARIABLE reqVoteReqs
VARIABLE reqVoteResps
VARIABLE aeReqs
VARIABLE aeResps

vars == <<currentTerm, state, votedFor, logTerm, logValue, commitIndex,
          votesGranted, nextIndex, matchIndex, pendingResponse,
          acked, electionCtr, restartCtr,
          reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

----
\* Helpers

LastTerm(lt) == IF Len(lt) = 0 THEN 0 ELSE lt[Len(lt)]
Min2(a, b) == IF a <= b THEN a ELSE b
Max2(a, b) == IF a >= b THEN a ELSE b

----
Init ==
    /\ currentTerm = [i \in Server |-> 1]
    /\ state = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> -1]
    /\ logTerm = [i \in Server |-> <<>>]
    /\ logValue = [i \in Server |-> <<>>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ votesGranted = [i \in Server |-> [j \in Server |-> FALSE]]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ pendingResponse = [i \in Server |-> [j \in Server |-> FALSE]]
    /\ acked = [v \in Values |-> -1]
    /\ electionCtr = 0
    /\ restartCtr = 0
    /\ reqVoteReqs = {}
    /\ reqVoteResps = {}
    /\ aeReqs = {}
    /\ aeResps = {}

----
\* =========================================================================
\* Actions
\* =========================================================================

\* Server i restarts from stable storage (loses volatile state)
Restart(i) ==
    /\ restartCtr < MaxRestarts
    /\ state' = [state EXCEPT ![i] = 0]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
    /\ restartCtr' = restartCtr + 1
    /\ UNCHANGED <<currentTerm, votedFor, logTerm, logValue,
                   acked, electionCtr,
                   reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

\* Combined Timeout + RequestVote: server i starts election
RequestVote(i) ==
    /\ electionCtr < MaxElections
    /\ state[i] \in {0, 1}
    /\ state' = [state EXCEPT ![i] = 1]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = [j \in Server |-> j = i]]
    /\ electionCtr' = electionCtr + 1
    /\ reqVoteReqs' = reqVoteReqs \union
        {<<currentTerm[i] + 1, i, j, LastTerm(logTerm[i]), Len(logTerm[i])>>
         : j \in Server \ {i}}
    /\ UNCHANGED <<logTerm, logValue, commitIndex, nextIndex, matchIndex,
                   pendingResponse, acked, restartCtr,
                   reqVoteResps, aeReqs, aeResps>>

\* Candidate i becomes leader with quorum
BecomeLeader(i) ==
    /\ state[i] = 1
    /\ Cardinality({k \in Server : votesGranted[i][k]}) * 2 > N + 1
    /\ state' = [state EXCEPT ![i] = 2]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(logTerm[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ UNCHANGED <<currentTerm, votedFor, logTerm, logValue, commitIndex,
                   votesGranted, acked, electionCtr, restartCtr,
                   reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

\* Leader i receives client request to add value v
ClientRequest(i, v) ==
    /\ state[i] = 2
    /\ acked[v] = -1
    /\ logTerm' = [logTerm EXCEPT ![i] = Append(@, currentTerm[i])]
    /\ logValue' = [logValue EXCEPT ![i] = Append(@, v)]
    /\ acked' = [acked EXCEPT ![v] = 0]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex,
                   votesGranted, nextIndex, matchIndex, pendingResponse,
                   electionCtr, restartCtr,
                   reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

\* Leader i sends AppendEntries to follower j
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = 2
    /\ pendingResponse[i][j] = FALSE
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0
                          THEN logTerm[i][prevLogIndex]
                          ELSE 0
           hasEntry == IF nextIndex[i][j] <= Len(logTerm[i]) THEN 1 ELSE 0
           entryTerm == IF hasEntry = 1 THEN logTerm[i][nextIndex[i][j]] ELSE 0
           entryValue == IF hasEntry = 1 THEN logValue[i][nextIndex[i][j]] ELSE 0
           ci == Min2(commitIndex[i], Min2(Len(logTerm[i]), nextIndex[i][j]))
       IN
       /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = TRUE]
       /\ aeReqs' = aeReqs \union
           {<<currentTerm[i], i, j, prevLogIndex, prevLogTerm,
              hasEntry, entryTerm, entryValue, ci>>}
    /\ UNCHANGED <<currentTerm, state, votedFor, logTerm, logValue, commitIndex,
                   votesGranted, nextIndex, matchIndex,
                   acked, electionCtr, restartCtr,
                   reqVoteReqs, reqVoteResps, aeResps>>

\* Leader i advances commitIndex to k (parameterized with maximality guard)
AdvanceCommitIndex(i, k) ==
    /\ state[i] = 2
    /\ k <= Len(logTerm[i])
    /\ k > commitIndex[i]
    /\ logTerm[i][k] = currentTerm[i]
    /\ Cardinality({j \in Server : matchIndex[i][j] >= k \/ j = i}) * 2 > N + 1
    \* k must be the maximum valid index
    /\ \A k2 \in 1..MaxLogLen :
        ~(/\ k2 > k
          /\ k2 <= Len(logTerm[i])
          /\ logTerm[i][k2] = currentTerm[i]
          /\ Cardinality({j \in Server : matchIndex[i][j] >= k2 \/ j = i}) * 2 > N + 1)
    /\ commitIndex' = [commitIndex EXCEPT ![i] = k]
    /\ acked' = [v \in Values |->
        IF /\ acked[v] = 0
           /\ \E idx \in (commitIndex[i] + 1)..k : logValue[i][idx] = v
        THEN 1
        ELSE acked[v]]
    /\ UNCHANGED <<currentTerm, state, votedFor, logTerm, logValue,
                   votesGranted, nextIndex, matchIndex, pendingResponse,
                   electionCtr, restartCtr,
                   reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

----
\* =========================================================================
\* UpdateTerm: split into 4 actions (one per message type)
\* Message stays in set for further processing.
\* =========================================================================

\* ReqVoteReq:  <<term, src, dest, lastLogTerm, lastLogIndex>>
UpdateTermReqVoteReq ==
    \E msg \in reqVoteReqs :
        /\ msg[1] > currentTerm[msg[3]]
        /\ currentTerm' = [currentTerm EXCEPT ![msg[3]] = msg[1]]
        /\ state' = [state EXCEPT ![msg[3]] = 0]
        /\ votedFor' = [votedFor EXCEPT ![msg[3]] = -1]
        /\ UNCHANGED <<logTerm, logValue, commitIndex,
                       votesGranted, nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr,
                       reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

\* ReqVoteResp: <<term, src, dest, voteGranted>>
UpdateTermReqVoteResp ==
    \E msg \in reqVoteResps :
        /\ msg[1] > currentTerm[msg[3]]
        /\ currentTerm' = [currentTerm EXCEPT ![msg[3]] = msg[1]]
        /\ state' = [state EXCEPT ![msg[3]] = 0]
        /\ votedFor' = [votedFor EXCEPT ![msg[3]] = -1]
        /\ UNCHANGED <<logTerm, logValue, commitIndex,
                       votesGranted, nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr,
                       reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

\* AEReq: <<term, src, dest, prevLogIndex, prevLogTerm,
\*          hasEntry, entryTerm, entryValue, commitIndex>>
UpdateTermAEReq ==
    \E msg \in aeReqs :
        /\ msg[1] > currentTerm[msg[3]]
        /\ currentTerm' = [currentTerm EXCEPT ![msg[3]] = msg[1]]
        /\ state' = [state EXCEPT ![msg[3]] = 0]
        /\ votedFor' = [votedFor EXCEPT ![msg[3]] = -1]
        /\ UNCHANGED <<logTerm, logValue, commitIndex,
                       votesGranted, nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr,
                       reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

\* AEResp: <<term, src, dest, success, matchIndex>>
UpdateTermAEResp ==
    \E msg \in aeResps :
        /\ msg[1] > currentTerm[msg[3]]
        /\ currentTerm' = [currentTerm EXCEPT ![msg[3]] = msg[1]]
        /\ state' = [state EXCEPT ![msg[3]] = 0]
        /\ votedFor' = [votedFor EXCEPT ![msg[3]] = -1]
        /\ UNCHANGED <<logTerm, logValue, commitIndex,
                       votesGranted, nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr,
                       reqVoteReqs, reqVoteResps, aeReqs, aeResps>>

----
\* =========================================================================
\* HandleRequestVoteRequest (LessOrEqualTerm)
\* =========================================================================

HandleRequestVoteRequest ==
    \E msg \in reqVoteReqs :
        /\ msg[1] <= currentTerm[msg[3]]
        /\ LET dest == msg[3]
               src == msg[2]
               grant == /\ msg[1] = currentTerm[dest]
                        /\ \/ msg[4] > LastTerm(logTerm[dest])
                           \/ /\ msg[4] = LastTerm(logTerm[dest])
                              /\ msg[5] >= Len(logTerm[dest])
                        /\ votedFor[dest] \in {-1, src}
           IN
           /\ votedFor' = [votedFor EXCEPT ![dest] = IF grant THEN src ELSE @]
           /\ reqVoteReqs' = reqVoteReqs \ {msg}
           /\ reqVoteResps' = reqVoteResps \union
               {<<currentTerm[dest], dest, src, IF grant THEN 1 ELSE 0>>}
        /\ UNCHANGED <<currentTerm, state, logTerm, logValue, commitIndex,
                       votesGranted, nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr, aeReqs, aeResps>>

----
\* =========================================================================
\* HandleRequestVoteResponse (EqualTerm)
\* =========================================================================

HandleRequestVoteResponse ==
    \E msg \in reqVoteResps :
        /\ msg[1] = currentTerm[msg[3]]
        /\ votesGranted' = [votesGranted EXCEPT ![msg[3]][msg[2]] =
            IF msg[4] = 1 THEN TRUE ELSE @]
        /\ reqVoteResps' = reqVoteResps \ {msg}
        /\ UNCHANGED <<currentTerm, state, votedFor, logTerm, logValue, commitIndex,
                       nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr,
                       reqVoteReqs, aeReqs, aeResps>>

----
\* =========================================================================
\* RejectAppendEntriesRequest (LessOrEqualTerm, stale term or log mismatch)
\* =========================================================================

RejectAppendEntriesRequest ==
    \E msg \in aeReqs :
        /\ msg[1] <= currentTerm[msg[3]]
        /\ \/ msg[1] < currentTerm[msg[3]]
           \/ /\ msg[1] = currentTerm[msg[3]]
              /\ state[msg[3]] = 0
              /\ msg[4] > 0
              /\ IF msg[4] > Len(logTerm[msg[3]])
                 THEN TRUE
                 ELSE logTerm[msg[3]][msg[4]] # msg[5]
        /\ aeReqs' = aeReqs \ {msg}
        /\ aeResps' = aeResps \union {<<currentTerm[msg[3]], msg[3], msg[2], 0, 0>>}
        /\ UNCHANGED <<currentTerm, state, votedFor, logTerm, logValue, commitIndex,
                       votesGranted, nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr,
                       reqVoteReqs, reqVoteResps>>

----
\* =========================================================================
\* AcceptAppendEntriesRequest (EqualTerm, log matches)
\* =========================================================================

AcceptAppendEntriesRequest ==
    \E msg \in aeReqs :
        LET dest == msg[3]
            src == msg[2]
        IN
        /\ msg[1] = currentTerm[dest]
        /\ state[dest] \in {0, 1}
        \* logOk
        /\ \/ msg[4] = 0
           \/ /\ msg[4] > 0
              /\ msg[4] <= Len(logTerm[dest])
              /\ logTerm[dest][msg[4]] = msg[5]
        /\ state' = [state EXCEPT ![dest] = 0]
        /\ logTerm' = [logTerm EXCEPT ![dest] =
            IF msg[6] = 1
            THEN Append(SubSeq(@, 1, msg[4]), msg[7])
            ELSE IF Len(@) > msg[4]
            THEN SubSeq(@, 1, msg[4])
            ELSE @]
        /\ logValue' = [logValue EXCEPT ![dest] =
            IF msg[6] = 1
            THEN Append(SubSeq(@, 1, msg[4]), msg[8])
            ELSE IF Len(@) > msg[4]
            THEN SubSeq(@, 1, msg[4])
            ELSE @]
        /\ commitIndex' = [commitIndex EXCEPT ![dest] = msg[9]]
        /\ aeReqs' = aeReqs \ {msg}
        /\ aeResps' = aeResps \union
            {<<currentTerm[dest], dest, src, 1, msg[4] + msg[6]>>}
        /\ UNCHANGED <<currentTerm, votedFor, votesGranted,
                       nextIndex, matchIndex, pendingResponse,
                       acked, electionCtr, restartCtr,
                       reqVoteReqs, reqVoteResps>>

----
\* =========================================================================
\* HandleAppendEntriesResponse (EqualTerm)
\* =========================================================================

HandleAppendEntriesResponse ==
    \E msg \in aeResps :
        LET leader == msg[3]
            follower == msg[2]
        IN
        /\ msg[1] = currentTerm[leader]
        /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] =
            IF msg[4] = 1 THEN msg[5] + 1 ELSE Max2(@ - 1, 1)]
        /\ matchIndex' = [matchIndex EXCEPT ![leader][follower] =
            IF msg[4] = 1 THEN msg[5] ELSE @]
        /\ pendingResponse' = [pendingResponse EXCEPT ![leader][follower] = FALSE]
        /\ aeResps' = aeResps \ {msg}
        /\ UNCHANGED <<currentTerm, state, votedFor, logTerm, logValue, commitIndex,
                       votesGranted, acked, electionCtr, restartCtr,
                       reqVoteReqs, reqVoteResps, aeReqs>>

----
\* =========================================================================
\* Next
\* =========================================================================

Next ==
    \/ \E i \in Server : Restart(i)
    \/ \E i \in Server : RequestVote(i)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server, v \in Values : ClientRequest(i, v)
    \/ \E i, j \in Server : AppendEntries(i, j)
    \/ \E i \in Server, k \in 1..MaxLogLen : AdvanceCommitIndex(i, k)
    \/ UpdateTermReqVoteReq
    \/ UpdateTermReqVoteResp
    \/ UpdateTermAEReq
    \/ UpdateTermAEResp
    \/ HandleRequestVoteRequest
    \/ HandleRequestVoteResponse
    \/ RejectAppendEntriesRequest
    \/ AcceptAppendEntriesRequest
    \/ HandleAppendEntriesResponse

----
\* =========================================================================
\* Invariants
\* =========================================================================

NoLogDivergence ==
    \A s1 \in Server : \A s2 \in Server :
        (s1 # s2 /\ commitIndex[s1] > 0 /\ commitIndex[s2] > 0) =>
        (\A idx \in 1..MaxLogLen :
            (idx <= commitIndex[s1] /\ idx <= commitIndex[s2]
             /\ idx <= Len(logTerm[s1]) /\ idx <= Len(logTerm[s2])) =>
            (logTerm[s1][idx] = logTerm[s2][idx]
             /\ logValue[s1][idx] = logValue[s2][idx]))

\* Note: idx range 1..(N+1) matches specl's 0..N. Covers all log positions
\* when MaxLogLen <= N+1 (true for both tested configs). See GitHub issue #34.
LeaderHasAllAckedValues ==
    \A v \in Values :
        acked[v] = 1 =>
        ~(\E i \in Server :
            /\ state[i] = 2
            /\ ~(\E l \in Server : l # i /\ currentTerm[l] > currentTerm[i])
            /\ ~(\E idx \in 1..(N + 1) :
                  idx <= Len(logValue[i]) /\ logValue[i][idx] = v))

====
