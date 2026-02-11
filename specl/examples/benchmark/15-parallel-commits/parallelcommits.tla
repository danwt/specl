------------------------ MODULE parallelcommits -------------------------
(* CockroachDB Parallel Commits - transaction commit with concurrent recovery
   Based on: cockroachdb/cockroach TLA+ specification
   One committer, P+1 preventers. K+1 keys. Key 0 pipelined, 1..K parallel. *)

EXTENDS Integers, FiniteSets

CONSTANTS K, P, MaxAttempts

VARIABLES recordStatus, recordEpoch, recordTs,
          intentEpoch, intentTs, intentResolved,
          tscache, commitAck,
          cPc, attempt, txnEpoch, txnTs,
          toWrite, toCheck, haveStagingRecord,
          pPc, preventEpoch, preventTs, foundWrites, toResolve

vars == <<recordStatus, recordEpoch, recordTs,
          intentEpoch, intentTs, intentResolved,
          tscache, commitAck,
          cPc, attempt, txnEpoch, txnTs,
          toWrite, toCheck, haveStagingRecord,
          pPc, preventEpoch, preventTs, foundWrites, toResolve>>

Keys == 0..K
Preventers == 0..P

QueryIntent(k, qEpoch, qTs) ==
    /\ intentEpoch[k] = qEpoch
    /\ intentTs[k] <= qTs
    /\ ~intentResolved[k]

AnyInSet(d) == \E k \in Keys : d[k]

ImplicitlyCommitted ==
    /\ recordStatus = 1
    /\ \A k \in Keys : intentEpoch[k] = recordEpoch /\ intentTs[k] <= recordTs

Committed == ImplicitlyCommitted \/ recordStatus = 2

\* unchanged helpers
cVars == <<cPc, attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
pVars == <<pPc, preventEpoch, preventTs, foundWrites, toResolve>>
globalVars == <<recordStatus, recordEpoch, recordTs,
                intentEpoch, intentTs, intentResolved, tscache, commitAck>>

Init ==
    /\ recordStatus = 0 /\ recordEpoch = 0 /\ recordTs = 0
    /\ intentEpoch = [k \in Keys |-> 0]
    /\ intentTs = [k \in Keys |-> 0]
    /\ intentResolved = [k \in Keys |-> FALSE]
    /\ tscache = [k \in Keys |-> 0]
    /\ commitAck = FALSE
    /\ cPc = 0 /\ attempt = 1 /\ txnEpoch = 0 /\ txnTs = 0
    /\ toWrite = [k \in Keys |-> FALSE]
    /\ toCheck = [k \in Keys |-> FALSE]
    /\ haveStagingRecord = FALSE
    /\ pPc = [p \in Preventers |-> 0]
    /\ preventEpoch = [p \in Preventers |-> 0]
    /\ preventTs = [p \in Preventers |-> 0]
    /\ foundWrites = [p \in Preventers |-> [k \in Keys |-> FALSE]]
    /\ toResolve = [p \in Preventers |-> [k \in Keys |-> TRUE]]

\* === COMMITTER ===

BeginTxnEpoch ==
    /\ cPc = 0
    /\ txnEpoch' = txnEpoch + 1
    /\ txnTs' = txnTs + 1
    /\ toWrite' = [toWrite EXCEPT ![0] = TRUE]
    /\ cPc' = IF attempt > MaxAttempts THEN 10 ELSE 1
    /\ UNCHANGED <<attempt, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

PipelineWriteKey(k) ==
    /\ cPc = 1
    /\ toWrite[k]
    /\ toWrite' = [toWrite EXCEPT ![k] = FALSE]
    /\ cPc' = IF \A j \in Keys : j = k \/ ~toWrite[j] THEN 2 ELSE 1
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

PipelineWriteKeySucc(k) ==
    /\ cPc = 1
    /\ toWrite[k]
    /\ ~intentResolved[k]
    /\ tscache[k] < txnTs
    /\ toWrite' = [toWrite EXCEPT ![k] = FALSE]
    /\ intentEpoch' = [intentEpoch EXCEPT ![k] = txnEpoch]
    /\ intentTs' = [intentTs EXCEPT ![k] = txnTs]
    /\ intentResolved' = [intentResolved EXCEPT ![k] = FALSE]
    /\ cPc' = IF \A j \in Keys : j = k \/ ~toWrite[j] THEN 2 ELSE 1
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<recordStatus, recordEpoch, recordTs, tscache, commitAck, pVars>>

StageWritesAndRecord ==
    /\ cPc = 2
    /\ toWrite' = [k \in Keys |-> k >= 1]
    /\ toCheck' = [k \in Keys |-> k = 0]
    /\ haveStagingRecord' = FALSE
    /\ cPc' = IF attempt > MaxAttempts THEN 10 ELSE 3
    /\ UNCHANGED <<attempt, txnEpoch, txnTs>>
    /\ UNCHANGED <<globalVars, pVars>>

StageWritesAndRecordLoop ==
    /\ cPc = 3
    /\ ~AnyInSet(toCheck) /\ ~AnyInSet(toWrite) /\ haveStagingRecord
    /\ cPc' = 7
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

DispatchQuery ==
    /\ cPc = 3
    /\ AnyInSet(toCheck)
    /\ cPc' = 4
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

DispatchParallelWrite ==
    /\ cPc = 3
    /\ AnyInSet(toWrite)
    /\ cPc' = 5
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

DispatchStageRecord ==
    /\ cPc = 3
    /\ ~haveStagingRecord
    /\ cPc' = 6
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

QueryPipelinedWriteOk(k) ==
    /\ cPc = 4
    /\ toCheck[k]
    /\ QueryIntent(k, txnEpoch, txnTs)
    /\ toCheck' = [toCheck EXCEPT ![k] = FALSE]
    /\ cPc' = 3
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

QueryPipelinedWriteRestartEpoch(k) ==
    /\ cPc = 4
    /\ toCheck[k]
    /\ ~QueryIntent(k, txnEpoch, txnTs)
    /\ recordStatus \in {0, 1}
    /\ attempt' = attempt + 1
    /\ cPc' = 0
    /\ UNCHANGED <<txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

QueryPipelinedWriteAborted(k) ==
    /\ cPc = 4
    /\ toCheck[k]
    /\ ~QueryIntent(k, txnEpoch, txnTs)
    /\ recordStatus = 3
    /\ cPc' = 10
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

QueryPipelinedWriteCommitted(k) ==
    /\ cPc = 4
    /\ toCheck[k]
    /\ ~QueryIntent(k, txnEpoch, txnTs)
    /\ recordStatus = 2
    /\ cPc' = 7
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

ParallelWriteIdem(k) ==
    /\ cPc = 5
    /\ toWrite[k]
    /\ intentEpoch[k] = txnEpoch
    /\ toWrite' = [toWrite EXCEPT ![k] = FALSE]
    /\ cPc' = 3
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

ParallelWriteRefresh(k) ==
    /\ cPc = 5
    /\ toWrite[k]
    /\ intentEpoch[k] # txnEpoch
    /\ tscache[k] >= txnTs \/ intentResolved[k]
    /\ txnTs' = txnTs + 1
    /\ attempt' = attempt + 1
    /\ cPc' = 2
    /\ UNCHANGED <<txnEpoch, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

ParallelWriteRestartEpoch(k) ==
    /\ cPc = 5
    /\ toWrite[k]
    /\ intentEpoch[k] # txnEpoch
    /\ tscache[k] >= txnTs \/ intentResolved[k]
    /\ attempt' = attempt + 1
    /\ cPc' = 0
    /\ UNCHANGED <<txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

ParallelWriteSucc(k) ==
    /\ cPc = 5
    /\ toWrite[k]
    /\ intentEpoch[k] # txnEpoch
    /\ tscache[k] < txnTs
    /\ ~intentResolved[k]
    /\ toWrite' = [toWrite EXCEPT ![k] = FALSE]
    /\ intentEpoch' = [intentEpoch EXCEPT ![k] = txnEpoch]
    /\ intentTs' = [intentTs EXCEPT ![k] = txnTs]
    /\ intentResolved' = [intentResolved EXCEPT ![k] = FALSE]
    /\ cPc' = 3
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<recordStatus, recordEpoch, recordTs, tscache, commitAck, pVars>>

StageRecordOk ==
    /\ cPc = 6
    /\ recordStatus \in {0, 1}
    /\ haveStagingRecord' = TRUE
    /\ recordStatus' = 1
    /\ recordEpoch' = txnEpoch
    /\ recordTs' = txnTs
    /\ cPc' = 3
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck>>
    /\ UNCHANGED <<intentEpoch, intentTs, intentResolved, tscache, commitAck, pVars>>

StageRecordAborted ==
    /\ cPc = 6
    /\ recordStatus = 3
    /\ cPc' = 10
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

AckClient ==
    /\ cPc = 7
    /\ commitAck' = TRUE
    /\ cPc' = 8
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<recordStatus, recordEpoch, recordTs,
                   intentEpoch, intentTs, intentResolved, tscache, pVars>>

AsyncExplicitlyCommitted ==
    /\ cPc = 8
    /\ recordStatus \in {1, 2}
    /\ recordStatus' = 2
    /\ toWrite' = [k \in Keys |-> TRUE]
    /\ cPc' = 9
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<recordEpoch, recordTs, intentEpoch, intentTs, intentResolved,
                   tscache, commitAck, pVars>>

AsyncResolveIntent(k) ==
    /\ cPc = 9
    /\ toWrite[k]
    /\ toWrite' = [toWrite EXCEPT ![k] = FALSE]
    /\ intentResolved' = [intentResolved EXCEPT ![k] = TRUE]
    /\ cPc' = IF \A j \in Keys : j = k \/ ~toWrite[j] THEN 10 ELSE 9
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<recordStatus, recordEpoch, recordTs,
                   intentEpoch, intentTs, tscache, commitAck, pVars>>

AsyncResolveIntentDone ==
    /\ cPc = 9
    /\ ~AnyInSet(toWrite)
    /\ cPc' = 10
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

EndCommitter ==
    /\ cPc = 10
    /\ cPc' = 11
    /\ UNCHANGED <<attempt, txnEpoch, txnTs, toWrite, toCheck, haveStagingRecord>>
    /\ UNCHANGED <<globalVars, pVars>>

\* === PREVENTERS ===

PreventLoop(p) ==
    /\ pPc[p] = 0
    /\ foundWrites' = [foundWrites EXCEPT ![p] = [k \in Keys |-> FALSE]]
    /\ pPc' = [pPc EXCEPT ![p] = 1]
    /\ UNCHANGED <<preventEpoch, preventTs, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

PushRecordAbort(p) ==
    /\ pPc[p] = 1
    /\ recordStatus = 0
    /\ recordStatus' = 3
    /\ pPc' = [pPc EXCEPT ![p] = 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<recordEpoch, recordTs, intentEpoch, intentTs, intentResolved,
                   tscache, commitAck, cVars>>

PushRecordStaging(p) ==
    /\ pPc[p] = 1
    /\ recordStatus = 1
    /\ preventEpoch' = [preventEpoch EXCEPT ![p] = recordEpoch]
    /\ preventTs' = [preventTs EXCEPT ![p] = recordTs]
    /\ pPc' = [pPc EXCEPT ![p] = 2]
    /\ UNCHANGED <<foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

PushRecordFinalized(p) ==
    /\ pPc[p] = 1
    /\ recordStatus \in {2, 3}
    /\ pPc' = [pPc EXCEPT ![p] = 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

PreventWriteFound(p, k) ==
    /\ pPc[p] = 2
    /\ ~\A j \in Keys : foundWrites[p][j]
    /\ ~foundWrites[p][k]
    /\ QueryIntent(k, preventEpoch[p], preventTs[p])
    /\ foundWrites' = [foundWrites EXCEPT ![p] = [foundWrites[p] EXCEPT ![k] = TRUE]]
    /\ pPc' = [pPc EXCEPT ![p] = IF \A j \in Keys : j = k \/ foundWrites[p][j] THEN 3 ELSE 2]
    /\ UNCHANGED <<preventEpoch, preventTs, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

PreventWriteMissing(p, k) ==
    /\ pPc[p] = 2
    /\ ~\A j \in Keys : foundWrites[p][j]
    /\ ~foundWrites[p][k]
    /\ ~QueryIntent(k, preventEpoch[p], preventTs[p])
    /\ tscache' = [tscache EXCEPT ![k] = IF tscache[k] < preventTs[p] THEN preventTs[p] ELSE @]
    /\ pPc' = [pPc EXCEPT ![p] = 3]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<recordStatus, recordEpoch, recordTs,
                   intentEpoch, intentTs, intentResolved, commitAck, cVars>>

PreventWriteAllFound(p) ==
    /\ pPc[p] = 2
    /\ \A j \in Keys : foundWrites[p][j]
    /\ pPc' = [pPc EXCEPT ![p] = 3]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

RecoverPreventedAborted(p) ==
    /\ pPc[p] = 3
    /\ ~\A j \in Keys : foundWrites[p][j]
    /\ recordStatus = 3
    /\ pPc' = [pPc EXCEPT ![p] = 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

RecoverPreventedCommitted(p) ==
    /\ pPc[p] = 3
    /\ ~\A j \in Keys : foundWrites[p][j]
    /\ recordStatus = 2
    /\ pPc' = [pPc EXCEPT ![p] = 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

RecoverPreventedRetry(p) ==
    /\ pPc[p] = 3
    /\ ~\A j \in Keys : foundWrites[p][j]
    /\ recordStatus = 1
    /\ recordEpoch >= preventEpoch[p] /\ recordTs > preventTs[p]
    /\ pPc' = [pPc EXCEPT ![p] = 0]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

RecoverPreventedAbort(p) ==
    /\ pPc[p] = 3
    /\ ~\A j \in Keys : foundWrites[p][j]
    /\ recordStatus = 1
    /\ ~(recordEpoch >= preventEpoch[p] /\ recordTs > preventTs[p])
    /\ recordStatus' = 3
    /\ pPc' = [pPc EXCEPT ![p] = 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<recordEpoch, recordTs, intentEpoch, intentTs, intentResolved,
                   tscache, commitAck, cVars>>

RecoverNotPreventedCommit(p) ==
    /\ pPc[p] = 3
    /\ \A j \in Keys : foundWrites[p][j]
    /\ recordStatus = 1
    /\ recordEpoch = preventEpoch[p] /\ recordTs = preventTs[p]
    /\ recordStatus' = 2
    /\ pPc' = [pPc EXCEPT ![p] = 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<recordEpoch, recordTs, intentEpoch, intentTs, intentResolved,
                   tscache, commitAck, cVars>>

RecoverNotPreventedDone(p) ==
    /\ pPc[p] = 3
    /\ \A j \in Keys : foundWrites[p][j]
    /\ recordStatus = 2
    /\ recordEpoch = preventEpoch[p] /\ recordTs = preventTs[p]
    /\ pPc' = [pPc EXCEPT ![p] = 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

PResolveIntent(p, k) ==
    /\ pPc[p] = 4
    /\ toResolve[p][k]
    /\ toResolve' = [toResolve EXCEPT ![p] = [toResolve[p] EXCEPT ![k] = FALSE]]
    /\ intentResolved' = [intentResolved EXCEPT ![k] = TRUE]
    /\ pPc' = [pPc EXCEPT ![p] = IF \A j \in Keys : j = k \/ ~toResolve[p][j] THEN 5 ELSE 4]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites>>
    /\ UNCHANGED <<recordStatus, recordEpoch, recordTs,
                   intentEpoch, intentTs, tscache, commitAck, cVars>>

PResolveIntentDone(p) ==
    /\ pPc[p] = 4
    /\ ~\E j \in Keys : toResolve[p][j]
    /\ pPc' = [pPc EXCEPT ![p] = 5]
    /\ UNCHANGED <<preventEpoch, preventTs, foundWrites, toResolve>>
    /\ UNCHANGED <<globalVars, cVars>>

Next ==
    \/ BeginTxnEpoch
    \/ \E k \in Keys : PipelineWriteKey(k)
    \/ \E k \in Keys : PipelineWriteKeySucc(k)
    \/ StageWritesAndRecord
    \/ StageWritesAndRecordLoop
    \/ DispatchQuery
    \/ DispatchParallelWrite
    \/ DispatchStageRecord
    \/ \E k \in Keys : QueryPipelinedWriteOk(k)
    \/ \E k \in Keys : QueryPipelinedWriteRestartEpoch(k)
    \/ \E k \in Keys : QueryPipelinedWriteAborted(k)
    \/ \E k \in Keys : QueryPipelinedWriteCommitted(k)
    \/ \E k \in Keys : ParallelWriteIdem(k)
    \/ \E k \in Keys : ParallelWriteRefresh(k)
    \/ \E k \in Keys : ParallelWriteRestartEpoch(k)
    \/ \E k \in Keys : ParallelWriteSucc(k)
    \/ StageRecordOk
    \/ StageRecordAborted
    \/ AckClient
    \/ AsyncExplicitlyCommitted
    \/ \E k \in Keys : AsyncResolveIntent(k)
    \/ AsyncResolveIntentDone
    \/ EndCommitter
    \/ \E p \in Preventers : PreventLoop(p)
    \/ \E p \in Preventers : PushRecordAbort(p)
    \/ \E p \in Preventers : PushRecordStaging(p)
    \/ \E p \in Preventers : PushRecordFinalized(p)
    \/ \E p \in Preventers, k \in Keys : PreventWriteFound(p, k)
    \/ \E p \in Preventers, k \in Keys : PreventWriteMissing(p, k)
    \/ \E p \in Preventers : PreventWriteAllFound(p)
    \/ \E p \in Preventers : RecoverPreventedAborted(p)
    \/ \E p \in Preventers : RecoverPreventedCommitted(p)
    \/ \E p \in Preventers : RecoverPreventedRetry(p)
    \/ \E p \in Preventers : RecoverPreventedAbort(p)
    \/ \E p \in Preventers : RecoverNotPreventedCommit(p)
    \/ \E p \in Preventers : RecoverNotPreventedDone(p)
    \/ \E p \in Preventers, k \in Keys : PResolveIntent(p, k)
    \/ \E p \in Preventers : PResolveIntentDone(p)

Spec == Init /\ [][Next]_vars

AckImpliesCommit == ~commitAck \/ Committed

=====================================================================
