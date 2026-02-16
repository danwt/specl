---------------------------- MODULE percolator ----------------------------
(* Google Percolator - Distributed Transactions with Snapshot Isolation
   Based on: PingCAP TLA+ specification
   C+1 clients (0..C), K+1 keys (0..K). Client c's primary key = c.
   MaxTs = 2*(C+1) bounds timestamps. *)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS C, K, MaxTs

VARIABLES nextTs, clientState, clientStartTs, clientCommitTs, clientPending,
          keyData, keyLockTs, keyLockPrimary, keyWriteCts, keyWriteSts,
          keyLastReadTs, keySi

vars == <<nextTs, clientState, clientStartTs, clientCommitTs, clientPending,
          keyData, keyLockTs, keyLockPrimary, keyWriteCts, keyWriteSts,
          keyLastReadTs, keySi>>

Clients == 0..C
Keys == 0..K
Timestamps == 1..MaxTs
WriteIndices == 0..C

PrimaryKey(c) == c

HasLockEQ(k, ts) == keyLockTs[k] = ts
HasLockLE(k, ts) == keyLockTs[k] # -1 /\ keyLockTs[k] <= ts

HasWriteWithStartTs(k, sTs) ==
    \E n \in WriteIndices : n < Len(keyWriteSts[k]) /\ keyWriteSts[k][n+1] = sTs

CanLockKey(k, ts) ==
    /\ keyLockTs[k] = -1
    /\ ~\E n \in WriteIndices : n < Len(keyWriteCts[k]) /\ keyWriteCts[k][n+1] >= ts

Init ==
    /\ nextTs = 0
    /\ clientState = [c \in Clients |-> 0]
    /\ clientStartTs = [c \in Clients |-> 0]
    /\ clientCommitTs = [c \in Clients |-> 0]
    /\ clientPending = [c \in Clients |-> [k \in Keys |-> TRUE]]
    /\ keyData = [k \in Keys |-> [ts \in Timestamps |-> FALSE]]
    /\ keyLockTs = [k \in Keys |-> -1]
    /\ keyLockPrimary = [k \in Keys |-> -1]
    /\ keyWriteCts = [k \in Keys |-> <<>>]
    /\ keyWriteSts = [k \in Keys |-> <<>>]
    /\ keyLastReadTs = [k \in Keys |-> 0]
    /\ keySi = [k \in Keys |-> TRUE]

Start(c) ==
    /\ clientState[c] = 0
    /\ nextTs' = nextTs + 1
    /\ clientState' = [clientState EXCEPT ![c] = 1]
    /\ clientStartTs' = [clientStartTs EXCEPT ![c] = nextTs + 1]
    /\ UNCHANGED <<clientCommitTs, clientPending, keyData, keyLockTs,
                   keyLockPrimary, keyWriteCts, keyWriteSts, keyLastReadTs, keySi>>

GetAdvance(c) ==
    /\ clientState[c] = 1
    /\ clientState' = [clientState EXCEPT ![c] = 2]
    /\ UNCHANGED <<nextTs, clientStartTs, clientCommitTs, clientPending, keyData,
                   keyLockTs, keyLockPrimary, keyWriteCts, keyWriteSts,
                   keyLastReadTs, keySi>>

GetRead(c, k) ==
    /\ clientState[c] = 1
    /\ keyLockTs[k] = -1 \/ keyLockTs[k] > clientStartTs[c]
    /\ keyLastReadTs[k] < clientStartTs[c]
    /\ keyLastReadTs' = [keyLastReadTs EXCEPT ![k] = clientStartTs[c]]
    /\ UNCHANGED <<nextTs, clientState, clientStartTs, clientCommitTs, clientPending,
                   keyData, keyLockTs, keyLockPrimary, keyWriteCts, keyWriteSts, keySi>>

CleanupPrimaryLock(c, k) ==
    /\ clientState[c] = 1
    /\ HasLockLE(k, clientStartTs[c])
    /\ keyLockPrimary[k] = k
    /\ keyData' = [keyData EXCEPT ![k] = [keyData[k] EXCEPT ![keyLockTs[k]] = FALSE]]
    /\ keyLockTs' = [keyLockTs EXCEPT ![k] = -1]
    /\ keyLockPrimary' = [keyLockPrimary EXCEPT ![k] = -1]
    /\ UNCHANGED <<nextTs, clientState, clientStartTs, clientCommitTs, clientPending,
                   keyWriteCts, keyWriteSts, keyLastReadTs, keySi>>

CleanupSecRollbackPri(c, k) ==
    LET pk == keyLockPrimary[k]
        lockTs == keyLockTs[k]
    IN
    /\ clientState[c] = 1
    /\ HasLockLE(k, clientStartTs[c])
    /\ pk # k
    /\ ~HasWriteWithStartTs(pk, lockTs)
    /\ HasLockEQ(pk, lockTs)
    /\ keyData' = [keyData EXCEPT ![pk] = [keyData[pk] EXCEPT ![lockTs] = FALSE]]
    /\ keyLockTs' = [keyLockTs EXCEPT ![pk] = -1]
    /\ keyLockPrimary' = [keyLockPrimary EXCEPT ![pk] = -1]
    /\ UNCHANGED <<nextTs, clientState, clientStartTs, clientCommitTs, clientPending,
                   keyWriteCts, keyWriteSts, keyLastReadTs, keySi>>

CleanupSecRollbackSec(c, k) ==
    LET pk == keyLockPrimary[k]
        lockTs == keyLockTs[k]
    IN
    /\ clientState[c] = 1
    /\ HasLockLE(k, clientStartTs[c])
    /\ pk # k
    /\ ~HasWriteWithStartTs(pk, lockTs)
    /\ ~HasLockEQ(pk, lockTs)
    /\ keyData' = [keyData EXCEPT ![k] = [keyData[k] EXCEPT ![lockTs] = FALSE]]
    /\ keyLockTs' = [keyLockTs EXCEPT ![k] = -1]
    /\ keyLockPrimary' = [keyLockPrimary EXCEPT ![k] = -1]
    /\ UNCHANGED <<nextTs, clientState, clientStartTs, clientCommitTs, clientPending,
                   keyWriteCts, keyWriteSts, keyLastReadTs, keySi>>

CleanupSecCommit(c, k, wi) ==
    LET pk == keyLockPrimary[k]
        lockTs == keyLockTs[k]
        commitTs == keyWriteCts[pk][wi+1]
    IN
    /\ clientState[c] = 1
    /\ HasLockLE(k, clientStartTs[c])
    /\ pk # k
    /\ wi < Len(keyWriteSts[pk])
    /\ keyWriteSts[pk][wi+1] = lockTs
    /\ keyLockTs' = [keyLockTs EXCEPT ![k] = -1]
    /\ keyLockPrimary' = [keyLockPrimary EXCEPT ![k] = -1]
    /\ keyWriteCts' = [keyWriteCts EXCEPT ![k] = Append(@, commitTs)]
    /\ keyWriteSts' = [keyWriteSts EXCEPT ![k] = Append(@, lockTs)]
    /\ keySi' = [keySi EXCEPT ![k] = IF keyLastReadTs[k] >= commitTs THEN FALSE ELSE @]
    /\ UNCHANGED <<nextTs, clientState, clientStartTs, clientCommitTs, clientPending,
                   keyData, keyLastReadTs>>

PrewriteAdvance(c) ==
    /\ clientState[c] = 2
    /\ \A k \in Keys : ~clientPending[c][k]
    /\ nextTs' = nextTs + 1
    /\ clientState' = [clientState EXCEPT ![c] = 3]
    /\ clientCommitTs' = [clientCommitTs EXCEPT ![c] = nextTs + 1]
    /\ UNCHANGED <<clientStartTs, clientPending, keyData, keyLockTs,
                   keyLockPrimary, keyWriteCts, keyWriteSts, keyLastReadTs, keySi>>

PrewritePrimary(c) ==
    /\ clientState[c] = 2
    /\ clientPending[c][c]
    /\ CanLockKey(c, clientStartTs[c])
    /\ keyLockTs' = [keyLockTs EXCEPT ![c] = clientStartTs[c]]
    /\ keyLockPrimary' = [keyLockPrimary EXCEPT ![c] = c]
    /\ keyData' = [keyData EXCEPT ![c] = [keyData[c] EXCEPT ![clientStartTs[c]] = TRUE]]
    /\ clientPending' = [clientPending EXCEPT ![c] = [clientPending[c] EXCEPT ![c] = FALSE]]
    /\ UNCHANGED <<nextTs, clientState, clientStartTs, clientCommitTs,
                   keyWriteCts, keyWriteSts, keyLastReadTs, keySi>>

PrewriteSecondary(c, k) ==
    /\ clientState[c] = 2
    /\ k # c
    /\ clientPending[c][k]
    /\ ~clientPending[c][c]
    /\ CanLockKey(k, clientStartTs[c])
    /\ keyLockTs' = [keyLockTs EXCEPT ![k] = clientStartTs[c]]
    /\ keyLockPrimary' = [keyLockPrimary EXCEPT ![k] = c]
    /\ keyData' = [keyData EXCEPT ![k] = [keyData[k] EXCEPT ![clientStartTs[c]] = TRUE]]
    /\ clientPending' = [clientPending EXCEPT ![c] = [clientPending[c] EXCEPT ![k] = FALSE]]
    /\ UNCHANGED <<nextTs, clientState, clientStartTs, clientCommitTs,
                   keyWriteCts, keyWriteSts, keyLastReadTs, keySi>>

Commit(c) ==
    /\ clientState[c] = 3
    /\ HasLockEQ(c, clientStartTs[c])
    /\ keyWriteCts' = [keyWriteCts EXCEPT ![c] = Append(@, clientCommitTs[c])]
    /\ keyWriteSts' = [keyWriteSts EXCEPT ![c] = Append(@, clientStartTs[c])]
    /\ keyLockTs' = [keyLockTs EXCEPT ![c] = -1]
    /\ keyLockPrimary' = [keyLockPrimary EXCEPT ![c] = -1]
    /\ clientState' = [clientState EXCEPT ![c] = 4]
    /\ keySi' = [keySi EXCEPT ![c] = IF keyLastReadTs[c] >= clientCommitTs[c] THEN FALSE ELSE @]
    /\ UNCHANGED <<nextTs, clientStartTs, clientCommitTs, clientPending, keyData,
                   keyLastReadTs>>

Abort(c) ==
    /\ clientState[c] # 4
    /\ clientState[c] # 5
    /\ clientState' = [clientState EXCEPT ![c] = 5]
    /\ UNCHANGED <<nextTs, clientStartTs, clientCommitTs, clientPending, keyData,
                   keyLockTs, keyLockPrimary, keyWriteCts, keyWriteSts,
                   keyLastReadTs, keySi>>

Next ==
    \/ \E c \in Clients : Start(c)
    \/ \E c \in Clients : GetAdvance(c)
    \/ \E c \in Clients, k \in Keys : GetRead(c, k)
    \/ \E c \in Clients, k \in Keys : CleanupPrimaryLock(c, k)
    \/ \E c \in Clients, k \in Keys : CleanupSecRollbackPri(c, k)
    \/ \E c \in Clients, k \in Keys : CleanupSecRollbackSec(c, k)
    \/ \E c \in Clients, k \in Keys, wi \in WriteIndices : CleanupSecCommit(c, k, wi)
    \/ \E c \in Clients : PrewriteAdvance(c)
    \/ \E c \in Clients : PrewritePrimary(c)
    \/ \E c \in Clients, k \in Keys : PrewriteSecondary(c, k)
    \/ \E c \in Clients : Commit(c)
    \/ \E c \in Clients : Abort(c)

Spec == Init /\ [][Next]_vars

WriteConsistency ==
    \A k \in Keys : \A n \in WriteIndices :
        n < Len(keyWriteCts[k]) =>
            /\ keyWriteSts[k][n+1] < keyWriteCts[k][n+1]
            /\ (n > 0 => keyWriteCts[k][n] < keyWriteSts[k][n+1])

LockConsistency ==
    \A c \in Clients : \A k \in Keys :
        (clientState[c] = 3 /\ keyLockTs[c] = clientStartTs[c] /\ k # c)
        => keyLockTs[k] = clientStartTs[c]

AbortedConsistency ==
    \A c \in Clients :
        (clientState[c] = 5 /\ clientCommitTs[c] # 0)
        => ~\E n \in WriteIndices :
            n < Len(keyWriteCts[c]) /\ keyWriteCts[c][n+1] = clientCommitTs[c]

SnapshotIsolation ==
    \A k \in Keys : keySi[k]

=====================================================================
