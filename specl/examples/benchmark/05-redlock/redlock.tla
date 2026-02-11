---------------------------- MODULE redlock ----------------------------
(* Redlock distributed locking - modeled to find Kleppmann's counterexample
   From: Antirez, "Distributed locks with Redis" (2016)
   Analysis: Kleppmann, "How to do distributed locking" (2016)
   N+1 Redis instances (0..N), M+1 clients (0..M)
   TTL is lock time-to-live in ticks, MaxTime bounds global clock *)

EXTENDS Integers, FiniteSets

CONSTANTS N, M, TTL, MaxTime

VARIABLES globalTime, localClock, clientState, clientLocks,
          acquireTime, nextInstance, instanceLock, instanceExpiry

vars == <<globalTime, localClock, clientState, clientLocks,
          acquireTime, nextInstance, instanceLock, instanceExpiry>>

Clients == 0..M
Instances == 0..N

Majority == (N + 1) \div 2 + 1

Init ==
    /\ globalTime = 0
    /\ localClock = [c \in Clients |-> 0]
    /\ clientState = [c \in Clients |-> 0]
    /\ clientLocks = [c \in Clients |-> {}]
    /\ acquireTime = [c \in Clients |-> 0]
    /\ nextInstance = [c \in Clients |-> 0]
    /\ instanceLock = [i \in Instances |-> -1]
    /\ instanceExpiry = [i \in Instances |-> 0]

(* Global time advances by one tick *)
Tick ==
    /\ globalTime < MaxTime
    /\ globalTime' = globalTime + 1
    /\ UNCHANGED <<localClock, clientState, clientLocks,
                   acquireTime, nextInstance, instanceLock, instanceExpiry>>

(* Client c's local clock advances toward global time *)
ClockAdvance(c) ==
    /\ localClock[c] < globalTime
    /\ localClock' = [localClock EXCEPT ![c] = localClock[c] + 1]
    /\ UNCHANGED <<globalTime, clientState, clientLocks,
                   acquireTime, nextInstance, instanceLock, instanceExpiry>>

(* Instance i's lock expires (TTL exceeded in real/global time) *)
ExpireLock(i) ==
    /\ instanceLock[i] # -1
    /\ globalTime >= instanceExpiry[i]
    /\ instanceLock' = [instanceLock EXCEPT ![i] = -1]
    /\ UNCHANGED <<globalTime, localClock, clientState, clientLocks,
                   acquireTime, nextInstance, instanceExpiry>>

(* Client c starts acquiring the lock *)
StartAcquire(c) ==
    /\ clientState[c] = 0
    /\ clientState' = [clientState EXCEPT ![c] = 1]
    /\ acquireTime' = [acquireTime EXCEPT ![c] = localClock[c]]
    /\ clientLocks' = [clientLocks EXCEPT ![c] = {}]
    /\ nextInstance' = [nextInstance EXCEPT ![c] = 0]
    /\ UNCHANGED <<globalTime, localClock, instanceLock, instanceExpiry>>

(* Client c successfully locks instance i (SET NX equivalent) *)
TryLock(c, i) ==
    /\ clientState[c] = 1
    /\ nextInstance[c] = i
    /\ instanceLock[i] = -1
    /\ instanceLock' = [instanceLock EXCEPT ![i] = c]
    /\ instanceExpiry' = [instanceExpiry EXCEPT ![i] = globalTime + TTL]
    /\ clientLocks' = [clientLocks EXCEPT ![c] = clientLocks[c] \union {i}]
    /\ nextInstance' = [nextInstance EXCEPT ![c] = i + 1]
    /\ UNCHANGED <<globalTime, localClock, clientState, acquireTime>>

(* Client c fails to lock instance i (already locked by another client) *)
FailLock(c, i) ==
    /\ clientState[c] = 1
    /\ nextInstance[c] = i
    /\ instanceLock[i] # -1
    /\ instanceLock[i] # c
    /\ nextInstance' = [nextInstance EXCEPT ![c] = i + 1]
    /\ UNCHANGED <<globalTime, localClock, clientState, clientLocks,
                   acquireTime, instanceLock, instanceExpiry>>

(* Client c finishes acquisition: majority obtained and validity remaining *)
(* Validity check uses LOCAL clock - this is the source of the bug *)
FinishAcquire(c) ==
    /\ clientState[c] = 1
    /\ nextInstance[c] > N
    /\ Cardinality(clientLocks[c]) >= Majority
    /\ localClock[c] - acquireTime[c] < TTL
    /\ clientState' = [clientState EXCEPT ![c] = 2]
    /\ UNCHANGED <<globalTime, localClock, clientLocks,
                   acquireTime, nextInstance, instanceLock, instanceExpiry>>

(* Client c fails acquisition: unlock all instances, return to Idle *)
FailAcquire(c) ==
    /\ clientState[c] = 1
    /\ nextInstance[c] > N
    /\ \/ Cardinality(clientLocks[c]) < Majority
       \/ localClock[c] - acquireTime[c] >= TTL
    /\ clientState' = [clientState EXCEPT ![c] = 0]
    /\ clientLocks' = [clientLocks EXCEPT ![c] = {}]
    /\ instanceLock' = [i \in Instances |->
        IF instanceLock[i] = c THEN -1 ELSE instanceLock[i]]
    /\ UNCHANGED <<globalTime, localClock,
                   acquireTime, nextInstance, instanceExpiry>>

(* Client c releases the lock *)
ReleaseLock(c) ==
    /\ clientState[c] = 2
    /\ clientState' = [clientState EXCEPT ![c] = 3]
    /\ instanceLock' = [i \in Instances |->
        IF instanceLock[i] = c THEN -1 ELSE instanceLock[i]]
    /\ UNCHANGED <<globalTime, localClock, clientLocks,
                   acquireTime, nextInstance, instanceExpiry>>

Next ==
    \/ Tick
    \/ \E c \in Clients : ClockAdvance(c)
    \/ \E i \in Instances : ExpireLock(i)
    \/ \E c \in Clients : StartAcquire(c)
    \/ \E c \in Clients, i \in Instances : TryLock(c, i)
    \/ \E c \in Clients, i \in Instances : FailLock(c, i)
    \/ \E c \in Clients : FinishAcquire(c)
    \/ \E c \in Clients : FailAcquire(c)
    \/ \E c \in Clients : ReleaseLock(c)

Spec == Init /\ [][Next]_vars

(* Mutual exclusion: at most one client in Holding state *)
(* This SHOULD be VIOLATED -- the checker finds Kleppmann's counterexample *)
MutualExclusion ==
    \A c1 \in Clients : \A c2 \in Clients :
        (clientState[c1] = 2 /\ clientState[c2] = 2) => c1 = c2

=====================================================================
