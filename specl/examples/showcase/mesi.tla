---------------------------- MODULE mesi -----------------------------
(* MESI cache coherence protocol
   From: Papamarcos & Patel (ISCA 1984)
   C+1 cores (0..C), single cache line, values 0..V
   States: 0=Invalid, 1=Shared, 2=Exclusive, 3=Modified *)

EXTENDS Integers, FiniteSets

CONSTANTS C, V

VARIABLES cacheState, cacheData, memory

vars == <<cacheState, cacheData, memory>>

Cores == 0..C
Values == 0..V

Init ==
    /\ cacheState = [c \in Cores |-> 0]
    /\ cacheData = [c \in Cores |-> -1]
    /\ memory = 0

(* BusRd from Invalid when another core has M: M-holder flushes *)
PrRdMissFromM(core, mHolder) ==
    /\ core # mHolder
    /\ cacheState[core] = 0
    /\ cacheState[mHolder] = 3
    /\ cacheState' = [c \in Cores |->
         IF c = core THEN 1
         ELSE IF c = mHolder THEN 1
         ELSE cacheState[c]]
    /\ cacheData' = [cacheData EXCEPT ![core] = cacheData[mHolder]]
    /\ memory' = cacheData[mHolder]

(* BusRd from Invalid when another core has E (no M exists) *)
PrRdMissFromE(core, eHolder) ==
    /\ core # eHolder
    /\ cacheState[core] = 0
    /\ cacheState[eHolder] = 2
    /\ ~\E c \in Cores : c # core /\ cacheState[c] = 3
    /\ cacheState' = [c \in Cores |->
         IF c = core THEN 1
         ELSE IF c = eHolder THEN 1
         ELSE cacheState[c]]
    /\ cacheData' = [cacheData EXCEPT ![core] = memory]
    /\ UNCHANGED memory

(* BusRd from Invalid when others have S only *)
PrRdMissFromS(core) ==
    /\ cacheState[core] = 0
    /\ \E c \in Cores : c # core /\ cacheState[c] = 1
    /\ ~\E c \in Cores : c # core /\ cacheState[c] \in {2, 3}
    /\ cacheState' = [cacheState EXCEPT ![core] = 1]
    /\ cacheData' = [cacheData EXCEPT ![core] = memory]
    /\ UNCHANGED memory

(* BusRd from Invalid when no other cache has the line *)
PrRdMissNoSharers(core) ==
    /\ cacheState[core] = 0
    /\ ~\E c \in Cores : c # core /\ cacheState[c] # 0
    /\ cacheState' = [cacheState EXCEPT ![core] = 2]
    /\ cacheData' = [cacheData EXCEPT ![core] = memory]
    /\ UNCHANGED memory

(* Write from Invalid with M-holder: BusRdX *)
PrWrFromInvalidWithM(core, val, mHolder) ==
    /\ core # mHolder
    /\ cacheState[core] = 0
    /\ cacheState[mHolder] = 3
    /\ memory' = cacheData[mHolder]
    /\ cacheState' = [c \in Cores |-> IF c = core THEN 3 ELSE 0]
    /\ cacheData' = [c \in Cores |-> IF c = core THEN val ELSE -1]

(* Write from Invalid without M-holder *)
PrWrFromInvalidNoM(core, val) ==
    /\ cacheState[core] = 0
    /\ ~\E c \in Cores : c # core /\ cacheState[c] = 3
    /\ cacheState' = [c \in Cores |-> IF c = core THEN 3 ELSE 0]
    /\ cacheData' = [c \in Cores |-> IF c = core THEN val ELSE -1]
    /\ UNCHANGED memory

(* Write from Shared: BusUpgr *)
PrWrFromShared(core, val) ==
    /\ cacheState[core] = 1
    /\ cacheState' = [c \in Cores |->
         IF c = core THEN 3
         ELSE IF cacheState[c] = 1 THEN 0
         ELSE cacheState[c]]
    /\ cacheData' = [c \in Cores |->
         IF c = core THEN val
         ELSE IF cacheState[c] = 1 THEN -1
         ELSE cacheData[c]]
    /\ UNCHANGED memory

(* Write from Exclusive: silent upgrade *)
PrWrFromExclusive(core, val) ==
    /\ cacheState[core] = 2
    /\ cacheState' = [cacheState EXCEPT ![core] = 3]
    /\ cacheData' = [cacheData EXCEPT ![core] = val]
    /\ UNCHANGED memory

(* Write from Modified *)
PrWrFromModified(core, val) ==
    /\ cacheState[core] = 3
    /\ cacheData' = [cacheData EXCEPT ![core] = val]
    /\ UNCHANGED <<cacheState, memory>>

(* Evict Modified: writeback *)
EvictModified(core) ==
    /\ cacheState[core] = 3
    /\ memory' = cacheData[core]
    /\ cacheState' = [cacheState EXCEPT ![core] = 0]
    /\ cacheData' = [cacheData EXCEPT ![core] = -1]

(* Evict Clean: silent *)
EvictClean(core) ==
    /\ cacheState[core] \in {1, 2}
    /\ cacheState' = [cacheState EXCEPT ![core] = 0]
    /\ cacheData' = [cacheData EXCEPT ![core] = -1]
    /\ UNCHANGED memory

Next ==
    \/ \E core \in Cores, mHolder \in Cores : PrRdMissFromM(core, mHolder)
    \/ \E core \in Cores, eHolder \in Cores : PrRdMissFromE(core, eHolder)
    \/ \E core \in Cores : PrRdMissFromS(core)
    \/ \E core \in Cores : PrRdMissNoSharers(core)
    \/ \E core \in Cores, val \in Values, mHolder \in Cores : PrWrFromInvalidWithM(core, val, mHolder)
    \/ \E core \in Cores, val \in Values : PrWrFromInvalidNoM(core, val)
    \/ \E core \in Cores, val \in Values : PrWrFromShared(core, val)
    \/ \E core \in Cores, val \in Values : PrWrFromExclusive(core, val)
    \/ \E core \in Cores, val \in Values : PrWrFromModified(core, val)
    \/ \E core \in Cores : EvictModified(core)
    \/ \E core \in Cores : EvictClean(core)

Spec == Init /\ [][Next]_vars

SWMR ==
    \A c1 \in Cores : \A c2 \in Cores :
        (c1 # c2 /\ cacheState[c1] = 3) => cacheState[c2] = 0

ExclusiveExclusive ==
    \A c1 \in Cores : \A c2 \in Cores :
        (c1 # c2 /\ cacheState[c1] = 2) => cacheState[c2] = 0

SharedMatchesMemory ==
    \A c \in Cores : cacheState[c] = 1 => cacheData[c] = memory

ExclusiveMatchesMemory ==
    \A c \in Cores : cacheState[c] = 2 => cacheData[c] = memory

=====================================================================
