---- MODULE BronsonAVL ----
\* Bronson et al. concurrent AVL tree (PPOPP 2010) - writer-only model
\* Translated from bronson_avl.specl

EXTENDS Integers, Sequences

\* --- Special values ---
Null == 101
Shrinking == 102
Unlinked == 103
Retry == 104
DirectionLeft == 105
DirectionRite == 106
NoRepair == 107
UnlinkReq == 108
RebalanceReq == 109

Addr == 0..14
Procs == 0..1
Keys == 1..11

\* ======== Tree state ========
VARIABLES ver, key, val, height, parent, left, rite, locked
\* ======== Process state ========
VARIABLES pc, ret, retStack, auSaveStack
\* ======== update locals ========
VARIABLES U_k, U_newValue
\* ======== attemptUpdate locals ========
VARIABLES AU_k, AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged
\* ======== attemptNodeUpdate locals ========
VARIABLES ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged
\* ======== attemptUnlink locals ========
VARIABLES AUL_parent, AUL_node
\* ======== nodeCondition locals ========
VARIABLES NC_node
\* ======== fixHeightAndRebalance locals ========
VARIABLES FHR_node, FHR_condition, FHR_nParent
\* ======== fixHeight locals ========
VARIABLES FH_node
\* ======== rebalance locals ========
VARIABLES REB_nParent, REB_n, REB_nL, REB_nR
\* ======== rebalanceToRite locals ========
VARIABLES REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0
\* ======== rebalanceToLeft locals ========
VARIABLES REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0
\* ======== rotateRite locals ========
VARIABLES ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR
\* ======== rotateLeft locals ========
VARIABLES ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR
\* ======== rotateRiteOverLeft locals ========
VARIABLES ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL
\* ======== rotateLeftOverRite locals ========
VARIABLES ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR

allVars == <<ver, key, val, height, parent, left, rite, locked, pc, ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

\* ======== Helper functions ========
NullSafeHeight(e) == IF e = Null THEN 0 ELSE height[e]
MaxPlusOne(x, y) == IF y < x THEN x + 1 ELSE y + 1
Child(addr, dir) == IF dir = DirectionLeft THEN left[addr] ELSE rite[addr]

TH5(e5) == IF e5 = Null THEN 0 ELSE 1
LH5(n5) == TH5(left[n5])
RH5(n5) == TH5(rite[n5])
TH4(e4) == IF e4 = Null THEN 0 ELSE IF RH5(e4) < LH5(e4) THEN LH5(e4) + 1 ELSE RH5(e4) + 1
LH4(n4) == TH4(left[n4])
RH4(n4) == TH4(rite[n4])
TH3(e3) == IF e3 = Null THEN 0 ELSE IF RH4(e3) < LH4(e3) THEN LH4(e3) + 1 ELSE RH4(e3) + 1
LH3(n3) == TH3(left[n3])
RH3(n3) == TH3(rite[n3])
TH2(e2) == IF e2 = Null THEN 0 ELSE IF RH3(e2) < LH3(e2) THEN LH3(e2) + 1 ELSE RH3(e2) + 1
LH2(n2) == TH2(left[n2])
RH2(n2) == TH2(rite[n2])
TH1(e1) == IF e1 = Null THEN 0 ELSE IF RH2(e1) < LH2(e1) THEN LH2(e1) + 1 ELSE RH2(e1) + 1
LH1(n1) == TH1(left[n1])
RH1(n1) == TH1(rite[n1])
TrueHeight(e0) == IF e0 = Null THEN 0 ELSE IF RH1(e0) < LH1(e0) THEN LH1(e0) + 1 ELSE RH1(e0) + 1

UnusedAddr == IF key[1] = Null THEN 1 ELSE IF key[2] = Null THEN 2 ELSE IF key[3] = Null THEN 3
              ELSE IF key[4] = Null THEN 4 ELSE IF key[5] = Null THEN 5 ELSE IF key[6] = Null THEN 6
              ELSE IF key[7] = Null THEN 7 ELSE IF key[8] = Null THEN 8 ELSE IF key[9] = Null THEN 9
              ELSE IF key[10] = Null THEN 10 ELSE IF key[11] = Null THEN 11 ELSE IF key[12] = Null THEN 12
              ELSE IF key[13] = Null THEN 13 ELSE 14

\* Stack helpers (TLA+ is 1-indexed)
RetTop(p) == retStack[p][Len(retStack[p])]
RetPop(p) == SubSeq(retStack[p], 1, Len(retStack[p]) - 1)

\* ======== Initial state ========
Init ==
    /\ key = [a \in Addr |-> CASE a = 4 -> 4 [] a = 5 -> 5 [] a = 6 -> 6 [] a = 7 -> 7
                                [] a = 8 -> 8 [] a = 9 -> 9 [] a = 10 -> 10 [] OTHER -> Null]
    /\ val = [a \in Addr |-> CASE a = 4 -> 4 [] a = 5 -> 5 [] a = 6 -> 6 [] a = 7 -> 7
                                [] a = 8 -> 8 [] a = 9 -> 9 [] a = 10 -> 10 [] OTHER -> Null]
    /\ left = [a \in Addr |-> CASE a = 5 -> 4 [] a = 6 -> 5 [] a = 8 -> 7 [] a = 9 -> 8 [] OTHER -> Null]
    /\ rite = [a \in Addr |-> CASE a = 0 -> 6 [] a = 6 -> 9 [] a = 9 -> 10 [] OTHER -> Null]
    /\ height = [a \in Addr |-> CASE a = 0 -> 5 [] a = 4 -> 1 [] a = 5 -> 2 [] a = 6 -> 4
                                  [] a = 7 -> 1 [] a = 8 -> 2 [] a = 9 -> 3 [] a = 10 -> 1 [] OTHER -> 0]
    /\ parent = [a \in Addr |-> CASE a = 4 -> 5 [] a = 5 -> 6 [] a = 6 -> 0 [] a = 7 -> 8
                                  [] a = 8 -> 9 [] a = 9 -> 6 [] a = 10 -> 9 [] OTHER -> Null]
    /\ ver = [a \in Addr |-> 0]
    /\ locked = [a \in Addr |-> -1]
    /\ pc = [p \in Procs |-> 1]
    /\ ret = [p \in Procs |-> Null]
    /\ retStack = [p \in Procs |-> << >>]
    /\ auSaveStack = [p \in Procs |-> << >>]
    /\ U_k = [p \in Procs |-> Null]
    /\ U_newValue = [p \in Procs |-> Null]
    /\ AU_k = [p \in Procs |-> Null]
    /\ AU_newValue = [p \in Procs |-> Null]
    /\ AU_parent = [p \in Procs |-> Null]
    /\ AU_node = [p \in Procs |-> Null]
    /\ AU_nodeVer = [p \in Procs |-> Null]
    /\ AU_dirToC = [p \in Procs |-> Null]
    /\ AU_child = [p \in Procs |-> Null]
    /\ AU_damaged = [p \in Procs |-> Null]
    /\ ANU_newValue = [p \in Procs |-> Null]
    /\ ANU_parent = [p \in Procs |-> Null]
    /\ ANU_node = [p \in Procs |-> Null]
    /\ ANU_prev = [p \in Procs |-> Null]
    /\ ANU_damaged = [p \in Procs |-> Null]
    /\ AUL_parent = [p \in Procs |-> Null]
    /\ AUL_node = [p \in Procs |-> Null]
    /\ NC_node = [p \in Procs |-> Null]
    /\ FHR_node = [p \in Procs |-> Null]
    /\ FHR_condition = [p \in Procs |-> Null]
    /\ FHR_nParent = [p \in Procs |-> Null]
    /\ FH_node = [p \in Procs |-> Null]
    /\ REB_nParent = [p \in Procs |-> Null]
    /\ REB_n = [p \in Procs |-> Null]
    /\ REB_nL = [p \in Procs |-> Null]
    /\ REB_nR = [p \in Procs |-> Null]
    /\ REBR_nParent = [p \in Procs |-> Null]
    /\ REBR_n = [p \in Procs |-> Null]
    /\ REBR_nL = [p \in Procs |-> Null]
    /\ REBR_nLR = [p \in Procs |-> Null]
    /\ REBL_nParent = [p \in Procs |-> Null]
    /\ REBL_n = [p \in Procs |-> Null]
    /\ REBL_nR = [p \in Procs |-> Null]
    /\ REBL_nRL = [p \in Procs |-> Null]
    /\ ROTR_nParent = [p \in Procs |-> Null]
    /\ ROTR_n = [p \in Procs |-> Null]
    /\ ROTR_nL = [p \in Procs |-> Null]
    /\ ROTR_nLR = [p \in Procs |-> Null]
    /\ ROTL_nParent = [p \in Procs |-> Null]
    /\ ROTL_n = [p \in Procs |-> Null]
    /\ ROTL_nR = [p \in Procs |-> Null]
    /\ ROTL_nRL = [p \in Procs |-> Null]
    /\ ROTROL_nParent = [p \in Procs |-> Null]
    /\ ROTROL_n = [p \in Procs |-> Null]
    /\ ROTROL_nL = [p \in Procs |-> Null]
    /\ ROTROL_nLR = [p \in Procs |-> Null]
    /\ ROTLOR_nParent = [p \in Procs |-> Null]
    /\ ROTLOR_n = [p \in Procs |-> Null]
    /\ ROTLOR_nR = [p \in Procs |-> Null]
    /\ ROTLOR_nRL = [p \in Procs |-> Null]
    /\ AU_success = [p \in Procs |-> 0]
    /\ REBR_hR0 = [p \in Procs |-> 0]
    /\ REBR_hLL0 = [p \in Procs |-> 0]
    /\ REBR_hLR0 = [p \in Procs |-> 0]
    /\ REBL_hL0 = [p \in Procs |-> 0]
    /\ REBL_hRR0 = [p \in Procs |-> 0]
    /\ REBL_hRL0 = [p \in Procs |-> 0]
    /\ ROTR_hR = [p \in Procs |-> 0]
    /\ ROTR_hLL = [p \in Procs |-> 0]
    /\ ROTR_hLR = [p \in Procs |-> 0]
    /\ ROTL_hL = [p \in Procs |-> 0]
    /\ ROTL_hRL = [p \in Procs |-> 0]
    /\ ROTL_hRR = [p \in Procs |-> 0]
    /\ ROTROL_hR = [p \in Procs |-> 0]
    /\ ROTROL_hLL = [p \in Procs |-> 0]
    /\ ROTROL_hLRL = [p \in Procs |-> 0]
    /\ ROTLOR_hL = [p \in Procs |-> 0]
    /\ ROTLOR_hRR = [p \in Procs |-> 0]
    /\ ROTLOR_hRLR = [p \in Procs |-> 0]

\* ======================================================================
\* ACTIONS
\* ======================================================================

writeInv_erase(p, k) ==
    /\ pc[p] = 1
    /\ U_k' = [U_k EXCEPT ![p] = k]
    /\ U_newValue' = [U_newValue EXCEPT ![p] = Null]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 2)]
    /\ pc' = [pc EXCEPT ![p] = 10]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

writeInv_insert(p, k) ==
    /\ pc[p] = 1
    /\ U_k' = [U_k EXCEPT ![p] = k]
    /\ U_newValue' = [U_newValue EXCEPT ![p] = k]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 2)]
    /\ pc' = [pc EXCEPT ![p] = 10]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

writeResp(p) ==
    /\ pc[p] = 2
    /\ pc' = [pc EXCEPT ![p] = 0]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

u0_emptyErase(p) ==
    /\ pc[p] = 10
    /\ rite[0] = Null
    /\ U_newValue[p] = Null
    /\ ret' = [ret EXCEPT ![p] = Null]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

u0_emptyInsert(p) ==
    /\ pc[p] = 10
    /\ rite[0] = Null
    /\ U_newValue[p] # Null
    /\ pc' = [pc EXCEPT ![p] = 12]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

u0_navigate(p) ==
    /\ pc[p] = 10
    /\ rite[0] # Null
    /\ ver[rite[0]] # Shrinking
    /\ ver[rite[0]] # Unlinked
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 15)]
    /\ AU_k' = [AU_k EXCEPT ![p] = U_k[p]]
    /\ AU_newValue' = [AU_newValue EXCEPT ![p] = U_newValue[p]]
    /\ AU_parent' = [AU_parent EXCEPT ![p] = 0]
    /\ AU_node' = [AU_node EXCEPT ![p] = rite[0]]
    /\ AU_nodeVer' = [AU_nodeVer EXCEPT ![p] = ver[rite[0]]]
    /\ pc' = [pc EXCEPT ![p] = 20]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_dirToC, AU_child,
                   AU_success, AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged,
                   AUL_parent, AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node,
                   REB_nParent, REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL,
                   REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR,
                   REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL,
                   ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL,
                   ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL,
                   ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL,
                   ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

uLock0(p) ==
    /\ pc[p] = 12
    /\ locked[0] = -1 \/ locked[0] = p
    /\ locked' = [locked EXCEPT ![0] = p]
    /\ pc' = [pc EXCEPT ![p] = 13]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

u2_writeLeaf(p) ==
    /\ pc[p] = 13
    /\ rite[0] = Null
    /\ LET ua == UnusedAddr
       IN
       /\ key' = [key EXCEPT ![ua] = U_k[p]]
       /\ val' = [val EXCEPT ![ua] = U_newValue[p]]
       /\ parent' = [parent EXCEPT ![ua] = 0]
       /\ height' = [height EXCEPT ![ua] = 1, ![0] = 2]
       /\ left' = [left EXCEPT ![ua] = Null]
       /\ rite' = [rite EXCEPT ![0] = ua, ![ua] = Null]
       /\ ver' = [ver EXCEPT ![ua] = 0]
       /\ locked' = [locked EXCEPT ![0] = -1]
       /\ ret' = [ret EXCEPT ![p] = Null]
       /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
       /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
       /\ UNCHANGED <<auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

u2_retry(p) ==
    /\ pc[p] = 13
    /\ rite[0] # Null
    /\ locked' = [locked EXCEPT ![0] = -1]
    /\ pc' = [pc EXCEPT ![p] = 10]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

u4(p) ==
    /\ pc[p] = 15
    /\ pc' = [pc EXCEPT ![p] = IF ret[p] # Retry THEN 16 ELSE 10]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

u5(p) ==
    /\ pc[p] = 16
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

au0(p) ==
    /\ pc[p] = 20
    /\ pc' = [pc EXCEPT ![p] = IF key[AU_node[p]] = AU_k[p] THEN 39 ELSE 22]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

au1(p) ==
    /\ pc[p] = 39
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 40)]
    /\ ANU_newValue' = [ANU_newValue EXCEPT ![p] = AU_newValue[p]]
    /\ ANU_parent' = [ANU_parent EXCEPT ![p] = AU_parent[p]]
    /\ ANU_node' = [ANU_node EXCEPT ![p] = AU_node[p]]
    /\ pc' = [pc EXCEPT ![p] = 50]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node, FHR_condition,
                   FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR, REBR_nParent,
                   REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent,
                   REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent,
                   ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent,
                   ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent,
                   ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent,
                   ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

auT3(p) ==
    /\ pc[p] = 40
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

au2(p) ==
    /\ pc[p] = 22
    /\ AU_dirToC' = [AU_dirToC EXCEPT ![p] = IF AU_k[p] < key[AU_node[p]] THEN DirectionLeft ELSE DirectionRite]
    /\ pc' = [pc EXCEPT ![p] = 23]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

au3(p) ==
    /\ pc[p] = 23
    /\ AU_child' = [AU_child EXCEPT ![p] = Child(AU_node[p], AU_dirToC[p])]
    /\ pc' = [pc EXCEPT ![p] = IF ver[AU_node[p]] # AU_nodeVer[p] THEN 24 ELSE 25]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

au4(p) ==
    /\ pc[p] = 24
    /\ ret' = [ret EXCEPT ![p] = Retry]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

au5_childNull_erase(p) ==
    /\ pc[p] = 25
    /\ AU_child[p] = Null
    /\ AU_newValue[p] = Null
    /\ ret' = [ret EXCEPT ![p] = Null]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

au5_childNull_insert(p) ==
    /\ pc[p] = 25
    /\ AU_child[p] = Null
    /\ AU_newValue[p] # Null
    /\ pc' = [pc EXCEPT ![p] = 27]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

au5_childNotNull_navigate(p) ==
    /\ pc[p] = 25
    /\ AU_child[p] # Null
    /\ ver[AU_child[p]] # Shrinking
    /\ ver[AU_child[p]] # Unlinked
    /\ ver[AU_node[p]] = AU_nodeVer[p]
    /\ auSaveStack' = [auSaveStack EXCEPT ![p] = Append(Append(Append(Append(Append(Append(@, AU_k[p]), AU_newValue[p]), AU_parent[p]), AU_node[p]), AU_nodeVer[p]), AU_dirToC[p])]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 37)]
    /\ AU_parent' = [AU_parent EXCEPT ![p] = AU_node[p]]
    /\ AU_nodeVer' = [AU_nodeVer EXCEPT ![p] = ver[AU_child[p]]]
    /\ AU_node' = [AU_node EXCEPT ![p] = AU_child[p]]
    /\ pc' = [pc EXCEPT ![p] = 20]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, U_k, U_newValue, AU_k, AU_newValue, AU_dirToC,
                   AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev,
                   ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent,
                   FH_node, REB_nParent, REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n,
                   REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n,
                   REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n,
                   ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n,
                   ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n,
                   ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n,
                   ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

au5_childNotNull_shrinking(p) ==
    /\ pc[p] = 25
    /\ AU_child[p] # Null
    /\ ver[AU_child[p]] = Shrinking \/ ver[AU_child[p]] = Unlinked
    /\ pc' = [pc EXCEPT ![p] = 23]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

au5_childNotNull_verStale(p) ==
    /\ pc[p] = 25
    /\ AU_child[p] # Null
    /\ ver[AU_child[p]] # Shrinking
    /\ ver[AU_child[p]] # Unlinked
    /\ ver[AU_node[p]] # AU_nodeVer[p]
    /\ ret' = [ret EXCEPT ![p] = Retry]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

auLock0(p) ==
    /\ pc[p] = 27
    /\ locked[AU_node[p]] = -1 \/ locked[AU_node[p]] = p
    /\ locked' = [locked EXCEPT ![AU_node[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 28]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

au7(p) ==
    /\ pc[p] = 28
    /\ pc' = [pc EXCEPT ![p] = IF ver[AU_node[p]] # AU_nodeVer[p] THEN 29 ELSE 30]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

au8(p) ==
    /\ pc[p] = 29
    /\ ret' = [ret EXCEPT ![p] = Retry]
    /\ locked' = [locked EXCEPT ![AU_node[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

au9_childAppeared(p) ==
    /\ pc[p] = 30
    /\ Child(AU_node[p], AU_dirToC[p]) # Null
    /\ AU_success' = [AU_success EXCEPT ![p] = 0]
    /\ AU_damaged' = [AU_damaged EXCEPT ![p] = Null]
    /\ pc' = [pc EXCEPT ![p] = 32]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

au9_writeLeaf(p) ==
    /\ pc[p] = 30
    /\ Child(AU_node[p], AU_dirToC[p]) = Null
    /\ LET ua == UnusedAddr
       IN
       /\ key' = [key EXCEPT ![ua] = AU_k[p]]
       /\ val' = [val EXCEPT ![ua] = AU_newValue[p]]
       /\ parent' = [parent EXCEPT ![ua] = AU_node[p]]
       /\ height' = [height EXCEPT ![ua] = 1]
       /\ ver' = [ver EXCEPT ![ua] = 0]
       /\ left' = [left EXCEPT ![ua] = Null,
                         ![AU_node[p]] = IF AU_k[p] < key[AU_node[p]] THEN ua ELSE left[AU_node[p]]]
       /\ rite' = [rite EXCEPT ![ua] = Null,
                         ![AU_node[p]] = IF AU_k[p] < key[AU_node[p]] THEN rite[AU_node[p]] ELSE ua]
       /\ AU_success' = [AU_success EXCEPT ![p] = 1]
       /\ retStack' = [retStack EXCEPT ![p] = Append(@, 31)]
       /\ FH_node' = [FH_node EXCEPT ![p] = AU_node[p]]
       /\ pc' = [pc EXCEPT ![p] = 120]
       /\ UNCHANGED <<locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

auT1(p) ==
    /\ pc[p] = 31
    /\ AU_damaged' = [AU_damaged EXCEPT ![p] = ret[p]]
    /\ pc' = [pc EXCEPT ![p] = 32]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

auT2(p) ==
    /\ pc[p] = 32
    /\ locked' = [locked EXCEPT ![AU_node[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = IF AU_success[p] = 1 THEN 33 ELSE 23]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

au10(p) ==
    /\ pc[p] = 33
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 34)]
    /\ FHR_node' = [FHR_node EXCEPT ![p] = AU_damaged[p]]
    /\ pc' = [pc EXCEPT ![p] = 100]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

au11(p) ==
    /\ pc[p] = 34
    /\ ret' = [ret EXCEPT ![p] = Null]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

au14(p) ==
    /\ pc[p] = 37
    /\ LET stk == auSaveStack[p]
       IN
       LET L == Len(stk)
       IN
       /\ AU_k' = [AU_k EXCEPT ![p] = stk[L - 5]]
       /\ AU_newValue' = [AU_newValue EXCEPT ![p] = stk[L - 4]]
       /\ AU_parent' = [AU_parent EXCEPT ![p] = stk[L - 3]]
       /\ AU_node' = [AU_node EXCEPT ![p] = stk[L - 2]]
       /\ AU_nodeVer' = [AU_nodeVer EXCEPT ![p] = stk[L - 1]]
       /\ AU_dirToC' = [AU_dirToC EXCEPT ![p] = stk[L]]
       /\ auSaveStack' = [auSaveStack EXCEPT ![p] = SubSeq(stk, 1, L - 6)]
       /\ pc' = [pc EXCEPT ![p] = IF ret[p] # Retry THEN 38 ELSE 23]
       /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, U_k, U_newValue, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

au15(p) ==
    /\ pc[p] = 38
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

anu0_alreadyNull(p) ==
    /\ pc[p] = 50
    /\ ANU_newValue[p] = Null
    /\ val[ANU_node[p]] = Null
    /\ ret' = [ret EXCEPT ![p] = Null]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anu0_continue(p) ==
    /\ pc[p] = 50
    /\ ANU_newValue[p] # Null \/ val[ANU_node[p]] # Null
    /\ pc' = [pc EXCEPT ![p] = 51]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anu1_unlinkPath(p) ==
    /\ pc[p] = 51
    /\ ANU_newValue[p] = Null
    /\ left[ANU_node[p]] = Null \/ rite[ANU_node[p]] = Null
    /\ pc' = [pc EXCEPT ![p] = 52]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anu1_updatePath(p) ==
    /\ pc[p] = 51
    /\ ANU_newValue[p] # Null \/ (left[ANU_node[p]] # Null /\ rite[ANU_node[p]] # Null)
    /\ pc' = [pc EXCEPT ![p] = 66]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anuLock0(p) ==
    /\ pc[p] = 52
    /\ locked[ANU_parent[p]] = -1 \/ locked[ANU_parent[p]] = p
    /\ locked' = [locked EXCEPT ![ANU_parent[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 53]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

anu2(p) ==
    /\ pc[p] = 53
    /\ pc' = [pc EXCEPT ![p] = IF ver[ANU_parent[p]] = Unlinked \/ parent[ANU_node[p]] # ANU_parent[p] THEN 54 ELSE 55]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anu3(p) ==
    /\ pc[p] = 54
    /\ ret' = [ret EXCEPT ![p] = Retry]
    /\ locked' = [locked EXCEPT ![ANU_parent[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anuLock1(p) ==
    /\ pc[p] = 55
    /\ locked[ANU_node[p]] = -1 \/ locked[ANU_node[p]] = p
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 56]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

anu4(p) ==
    /\ pc[p] = 56
    /\ ANU_prev' = [ANU_prev EXCEPT ![p] = val[ANU_node[p]]]
    /\ pc' = [pc EXCEPT ![p] = IF val[ANU_node[p]] = Null THEN 57 ELSE 58]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

anu5(p) ==
    /\ pc[p] = 57
    /\ ret' = [ret EXCEPT ![p] = ANU_prev[p]]
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 72]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anu5b(p) ==
    /\ pc[p] = 72
    /\ locked' = [locked EXCEPT ![ANU_parent[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anu7(p) ==
    /\ pc[p] = 58
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 59)]
    /\ AUL_parent' = [AUL_parent EXCEPT ![p] = ANU_parent[p]]
    /\ AUL_node' = [AUL_node EXCEPT ![p] = ANU_node[p]]
    /\ pc' = [pc EXCEPT ![p] = 80]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anuT0_success(p) ==
    /\ pc[p] = 59
    /\ ret[p] = 111
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = -1]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 63)]
    /\ FH_node' = [FH_node EXCEPT ![p] = ANU_parent[p]]
    /\ pc' = [pc EXCEPT ![p] = 120]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anuT0_fail(p) ==
    /\ pc[p] = 59
    /\ ret[p] # 111
    /\ ret' = [ret EXCEPT ![p] = Retry]
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 73]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anu8b(p) ==
    /\ pc[p] = 73
    /\ locked' = [locked EXCEPT ![ANU_parent[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anu12(p) ==
    /\ pc[p] = 63
    /\ ANU_damaged' = [ANU_damaged EXCEPT ![p] = ret[p]]
    /\ locked' = [locked EXCEPT ![ANU_parent[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 64]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anu13(p) ==
    /\ pc[p] = 64
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 65)]
    /\ FHR_node' = [FHR_node EXCEPT ![p] = ANU_damaged[p]]
    /\ pc' = [pc EXCEPT ![p] = 100]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anu14(p) ==
    /\ pc[p] = 65
    /\ ret' = [ret EXCEPT ![p] = ANU_prev[p]]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

anuLock2(p) ==
    /\ pc[p] = 66
    /\ locked[ANU_node[p]] = -1 \/ locked[ANU_node[p]] = p
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 67]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

anu15(p) ==
    /\ pc[p] = 67
    /\ pc' = [pc EXCEPT ![p] = IF ver[ANU_node[p]] = Unlinked THEN 68 ELSE 69]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anu16(p) ==
    /\ pc[p] = 68
    /\ ret' = [ret EXCEPT ![p] = Retry]
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anu17(p) ==
    /\ pc[p] = 69
    /\ ANU_prev' = [ANU_prev EXCEPT ![p] = val[ANU_node[p]]]
    /\ pc' = [pc EXCEPT ![p] = IF ANU_newValue[p] = Null /\ (left[ANU_node[p]] = Null \/ rite[ANU_node[p]] = Null) THEN 70 ELSE 71]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

anu18(p) ==
    /\ pc[p] = 70
    /\ ret' = [ret EXCEPT ![p] = Retry]
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

anu19(p) ==
    /\ pc[p] = 71
    /\ val' = [val EXCEPT ![ANU_node[p]] = ANU_newValue[p]]
    /\ ret' = [ret EXCEPT ![p] = ANU_prev[p]]
    /\ locked' = [locked EXCEPT ![ANU_node[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, height, parent, left, rite, auSaveStack,
                   U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node, AU_nodeVer,
                   AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent, ANU_node,
                   ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node, FHR_condition,
                   FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR, REBR_nParent,
                   REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent,
                   REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent,
                   ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent,
                   ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent,
                   ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent,
                   ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

attemptUnlink(p) ==
    /\ pc[p] = 80
    /\ left[AUL_parent[p]] = AUL_node[p] \/ rite[AUL_parent[p]] = AUL_node[p]
    /\ left[AUL_node[p]] = Null \/ rite[AUL_node[p]] = Null
    /\ LET splice == IF left[AUL_node[p]] # Null THEN left[AUL_node[p]] ELSE rite[AUL_node[p]]
       IN
       /\ left' = [left EXCEPT ![AUL_parent[p]] = IF left[AUL_parent[p]] = AUL_node[p] THEN splice ELSE @]
       /\ rite' = [rite EXCEPT ![AUL_parent[p]] = IF rite[AUL_parent[p]] = AUL_node[p] THEN splice ELSE @]
       /\ parent' = [parent EXCEPT ![IF splice # Null THEN splice ELSE AUL_node[p]] = IF splice # Null THEN AUL_parent[p] ELSE @]
       /\ ver' = [ver EXCEPT ![AUL_node[p]] = Unlinked]
       /\ val' = [val EXCEPT ![AUL_node[p]] = Null]
       /\ ret' = [ret EXCEPT ![p] = 111]
       /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
       /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
       /\ UNCHANGED <<key, height, locked, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

attemptUnlink_notChild(p) ==
    /\ pc[p] = 80
    /\ left[AUL_parent[p]] # AUL_node[p]
    /\ rite[AUL_parent[p]] # AUL_node[p]
    /\ ret' = [ret EXCEPT ![p] = 110]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

attemptUnlink_twoChildren(p) ==
    /\ pc[p] = 80
    /\ left[AUL_parent[p]] = AUL_node[p] \/ rite[AUL_parent[p]] = AUL_node[p]
    /\ left[AUL_node[p]] # Null
    /\ rite[AUL_node[p]] # Null
    /\ ret' = [ret EXCEPT ![p] = 110]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

nodeCondition(p) ==
    /\ pc[p] = 90
    /\ LET n == NC_node[p]
       IN
       LET hL == NullSafeHeight(left[n])
       IN
       LET hR == NullSafeHeight(rite[n])
       IN
       LET bal == hL - hR
       IN
       /\ ret' = [ret EXCEPT ![p] =
            IF (left[n] = Null \/ rite[n] = Null) /\ val[n] = Null THEN UnlinkReq
            ELSE IF bal < -1 \/ bal > 1 THEN RebalanceReq
            ELSE IF height[n] # MaxPlusOne(hL, hR) THEN MaxPlusOne(hL, hR)
            ELSE NoRepair]
       /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
       /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
       /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

fhr0_null(p) ==
    /\ pc[p] = 100
    /\ FHR_node[p] = Null
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhr0_notNull(p) ==
    /\ pc[p] = 100
    /\ FHR_node[p] # Null
    /\ pc' = [pc EXCEPT ![p] = IF parent[FHR_node[p]] = Null THEN 101 ELSE 102]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

fhr1(p) ==
    /\ pc[p] = 101
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhr2(p) ==
    /\ pc[p] = 102
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 103)]
    /\ NC_node' = [NC_node EXCEPT ![p] = FHR_node[p]]
    /\ pc' = [pc EXCEPT ![p] = 90]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

fhrT1(p) ==
    /\ pc[p] = 103
    /\ FHR_condition' = [FHR_condition EXCEPT ![p] = ret[p]]
    /\ pc' = [pc EXCEPT ![p] = IF ret[p] = NoRepair \/ ver[FHR_node[p]] = Unlinked THEN 104 ELSE 105]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhr3(p) ==
    /\ pc[p] = 104
    /\ FHR_node' = [FHR_node EXCEPT ![p] = parent[FHR_node[p]]]
    /\ pc' = [pc EXCEPT ![p] = 100]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhr4(p) ==
    /\ pc[p] = 105
    /\ pc' = [pc EXCEPT ![p] = IF FHR_condition[p] # UnlinkReq /\ FHR_condition[p] # RebalanceReq THEN 106 ELSE 109]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

fhrLock0(p) ==
    /\ pc[p] = 106
    /\ locked[FHR_node[p]] = -1 \/ locked[FHR_node[p]] = p
    /\ locked' = [locked EXCEPT ![FHR_node[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 107]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhr5(p) ==
    /\ pc[p] = 107
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 108)]
    /\ FH_node' = [FH_node EXCEPT ![p] = FHR_node[p]]
    /\ pc' = [pc EXCEPT ![p] = 120]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

fhrT0(p) ==
    /\ pc[p] = 108
    /\ locked' = [locked EXCEPT ![FHR_node[p]] = -1]
    /\ FHR_node' = [FHR_node EXCEPT ![p] = ret[p]]
    /\ pc' = [pc EXCEPT ![p] = 100]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

fhr6(p) ==
    /\ pc[p] = 109
    /\ FHR_nParent' = [FHR_nParent EXCEPT ![p] = parent[FHR_node[p]]]
    /\ pc' = [pc EXCEPT ![p] = 110]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhrLock1(p) ==
    /\ pc[p] = 110
    /\ locked[FHR_nParent[p]] = -1 \/ locked[FHR_nParent[p]] = p
    /\ locked' = [locked EXCEPT ![FHR_nParent[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 111]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhr6b_valid(p) ==
    /\ pc[p] = 111
    /\ ver[FHR_nParent[p]] # Unlinked
    /\ parent[FHR_node[p]] = FHR_nParent[p]
    /\ pc' = [pc EXCEPT ![p] = 112]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

fhr6b_invalid(p) ==
    /\ pc[p] = 111
    /\ ver[FHR_nParent[p]] = Unlinked \/ parent[FHR_node[p]] # FHR_nParent[p]
    /\ locked' = [locked EXCEPT ![FHR_nParent[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 100]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhrLock2(p) ==
    /\ pc[p] = 112
    /\ locked[FHR_node[p]] = -1 \/ locked[FHR_node[p]] = p
    /\ locked' = [locked EXCEPT ![FHR_node[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 113]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fhr7(p) ==
    /\ pc[p] = 113
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 114)]
    /\ REB_nParent' = [REB_nParent EXCEPT ![p] = FHR_nParent[p]]
    /\ REB_n' = [REB_n EXCEPT ![p] = FHR_node[p]]
    /\ pc' = [pc EXCEPT ![p] = 130]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

fhr8(p) ==
    /\ pc[p] = 114
    /\ locked' = [locked EXCEPT ![FHR_node[p]] = -1]
    /\ FHR_node' = [FHR_node EXCEPT ![p] = ret[p]]
    /\ pc' = [pc EXCEPT ![p] = 115]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

fhr9(p) ==
    /\ pc[p] = 115
    /\ locked' = [locked EXCEPT ![FHR_nParent[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 100]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

fixHeight(p) ==
    /\ pc[p] = 120
    /\ LET n == FH_node[p]
       IN
       LET hL == NullSafeHeight(left[n])
       IN
       LET hR == NullSafeHeight(rite[n])
       IN
       LET bal == hL - hR
       IN
       LET isUnlink == (left[n] = Null \/ rite[n] = Null) /\ val[n] = Null
       IN
       LET isUnbal == bal < -1 \/ bal > 1
       IN
       LET hMatch == height[n] = MaxPlusOne(hL, hR)
       IN
       /\ ret' = [ret EXCEPT ![p] =
                 IF isUnlink THEN n
                 ELSE IF isUnbal THEN n
                 ELSE IF hMatch THEN Null
                 ELSE parent[n]]
       /\ height' = [height EXCEPT ![n] =
                 IF isUnlink THEN @
                 ELSE IF isUnbal THEN @
                 ELSE IF hMatch THEN @
                 ELSE MaxPlusOne(hL, hR)]
       /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
       /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
       /\ UNCHANGED <<ver, key, val, parent, left, rite, locked,
                   auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

reb0(p) ==
    /\ pc[p] = 130
    /\ REB_nL' = [REB_nL EXCEPT ![p] = left[REB_n[p]]]
    /\ REB_nR' = [REB_nR EXCEPT ![p] = rite[REB_n[p]]]
    /\ pc' = [pc EXCEPT ![p] = IF (left[REB_n[p]] = Null \/ rite[REB_n[p]] = Null) /\ val[REB_n[p]] = Null THEN 131 ELSE 135]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

reb_unlink(p) ==
    /\ pc[p] = 131
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 132)]
    /\ AUL_parent' = [AUL_parent EXCEPT ![p] = REB_nParent[p]]
    /\ AUL_node' = [AUL_node EXCEPT ![p] = REB_n[p]]
    /\ pc' = [pc EXCEPT ![p] = 80]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebT0_success(p) ==
    /\ pc[p] = 132
    /\ ret[p] = 111
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 141)]
    /\ FH_node' = [FH_node EXCEPT ![p] = REB_nParent[p]]
    /\ pc' = [pc EXCEPT ![p] = 120]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rebT0_fail(p) ==
    /\ pc[p] = 132
    /\ ret[p] # 111
    /\ ret' = [ret EXCEPT ![p] = REB_n[p]]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

reb3_rebalToRite(p) ==
    /\ pc[p] = 135
    /\ NullSafeHeight(REB_nL[p]) - NullSafeHeight(REB_nR[p]) > 1
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 137)]
    /\ REBR_nParent' = [REBR_nParent EXCEPT ![p] = REB_nParent[p]]
    /\ REBR_n' = [REBR_n EXCEPT ![p] = REB_n[p]]
    /\ REBR_nL' = [REBR_nL EXCEPT ![p] = REB_nL[p]]
    /\ REBR_hR0' = [REBR_hR0 EXCEPT ![p] = NullSafeHeight(REB_nR[p])]
    /\ pc' = [pc EXCEPT ![p] = 150]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n,
                   REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n,
                   ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n,
                   ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n,
                   ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n,
                   ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

reb3_rebalToLeft(p) ==
    /\ pc[p] = 135
    /\ NullSafeHeight(REB_nL[p]) - NullSafeHeight(REB_nR[p]) < -1
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 139)]
    /\ REBL_nParent' = [REBL_nParent EXCEPT ![p] = REB_nParent[p]]
    /\ REBL_n' = [REBL_n EXCEPT ![p] = REB_n[p]]
    /\ REBL_nR' = [REBL_nR EXCEPT ![p] = REB_nR[p]]
    /\ REBL_hL0' = [REBL_hL0 EXCEPT ![p] = NullSafeHeight(REB_nL[p])]
    /\ pc' = [pc EXCEPT ![p] = 170]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n,
                   ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n,
                   ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n,
                   ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n,
                   ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

reb3_heightFix(p) ==
    /\ pc[p] = 135
    /\ NullSafeHeight(REB_nL[p]) - NullSafeHeight(REB_nR[p]) >= -1
    /\ NullSafeHeight(REB_nL[p]) - NullSafeHeight(REB_nR[p]) <= 1
    /\ MaxPlusOne(NullSafeHeight(REB_nL[p]), NullSafeHeight(REB_nR[p])) # height[REB_n[p]]
    /\ height' = [height EXCEPT ![REB_n[p]] = MaxPlusOne(NullSafeHeight(REB_nL[p]), NullSafeHeight(REB_nR[p]))]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 141)]
    /\ FH_node' = [FH_node EXCEPT ![p] = REB_nParent[p]]
    /\ pc' = [pc EXCEPT ![p] = 120]
    /\ UNCHANGED <<ver, key, val, parent, left, rite, locked,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

reb3_noRepair(p) ==
    /\ pc[p] = 135
    /\ NullSafeHeight(REB_nL[p]) - NullSafeHeight(REB_nR[p]) >= -1
    /\ NullSafeHeight(REB_nL[p]) - NullSafeHeight(REB_nR[p]) <= 1
    /\ MaxPlusOne(NullSafeHeight(REB_nL[p]), NullSafeHeight(REB_nR[p])) = height[REB_n[p]]
    /\ ret' = [ret EXCEPT ![p] = Null]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

reb_return(p) ==
    /\ pc[p] = 137 \/ pc[p] = 139 \/ pc[p] = 141
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebr0Lock0(p) ==
    /\ pc[p] = 150
    /\ locked[REBR_nL[p]] = -1 \/ locked[REBR_nL[p]] = p
    /\ locked' = [locked EXCEPT ![REBR_nL[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 151]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebr1(p) ==
    /\ pc[p] = 151
    /\ pc' = [pc EXCEPT ![p] = IF height[REBR_nL[p]] - REBR_hR0[p] <= 1 THEN 152 ELSE 153]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebr2(p) ==
    /\ pc[p] = 152
    /\ ret' = [ret EXCEPT ![p] = REBR_n[p]]
    /\ locked' = [locked EXCEPT ![REBR_nL[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebr_simpleRotate(p) ==
    /\ pc[p] = 153
    /\ NullSafeHeight(left[REBR_nL[p]]) >= NullSafeHeight(rite[REBR_nL[p]])
    /\ REBR_nLR' = [REBR_nLR EXCEPT ![p] = rite[REBR_nL[p]]]
    /\ REBR_hLL0' = [REBR_hLL0 EXCEPT ![p] = NullSafeHeight(left[REBR_nL[p]])]
    /\ REBR_hLR0' = [REBR_hLR0 EXCEPT ![p] = NullSafeHeight(rite[REBR_nL[p]])]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 155)]
    /\ ROTR_nParent' = [ROTR_nParent EXCEPT ![p] = REBR_nParent[p]]
    /\ ROTR_n' = [ROTR_n EXCEPT ![p] = REBR_n[p]]
    /\ ROTR_nL' = [ROTR_nL EXCEPT ![p] = REBR_nL[p]]
    /\ ROTR_hR' = [ROTR_hR EXCEPT ![p] = REBR_hR0[p]]
    /\ ROTR_hLL' = [ROTR_hLL EXCEPT ![p] = NullSafeHeight(left[REBR_nL[p]])]
    /\ ROTR_nLR' = [ROTR_nLR EXCEPT ![p] = rite[REBR_nL[p]]]
    /\ ROTR_hLR' = [ROTR_hLR EXCEPT ![p] = NullSafeHeight(rite[REBR_nL[p]])]
    /\ pc' = [pc EXCEPT ![p] = 190]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBL_nParent,
                   REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTL_nParent,
                   ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent,
                   ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent,
                   ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebr_needInnerCheck(p) ==
    /\ pc[p] = 153
    /\ NullSafeHeight(left[REBR_nL[p]]) < NullSafeHeight(rite[REBR_nL[p]])
    /\ REBR_nLR' = [REBR_nLR EXCEPT ![p] = rite[REBR_nL[p]]]
    /\ REBR_hLL0' = [REBR_hLL0 EXCEPT ![p] = NullSafeHeight(left[REBR_nL[p]])]
    /\ REBR_hLR0' = [REBR_hLR0 EXCEPT ![p] = NullSafeHeight(rite[REBR_nL[p]])]
    /\ pc' = [pc EXCEPT ![p] = 156]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebr4(p) ==
    /\ pc[p] = 155
    /\ locked' = [locked EXCEPT ![REBR_nL[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rebrLock1(p) ==
    /\ pc[p] = 156
    /\ locked[REBR_nLR[p]] = -1 \/ locked[REBR_nLR[p]] = p
    /\ locked' = [locked EXCEPT ![REBR_nLR[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 157]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebr5_simpleRotate(p) ==
    /\ pc[p] = 157
    /\ REBR_hLL0[p] >= height[REBR_nLR[p]]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 159)]
    /\ ROTR_nParent' = [ROTR_nParent EXCEPT ![p] = REBR_nParent[p]]
    /\ ROTR_n' = [ROTR_n EXCEPT ![p] = REBR_n[p]]
    /\ ROTR_nL' = [ROTR_nL EXCEPT ![p] = REBR_nL[p]]
    /\ ROTR_hR' = [ROTR_hR EXCEPT ![p] = REBR_hR0[p]]
    /\ ROTR_hLL' = [ROTR_hLL EXCEPT ![p] = REBR_hLL0[p]]
    /\ ROTR_nLR' = [ROTR_nLR EXCEPT ![p] = REBR_nLR[p]]
    /\ ROTR_hLR' = [ROTR_hLR EXCEPT ![p] = height[REBR_nLR[p]]]
    /\ pc' = [pc EXCEPT ![p] = 190]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebr5_doubleCheck(p) ==
    /\ pc[p] = 157
    /\ REBR_hLL0[p] < height[REBR_nLR[p]]
    /\ pc' = [pc EXCEPT ![p] = 161]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebr_afterRotUnlockNLR(p) ==
    /\ pc[p] = 159
    /\ locked' = [locked EXCEPT ![REBR_nLR[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 160]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebr_afterRotUnlockNL(p) ==
    /\ pc[p] = 160
    /\ locked' = [locked EXCEPT ![REBR_nL[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rebr_doubleRot(p) ==
    /\ pc[p] = 161
    /\ REBR_hLL0[p] - NullSafeHeight(left[REBR_nLR[p]]) >= -1
    /\ REBR_hLL0[p] - NullSafeHeight(left[REBR_nLR[p]]) <= 1
    /\ ~((REBR_hLL0[p] = 0 \/ NullSafeHeight(left[REBR_nLR[p]]) = 0) /\ val[REBR_nL[p]] = Null)
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 163)]
    /\ ROTROL_nParent' = [ROTROL_nParent EXCEPT ![p] = REBR_nParent[p]]
    /\ ROTROL_n' = [ROTROL_n EXCEPT ![p] = REBR_n[p]]
    /\ ROTROL_nL' = [ROTROL_nL EXCEPT ![p] = REBR_nL[p]]
    /\ ROTROL_hR' = [ROTROL_hR EXCEPT ![p] = REBR_hR0[p]]
    /\ ROTROL_hLL' = [ROTROL_hLL EXCEPT ![p] = REBR_hLL0[p]]
    /\ ROTROL_nLR' = [ROTROL_nLR EXCEPT ![p] = REBR_nLR[p]]
    /\ ROTROL_hLRL' = [ROTROL_hLRL EXCEPT ![p] = NullSafeHeight(left[REBR_nLR[p]])]
    /\ pc' = [pc EXCEPT ![p] = 230]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebr_fallback(p) ==
    /\ pc[p] = 161
    /\ ~(REBR_hLL0[p] - NullSafeHeight(left[REBR_nLR[p]]) >= -1
         /\ REBR_hLL0[p] - NullSafeHeight(left[REBR_nLR[p]]) <= 1
         /\ ~((REBR_hLL0[p] = 0 \/ NullSafeHeight(left[REBR_nLR[p]]) = 0) /\ val[REBR_nL[p]] = Null))
    /\ locked' = [locked EXCEPT ![REBR_nLR[p]] = -1]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 167)]
    /\ REBL_nParent' = [REBL_nParent EXCEPT ![p] = REBR_n[p]]
    /\ REBL_n' = [REBL_n EXCEPT ![p] = REBR_nL[p]]
    /\ REBL_nR' = [REBL_nR EXCEPT ![p] = REBR_nLR[p]]
    /\ REBL_hL0' = [REBL_hL0 EXCEPT ![p] = REBR_hLL0[p]]
    /\ pc' = [pc EXCEPT ![p] = 170]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL,
                   ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL,
                   ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL,
                   ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL,
                   ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebr_afterDoubleRot163(p) ==
    /\ pc[p] = 163
    /\ locked' = [locked EXCEPT ![REBR_nLR[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 164]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebr_afterDoubleRot164(p) ==
    /\ pc[p] = 164
    /\ locked' = [locked EXCEPT ![REBR_nL[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rebr_afterFallback(p) ==
    /\ pc[p] = 167
    /\ locked' = [locked EXCEPT ![REBR_nL[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rebl0Lock0(p) ==
    /\ pc[p] = 170
    /\ locked[REBL_nR[p]] = -1 \/ locked[REBL_nR[p]] = p
    /\ locked' = [locked EXCEPT ![REBL_nR[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 171]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebl1(p) ==
    /\ pc[p] = 171
    /\ pc' = [pc EXCEPT ![p] = IF REBL_hL0[p] - height[REBL_nR[p]] >= -1 THEN 172 ELSE 173]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebl2(p) ==
    /\ pc[p] = 172
    /\ ret' = [ret EXCEPT ![p] = REBL_n[p]]
    /\ locked' = [locked EXCEPT ![REBL_nR[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent, AU_node,
                   AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue, ANU_parent,
                   ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node, FHR_node,
                   FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL, REB_nR,
                   REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0, REBR_hLR0,
                   REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebl_simpleRotate(p) ==
    /\ pc[p] = 173
    /\ NullSafeHeight(rite[REBL_nR[p]]) >= NullSafeHeight(left[REBL_nR[p]])
    /\ REBL_nRL' = [REBL_nRL EXCEPT ![p] = left[REBL_nR[p]]]
    /\ REBL_hRR0' = [REBL_hRR0 EXCEPT ![p] = NullSafeHeight(rite[REBL_nR[p]])]
    /\ REBL_hRL0' = [REBL_hRL0 EXCEPT ![p] = NullSafeHeight(left[REBL_nR[p]])]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 175)]
    /\ ROTL_nParent' = [ROTL_nParent EXCEPT ![p] = REBL_nParent[p]]
    /\ ROTL_n' = [ROTL_n EXCEPT ![p] = REBL_n[p]]
    /\ ROTL_hL' = [ROTL_hL EXCEPT ![p] = REBL_hL0[p]]
    /\ ROTL_nR' = [ROTL_nR EXCEPT ![p] = REBL_nR[p]]
    /\ ROTL_nRL' = [ROTL_nRL EXCEPT ![p] = left[REBL_nR[p]]]
    /\ ROTL_hRL' = [ROTL_hRL EXCEPT ![p] = NullSafeHeight(left[REBL_nR[p]])]
    /\ ROTL_hRR' = [ROTL_hRR EXCEPT ![p] = NullSafeHeight(rite[REBL_nR[p]])]
    /\ pc' = [pc EXCEPT ![p] = 210]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, ROTR_nParent,
                   ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTROL_nParent,
                   ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent,
                   ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebl_needInnerCheck(p) ==
    /\ pc[p] = 173
    /\ NullSafeHeight(rite[REBL_nR[p]]) < NullSafeHeight(left[REBL_nR[p]])
    /\ REBL_nRL' = [REBL_nRL EXCEPT ![p] = left[REBL_nR[p]]]
    /\ REBL_hRR0' = [REBL_hRR0 EXCEPT ![p] = NullSafeHeight(rite[REBL_nR[p]])]
    /\ REBL_hRL0' = [REBL_hRL0 EXCEPT ![p] = NullSafeHeight(left[REBL_nR[p]])]
    /\ pc' = [pc EXCEPT ![p] = 176]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR,
                   ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR,
                   ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL,
                   ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebl4(p) ==
    /\ pc[p] = 175
    /\ locked' = [locked EXCEPT ![REBL_nR[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

reblLock1(p) ==
    /\ pc[p] = 176
    /\ locked[REBL_nRL[p]] = -1 \/ locked[REBL_nRL[p]] = p
    /\ locked' = [locked EXCEPT ![REBL_nRL[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = 177]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebl5_simpleRotate(p) ==
    /\ pc[p] = 177
    /\ REBL_hRR0[p] >= height[REBL_nRL[p]]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 179)]
    /\ ROTL_nParent' = [ROTL_nParent EXCEPT ![p] = REBL_nParent[p]]
    /\ ROTL_n' = [ROTL_n EXCEPT ![p] = REBL_n[p]]
    /\ ROTL_hL' = [ROTL_hL EXCEPT ![p] = REBL_hL0[p]]
    /\ ROTL_nR' = [ROTL_nR EXCEPT ![p] = REBL_nR[p]]
    /\ ROTL_nRL' = [ROTL_nRL EXCEPT ![p] = REBL_nRL[p]]
    /\ ROTL_hRL' = [ROTL_hRL EXCEPT ![p] = height[REBL_nRL[p]]]
    /\ ROTL_hRR' = [ROTL_hRR EXCEPT ![p] = REBL_hRR0[p]]
    /\ pc' = [pc EXCEPT ![p] = 210]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebl5_doubleCheck(p) ==
    /\ pc[p] = 177
    /\ REBL_hRR0[p] < height[REBL_nRL[p]]
    /\ pc' = [pc EXCEPT ![p] = 181]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, retStack, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebl_afterRotUnlockNR(p) ==
    /\ pc[p] = 179
    /\ locked' = [locked EXCEPT ![REBL_nR[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 180]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebl_afterRotUnlockNRL(p) ==
    /\ pc[p] = 180
    /\ locked' = [locked EXCEPT ![REBL_nRL[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rebl_doubleRot(p) ==
    /\ pc[p] = 181
    /\ REBL_hRR0[p] - NullSafeHeight(rite[REBL_nRL[p]]) >= -1
    /\ REBL_hRR0[p] - NullSafeHeight(rite[REBL_nRL[p]]) <= 1
    /\ ~((REBL_hRR0[p] = 0 \/ NullSafeHeight(rite[REBL_nRL[p]]) = 0) /\ val[REBL_nR[p]] = Null)
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 183)]
    /\ ROTLOR_nParent' = [ROTLOR_nParent EXCEPT ![p] = REBL_nParent[p]]
    /\ ROTLOR_n' = [ROTLOR_n EXCEPT ![p] = REBL_n[p]]
    /\ ROTLOR_hL' = [ROTLOR_hL EXCEPT ![p] = REBL_hL0[p]]
    /\ ROTLOR_nR' = [ROTLOR_nR EXCEPT ![p] = REBL_nR[p]]
    /\ ROTLOR_nRL' = [ROTLOR_nRL EXCEPT ![p] = REBL_nRL[p]]
    /\ ROTLOR_hRR' = [ROTLOR_hRR EXCEPT ![p] = REBL_hRR0[p]]
    /\ ROTLOR_hRLR' = [ROTLOR_hRLR EXCEPT ![p] = NullSafeHeight(rite[REBL_nRL[p]])]
    /\ pc' = [pc EXCEPT ![p] = 250]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   locked, ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL>>

rebl_fallback(p) ==
    /\ pc[p] = 181
    /\ ~(REBL_hRR0[p] - NullSafeHeight(rite[REBL_nRL[p]]) >= -1
         /\ REBL_hRR0[p] - NullSafeHeight(rite[REBL_nRL[p]]) <= 1
         /\ ~((REBL_hRR0[p] = 0 \/ NullSafeHeight(rite[REBL_nRL[p]]) = 0) /\ val[REBL_nR[p]] = Null))
    /\ locked' = [locked EXCEPT ![REBL_nRL[p]] = -1]
    /\ retStack' = [retStack EXCEPT ![p] = Append(@, 187)]
    /\ REBR_nParent' = [REBR_nParent EXCEPT ![p] = REBL_n[p]]
    /\ REBR_n' = [REBR_n EXCEPT ![p] = REBL_nR[p]]
    /\ REBR_nL' = [REBR_nL EXCEPT ![p] = REBL_nRL[p]]
    /\ REBR_hR0' = [REBR_hR0 EXCEPT ![p] = REBL_hRR0[p]]
    /\ pc' = [pc EXCEPT ![p] = 150]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR,
                   REBL_hL0, REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL,
                   ROTR_hR, ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL,
                   ROTL_nR, ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL,
                   ROTROL_hR, ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL,
                   ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rebl_afterDoubleRot183(p) ==
    /\ pc[p] = 183
    /\ locked' = [locked EXCEPT ![REBL_nR[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = 184]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, retStack, auSaveStack, U_k, U_newValue, AU_k, AU_newValue,
                   AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged,
                   ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node,
                   NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n,
                   REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR,
                   REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL,
                   REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL,
                   ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL,
                   ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL,
                   ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL,
                   ROTLOR_hRR, ROTLOR_hRLR>>

rebl_afterDoubleRot184(p) ==
    /\ pc[p] = 184
    /\ locked' = [locked EXCEPT ![REBL_nRL[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rebl_afterFallback(p) ==
    /\ pc[p] = 187
    /\ locked' = [locked EXCEPT ![REBL_nR[p]] = -1]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<ver, key, val, height, parent, left, rite,
                   ret, auSaveStack, U_k, U_newValue, AU_k, AU_newValue, AU_parent,
                   AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success, AU_damaged, ANU_newValue,
                   ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent, AUL_node, NC_node,
                   FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent, REB_n, REB_nL,
                   REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_nLR, REBR_hLL0,
                   REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0, REBL_nRL, REBL_hRR0,
                   REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR, ROTR_hLL, ROTR_nLR,
                   ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR, ROTL_nRL, ROTL_hRL,
                   ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR, ROTROL_hLL, ROTROL_nLR,
                   ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR, ROTLOR_nRL, ROTLOR_hRR,
                   ROTLOR_hRLR>>

rotateRite(p) ==
    /\ pc[p] = 190
    /\ ver' = [ver EXCEPT ![ROTR_n[p]] = @ + 1]
    /\ left' = [left EXCEPT ![ROTR_n[p]] = ROTR_nLR[p],
                 ![ROTR_nParent[p]] = IF left[ROTR_nParent[p]] = ROTR_n[p] THEN ROTR_nL[p] ELSE @]
    /\ rite' = [rite EXCEPT ![ROTR_nL[p]] = ROTR_n[p],
                 ![ROTR_nParent[p]] = IF left[ROTR_nParent[p]] = ROTR_n[p] THEN @ ELSE ROTR_nL[p]]
    /\ parent' = [parent EXCEPT ![ROTR_n[p]] = ROTR_nL[p],
                   ![ROTR_nL[p]] = ROTR_nParent[p],
                   ![IF ROTR_nLR[p] # Null THEN ROTR_nLR[p] ELSE ROTR_n[p]] = IF ROTR_nLR[p] # Null THEN ROTR_n[p] ELSE @]
    /\ height' = [height EXCEPT ![ROTR_n[p]] = MaxPlusOne(ROTR_hLR[p], ROTR_hR[p]),
                   ![ROTR_nL[p]] = MaxPlusOne(ROTR_hLL[p], MaxPlusOne(ROTR_hLR[p], ROTR_hR[p]))]
    /\ ret' = [ret EXCEPT ![p] =
            IF ROTR_hLR[p] - ROTR_hR[p] < -1 \/ ROTR_hLR[p] - ROTR_hR[p] > 1 THEN ROTR_n[p]
            ELSE IF (ROTR_nLR[p] = Null \/ ROTR_hR[p] = 0) /\ val[ROTR_n[p]] = Null THEN ROTR_n[p]
            ELSE IF ROTR_hLL[p] - MaxPlusOne(ROTR_hLR[p], ROTR_hR[p]) < -1 \/ ROTR_hLL[p] - MaxPlusOne(ROTR_hLR[p], ROTR_hR[p]) > 1 THEN ROTR_nL[p]
            ELSE IF ROTR_hLL[p] = 0 /\ val[ROTR_nL[p]] = Null THEN ROTR_nL[p]
            ELSE parent[ROTR_nParent[p]]]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<key, val, locked, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rotateLeft(p) ==
    /\ pc[p] = 210
    /\ ver' = [ver EXCEPT ![ROTL_n[p]] = @ + 1]
    /\ rite' = [rite EXCEPT ![ROTL_n[p]] = ROTL_nRL[p],
                 ![ROTL_nParent[p]] = IF left[ROTL_nParent[p]] = ROTL_n[p] THEN @ ELSE ROTL_nR[p]]
    /\ left' = [left EXCEPT ![ROTL_nR[p]] = ROTL_n[p],
                 ![ROTL_nParent[p]] = IF left[ROTL_nParent[p]] = ROTL_n[p] THEN ROTL_nR[p] ELSE @]
    /\ parent' = [parent EXCEPT ![ROTL_n[p]] = ROTL_nR[p],
                   ![ROTL_nR[p]] = ROTL_nParent[p],
                   ![IF ROTL_nRL[p] # Null THEN ROTL_nRL[p] ELSE ROTL_n[p]] = IF ROTL_nRL[p] # Null THEN ROTL_n[p] ELSE @]
    /\ height' = [height EXCEPT ![ROTL_n[p]] = MaxPlusOne(ROTL_hL[p], ROTL_hRL[p]),
                   ![ROTL_nR[p]] = MaxPlusOne(MaxPlusOne(ROTL_hL[p], ROTL_hRL[p]), ROTL_hRR[p])]
    /\ ret' = [ret EXCEPT ![p] =
            IF ROTL_hRL[p] - ROTL_hL[p] < -1 \/ ROTL_hRL[p] - ROTL_hL[p] > 1 THEN ROTL_n[p]
            ELSE IF (ROTL_nRL[p] = Null \/ ROTL_hL[p] = 0) /\ val[ROTL_n[p]] = Null THEN ROTL_n[p]
            ELSE IF ROTL_hRR[p] - MaxPlusOne(ROTL_hL[p], ROTL_hRL[p]) < -1 \/ ROTL_hRR[p] - MaxPlusOne(ROTL_hL[p], ROTL_hRL[p]) > 1 THEN ROTL_nR[p]
            ELSE IF ROTL_hRR[p] = 0 /\ val[ROTL_nR[p]] = Null THEN ROTL_nR[p]
            ELSE parent[ROTL_nParent[p]]]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<key, val, locked, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rotateRiteOverLeft(p) ==
    /\ pc[p] = 230
    /\ ver' = [ver EXCEPT ![ROTROL_n[p]] = @ + 1, ![ROTROL_nL[p]] = @ + 1]
    /\ left' = [left EXCEPT ![ROTROL_n[p]] = rite[ROTROL_nLR[p]],
                 ![ROTROL_nLR[p]] = ROTROL_nL[p],
                 ![ROTROL_nParent[p]] = IF left[ROTROL_nParent[p]] = ROTROL_n[p] THEN ROTROL_nLR[p] ELSE @]
    /\ rite' = [rite EXCEPT ![ROTROL_nL[p]] = left[ROTROL_nLR[p]],
                 ![ROTROL_nLR[p]] = ROTROL_n[p],
                 ![ROTROL_nParent[p]] = IF left[ROTROL_nParent[p]] = ROTROL_n[p] THEN @ ELSE ROTROL_nLR[p]]
    /\ parent' = [parent EXCEPT ![ROTROL_n[p]] = ROTROL_nLR[p],
                   ![ROTROL_nL[p]] = ROTROL_nLR[p],
                   ![ROTROL_nLR[p]] = ROTROL_nParent[p],
                   ![IF rite[ROTROL_nLR[p]] # Null THEN rite[ROTROL_nLR[p]] ELSE ROTROL_n[p]] = IF rite[ROTROL_nLR[p]] # Null THEN ROTROL_n[p] ELSE @,
                   ![IF left[ROTROL_nLR[p]] # Null THEN left[ROTROL_nLR[p]] ELSE ROTROL_nL[p]] = IF left[ROTROL_nLR[p]] # Null THEN ROTROL_nL[p] ELSE @]
    /\ height' = [height EXCEPT ![ROTROL_n[p]] = MaxPlusOne(NullSafeHeight(rite[ROTROL_nLR[p]]), ROTROL_hR[p]),
                   ![ROTROL_nL[p]] = MaxPlusOne(ROTROL_hLL[p], ROTROL_hLRL[p]),
                   ![ROTROL_nLR[p]] = MaxPlusOne(MaxPlusOne(ROTROL_hLL[p], ROTROL_hLRL[p]), MaxPlusOne(NullSafeHeight(rite[ROTROL_nLR[p]]), ROTROL_hR[p]))]
    /\ ret' = [ret EXCEPT ![p] =
            IF NullSafeHeight(rite[ROTROL_nLR[p]]) - ROTROL_hR[p] < -1 \/ NullSafeHeight(rite[ROTROL_nLR[p]]) - ROTROL_hR[p] > 1 THEN ROTROL_n[p]
            ELSE IF (rite[ROTROL_nLR[p]] = Null \/ ROTROL_hR[p] = 0) /\ val[ROTROL_n[p]] = Null THEN ROTROL_n[p]
            ELSE IF MaxPlusOne(ROTROL_hLL[p], ROTROL_hLRL[p]) - MaxPlusOne(NullSafeHeight(rite[ROTROL_nLR[p]]), ROTROL_hR[p]) < -1
                 \/ MaxPlusOne(ROTROL_hLL[p], ROTROL_hLRL[p]) - MaxPlusOne(NullSafeHeight(rite[ROTROL_nLR[p]]), ROTROL_hR[p]) > 1 THEN ROTROL_nLR[p]
            ELSE parent[ROTROL_nParent[p]]]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<key, val, locked, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

rotateLeftOverRite(p) ==
    /\ pc[p] = 250
    /\ ver' = [ver EXCEPT ![ROTLOR_n[p]] = @ + 1, ![ROTLOR_nR[p]] = @ + 1]
    /\ rite' = [rite EXCEPT ![ROTLOR_n[p]] = left[ROTLOR_nRL[p]],
                 ![ROTLOR_nRL[p]] = ROTLOR_nR[p],
                 ![ROTLOR_nParent[p]] = IF left[ROTLOR_nParent[p]] = ROTLOR_n[p] THEN @ ELSE ROTLOR_nRL[p]]
    /\ left' = [left EXCEPT ![ROTLOR_nR[p]] = rite[ROTLOR_nRL[p]],
                 ![ROTLOR_nRL[p]] = ROTLOR_n[p],
                 ![ROTLOR_nParent[p]] = IF left[ROTLOR_nParent[p]] = ROTLOR_n[p] THEN ROTLOR_nRL[p] ELSE @]
    /\ parent' = [parent EXCEPT ![ROTLOR_n[p]] = ROTLOR_nRL[p],
                   ![ROTLOR_nR[p]] = ROTLOR_nRL[p],
                   ![ROTLOR_nRL[p]] = ROTLOR_nParent[p],
                   ![IF left[ROTLOR_nRL[p]] # Null THEN left[ROTLOR_nRL[p]] ELSE ROTLOR_n[p]] = IF left[ROTLOR_nRL[p]] # Null THEN ROTLOR_n[p] ELSE @,
                   ![IF rite[ROTLOR_nRL[p]] # Null THEN rite[ROTLOR_nRL[p]] ELSE ROTLOR_nR[p]] = IF rite[ROTLOR_nRL[p]] # Null THEN ROTLOR_nR[p] ELSE @]
    /\ height' = [height EXCEPT ![ROTLOR_n[p]] = MaxPlusOne(ROTLOR_hL[p], NullSafeHeight(left[ROTLOR_nRL[p]])),
                   ![ROTLOR_nR[p]] = MaxPlusOne(ROTLOR_hRLR[p], ROTLOR_hRR[p]),
                   ![ROTLOR_nRL[p]] = MaxPlusOne(MaxPlusOne(ROTLOR_hL[p], NullSafeHeight(left[ROTLOR_nRL[p]])), MaxPlusOne(ROTLOR_hRLR[p], ROTLOR_hRR[p]))]
    /\ ret' = [ret EXCEPT ![p] =
            IF NullSafeHeight(left[ROTLOR_nRL[p]]) - ROTLOR_hL[p] < -1 \/ NullSafeHeight(left[ROTLOR_nRL[p]]) - ROTLOR_hL[p] > 1 THEN ROTLOR_n[p]
            ELSE IF (left[ROTLOR_nRL[p]] = Null \/ ROTLOR_hL[p] = 0) /\ val[ROTLOR_n[p]] = Null THEN ROTLOR_n[p]
            ELSE IF MaxPlusOne(ROTLOR_hRLR[p], ROTLOR_hRR[p]) - MaxPlusOne(ROTLOR_hL[p], NullSafeHeight(left[ROTLOR_nRL[p]])) < -1
                 \/ MaxPlusOne(ROTLOR_hRLR[p], ROTLOR_hRR[p]) - MaxPlusOne(ROTLOR_hL[p], NullSafeHeight(left[ROTLOR_nRL[p]])) > 1 THEN ROTLOR_nRL[p]
            ELSE parent[ROTLOR_nParent[p]]]
    /\ pc' = [pc EXCEPT ![p] = RetTop(p)]
    /\ retStack' = [retStack EXCEPT ![p] = RetPop(p)]
    /\ UNCHANGED <<key, val, locked, auSaveStack, U_k, U_newValue, AU_k,
                   AU_newValue, AU_parent, AU_node, AU_nodeVer, AU_dirToC, AU_child, AU_success,
                   AU_damaged, ANU_newValue, ANU_parent, ANU_node, ANU_prev, ANU_damaged, AUL_parent,
                   AUL_node, NC_node, FHR_node, FHR_condition, FHR_nParent, FH_node, REB_nParent,
                   REB_n, REB_nL, REB_nR, REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                   REBR_nLR, REBR_hLL0, REBR_hLR0, REBL_nParent, REBL_n, REBL_nR, REBL_hL0,
                   REBL_nRL, REBL_hRR0, REBL_hRL0, ROTR_nParent, ROTR_n, ROTR_nL, ROTR_hR,
                   ROTR_hLL, ROTR_nLR, ROTR_hLR, ROTL_nParent, ROTL_n, ROTL_hL, ROTL_nR,
                   ROTL_nRL, ROTL_hRL, ROTL_hRR, ROTROL_nParent, ROTROL_n, ROTROL_nL, ROTROL_hR,
                   ROTROL_hLL, ROTROL_nLR, ROTROL_hLRL, ROTLOR_nParent, ROTLOR_n, ROTLOR_hL, ROTLOR_nR,
                   ROTLOR_nRL, ROTLOR_hRR, ROTLOR_hRLR>>

\* ======================================================================
\* Next state relation
\* ======================================================================

Next ==
    \E p \in Procs :
        (\E k \in Keys : writeInv_erase(p, k))
        \/ (\E k \in Keys : writeInv_insert(p, k))
        \/ writeResp(p)
        \/ u0_emptyErase(p)
        \/ u0_emptyInsert(p)
        \/ u0_navigate(p)
        \/ uLock0(p)
        \/ u2_writeLeaf(p)
        \/ u2_retry(p)
        \/ u4(p)
        \/ u5(p)
        \/ au0(p)
        \/ au1(p)
        \/ auT3(p)
        \/ au2(p)
        \/ au3(p)
        \/ au4(p)
        \/ au5_childNull_erase(p)
        \/ au5_childNull_insert(p)
        \/ au5_childNotNull_navigate(p)
        \/ au5_childNotNull_shrinking(p)
        \/ au5_childNotNull_verStale(p)
        \/ auLock0(p)
        \/ au7(p)
        \/ au8(p)
        \/ au9_childAppeared(p)
        \/ au9_writeLeaf(p)
        \/ auT1(p)
        \/ auT2(p)
        \/ au10(p)
        \/ au11(p)
        \/ au14(p)
        \/ au15(p)
        \/ anu0_alreadyNull(p)
        \/ anu0_continue(p)
        \/ anu1_unlinkPath(p)
        \/ anu1_updatePath(p)
        \/ anuLock0(p)
        \/ anu2(p)
        \/ anu3(p)
        \/ anuLock1(p)
        \/ anu4(p)
        \/ anu5(p)
        \/ anu5b(p)
        \/ anu7(p)
        \/ anuT0_success(p)
        \/ anuT0_fail(p)
        \/ anu8b(p)
        \/ anu12(p)
        \/ anu13(p)
        \/ anu14(p)
        \/ anuLock2(p)
        \/ anu15(p)
        \/ anu16(p)
        \/ anu17(p)
        \/ anu18(p)
        \/ anu19(p)
        \/ attemptUnlink(p)
        \/ attemptUnlink_notChild(p)
        \/ attemptUnlink_twoChildren(p)
        \/ nodeCondition(p)
        \/ fhr0_null(p)
        \/ fhr0_notNull(p)
        \/ fhr1(p)
        \/ fhr2(p)
        \/ fhrT1(p)
        \/ fhr3(p)
        \/ fhr4(p)
        \/ fhrLock0(p)
        \/ fhr5(p)
        \/ fhrT0(p)
        \/ fhr6(p)
        \/ fhrLock1(p)
        \/ fhr6b_valid(p)
        \/ fhr6b_invalid(p)
        \/ fhrLock2(p)
        \/ fhr7(p)
        \/ fhr8(p)
        \/ fhr9(p)
        \/ fixHeight(p)
        \/ reb0(p)
        \/ reb_unlink(p)
        \/ rebT0_success(p)
        \/ rebT0_fail(p)
        \/ reb3_rebalToRite(p)
        \/ reb3_rebalToLeft(p)
        \/ reb3_heightFix(p)
        \/ reb3_noRepair(p)
        \/ reb_return(p)
        \/ rebr0Lock0(p)
        \/ rebr1(p)
        \/ rebr2(p)
        \/ rebr_simpleRotate(p)
        \/ rebr_needInnerCheck(p)
        \/ rebr4(p)
        \/ rebrLock1(p)
        \/ rebr5_simpleRotate(p)
        \/ rebr5_doubleCheck(p)
        \/ rebr_afterRotUnlockNLR(p)
        \/ rebr_afterRotUnlockNL(p)
        \/ rebr_doubleRot(p)
        \/ rebr_fallback(p)
        \/ rebr_afterDoubleRot163(p)
        \/ rebr_afterDoubleRot164(p)
        \/ rebr_afterFallback(p)
        \/ rebl0Lock0(p)
        \/ rebl1(p)
        \/ rebl2(p)
        \/ rebl_simpleRotate(p)
        \/ rebl_needInnerCheck(p)
        \/ rebl4(p)
        \/ reblLock1(p)
        \/ rebl5_simpleRotate(p)
        \/ rebl5_doubleCheck(p)
        \/ rebl_afterRotUnlockNR(p)
        \/ rebl_afterRotUnlockNRL(p)
        \/ rebl_doubleRot(p)
        \/ rebl_fallback(p)
        \/ rebl_afterDoubleRot183(p)
        \/ rebl_afterDoubleRot184(p)
        \/ rebl_afterFallback(p)
        \/ rotateRite(p)
        \/ rotateLeft(p)
        \/ rotateRiteOverLeft(p)
        \/ rotateLeftOverRite(p)

\* ======================================================================
\* Specification
\* ======================================================================

Spec == Init /\ [][Next]_allVars

\* ======================================================================
\* Invariant
\* ======================================================================

QuiescenceBalanced ==
    ~(pc[0] = 0 /\ pc[1] = 0)
    \/ \A a \in 1..14 :
        (key[a] = Null \/ ver[a] = Unlinked)
        \/ (TrueHeight(left[a]) - TrueHeight(rite[a]) > -2
            /\ TrueHeight(left[a]) - TrueHeight(rite[a]) < 2)

====
