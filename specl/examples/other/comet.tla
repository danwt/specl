---------------------------- MODULE comet ----------------------------
(* CometBFT/Tendermint BFT consensus — single height with Byzantine faults
   From: Buchman, Kwon, Milosevic, "The latest gossip on BFT consensus" (2018)
   N+1 validators (0..N), tolerating F Byzantine faults where N+1 >= 3F+1
   Quorum = 2F+1 *)

EXTENDS Integers, FiniteSets

CONSTANTS N, MaxRound, V, F

VARIABLES step, round, lockedValue, lockedRound,
          validValue, validRound, prevotes, precommits,
          proposal, decision, faulty

vars == <<step, round, lockedValue, lockedRound,
          validValue, validRound, prevotes, precommits,
          proposal, decision, faulty>>

Validators == 0..N
Rounds == 0..MaxRound
Values == 0..V
Quorum == 2 * F + 1

Proposer(r) == r % (N + 1)
PrevoteCount(r, v) == Cardinality({i \in Validators : prevotes[r][i] = v})
PrecommitCount(r, v) == Cardinality({i \in Validators : precommits[r][i] = v})
AnyPrevoteCount(r) == Cardinality({i \in Validators : prevotes[r][i] # -2})
AnyPrecommitCount(r) == Cardinality({i \in Validators : precommits[r][i] # -2})

Init ==
    /\ step = [i \in Validators |-> 0]
    /\ round = [i \in Validators |-> 0]
    /\ lockedValue = [i \in Validators |-> -1]
    /\ lockedRound = [i \in Validators |-> -1]
    /\ validValue = [i \in Validators |-> -1]
    /\ validRound = [i \in Validators |-> -1]
    /\ prevotes = [r \in Rounds |-> [i \in Validators |-> -2]]
    /\ precommits = [r \in Rounds |-> [i \in Validators |-> -2]]
    /\ proposal = [r \in Rounds |-> -1]
    /\ decision = [i \in Validators |-> -1]
    /\ faulty = [i \in Validators |-> FALSE]

(* A validator goes Byzantine (at most F can) *)
GoFaulty(i) ==
    /\ ~faulty[i]
    /\ Cardinality({j \in Validators : faulty[j]}) < F
    /\ faulty' = [faulty EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound,
                   validValue, validRound, prevotes, precommits,
                   proposal, decision>>

(* Byzantine validator prevotes for a value *)
ByzantinePrevote(i, r, v) ==
    /\ faulty[i]
    /\ prevotes[r][i] = -2
    /\ prevotes' = [prevotes EXCEPT ![r] = [prevotes[r] EXCEPT ![i] = v]]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound,
                   validValue, validRound, precommits, proposal, decision, faulty>>

(* Byzantine validator prevotes nil *)
ByzantinePrevoteNil(i, r) ==
    /\ faulty[i]
    /\ prevotes[r][i] = -2
    /\ prevotes' = [prevotes EXCEPT ![r] = [prevotes[r] EXCEPT ![i] = -1]]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound,
                   validValue, validRound, precommits, proposal, decision, faulty>>

(* Byzantine validator precommits for a value *)
ByzantinePrecommit(i, r, v) ==
    /\ faulty[i]
    /\ precommits[r][i] = -2
    /\ precommits' = [precommits EXCEPT ![r] = [precommits[r] EXCEPT ![i] = v]]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound,
                   validValue, validRound, prevotes, proposal, decision, faulty>>

(* Byzantine validator precommits nil *)
ByzantinePrecommitNil(i, r) ==
    /\ faulty[i]
    /\ precommits[r][i] = -2
    /\ precommits' = [precommits EXCEPT ![r] = [precommits[r] EXCEPT ![i] = -1]]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound,
                   validValue, validRound, prevotes, proposal, decision, faulty>>

(* Honest proposer for round r proposes value v *)
Propose(r, v) ==
    /\ ~faulty[Proposer(r)]
    /\ proposal[r] = -1
    /\ round[Proposer(r)] = r
    /\ step[Proposer(r)] = 0
    /\ validValue[Proposer(r)] = -1 \/ validValue[Proposer(r)] = v
    /\ proposal' = [proposal EXCEPT ![r] = v]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound,
                   validValue, validRound, prevotes, precommits, decision, faulty>>

(* Byzantine proposer can propose any value *)
ByzantinePropose(r, v) ==
    /\ faulty[Proposer(r)]
    /\ proposal[r] = -1
    /\ proposal' = [proposal EXCEPT ![r] = v]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound,
                   validValue, validRound, prevotes, precommits, decision, faulty>>

(* Honest validator i prevotes for proposed value in round r *)
PrevoteBlock(i, r) ==
    /\ ~faulty[i]
    /\ round[i] = r
    /\ step[i] = 0
    /\ prevotes[r][i] = -2
    /\ proposal[r] # -1
    /\ \/ lockedRound[i] = -1
       \/ lockedValue[i] = proposal[r]
       \/ \E vr \in Rounds :
            /\ vr < r
            /\ PrevoteCount(vr, proposal[r]) >= Quorum
            /\ lockedRound[i] <= vr
    /\ prevotes' = [prevotes EXCEPT ![r] = [prevotes[r] EXCEPT ![i] = proposal[r]]]
    /\ step' = [step EXCEPT ![i] = 1]
    /\ UNCHANGED <<round, lockedValue, lockedRound, validValue, validRound,
                   precommits, proposal, decision, faulty>>

(* Honest validator i prevotes nil in round r *)
PrevoteNil(i, r) ==
    /\ ~faulty[i]
    /\ round[i] = r
    /\ step[i] = 0
    /\ prevotes[r][i] = -2
    /\ prevotes' = [prevotes EXCEPT ![r] = [prevotes[r] EXCEPT ![i] = -1]]
    /\ step' = [step EXCEPT ![i] = 1]
    /\ UNCHANGED <<round, lockedValue, lockedRound, validValue, validRound,
                   precommits, proposal, decision, faulty>>

(* Honest validator i precommits for value v after 2F+1 prevotes *)
PrecommitBlock(i, r, v) ==
    /\ ~faulty[i]
    /\ round[i] = r
    /\ step[i] = 1
    /\ precommits[r][i] = -2
    /\ PrevoteCount(r, v) >= Quorum
    /\ proposal[r] = v
    /\ precommits' = [precommits EXCEPT ![r] = [precommits[r] EXCEPT ![i] = v]]
    /\ step' = [step EXCEPT ![i] = 2]
    /\ lockedValue' = [lockedValue EXCEPT ![i] = v]
    /\ lockedRound' = [lockedRound EXCEPT ![i] = r]
    /\ validValue' = [validValue EXCEPT ![i] = v]
    /\ validRound' = [validRound EXCEPT ![i] = r]
    /\ UNCHANGED <<round, prevotes, proposal, decision, faulty>>

(* Honest validator i precommits nil after 2F+1 nil prevotes *)
PrecommitNil(i, r) ==
    /\ ~faulty[i]
    /\ round[i] = r
    /\ step[i] = 1
    /\ precommits[r][i] = -2
    /\ PrevoteCount(r, -1) >= Quorum
    /\ precommits' = [precommits EXCEPT ![r] = [precommits[r] EXCEPT ![i] = -1]]
    /\ step' = [step EXCEPT ![i] = 2]
    /\ UNCHANGED <<round, lockedValue, lockedRound, validValue, validRound,
                   prevotes, proposal, decision, faulty>>

(* Honest validator i precommits nil on prevote timeout *)
PrecommitTimeout(i, r) ==
    /\ ~faulty[i]
    /\ round[i] = r
    /\ step[i] = 1
    /\ precommits[r][i] = -2
    /\ AnyPrevoteCount(r) >= Quorum
    /\ precommits' = [precommits EXCEPT ![r] = [precommits[r] EXCEPT ![i] = -1]]
    /\ step' = [step EXCEPT ![i] = 2]
    /\ UNCHANGED <<round, lockedValue, lockedRound, validValue, validRound,
                   prevotes, proposal, decision, faulty>>

(* Validator i decides value v *)
Decide(i, r, v) ==
    /\ decision[i] = -1
    /\ PrecommitCount(r, v) >= Quorum
    /\ proposal[r] = v
    /\ decision' = [decision EXCEPT ![i] = v]
    /\ UNCHANGED <<step, round, lockedValue, lockedRound, validValue, validRound,
                   prevotes, precommits, proposal, faulty>>

(* Honest validator i moves to next round *)
NextRound(i, r) ==
    /\ ~faulty[i]
    /\ round[i] = r
    /\ step[i] = 2
    /\ r < MaxRound
    /\ AnyPrecommitCount(r) >= Quorum
    /\ round' = [round EXCEPT ![i] = r + 1]
    /\ step' = [step EXCEPT ![i] = 0]
    /\ UNCHANGED <<lockedValue, lockedRound, validValue, validRound,
                   prevotes, precommits, proposal, decision, faulty>>

Next ==
    \/ \E i \in Validators : GoFaulty(i)
    \/ \E i \in Validators, r \in Rounds, v \in Values : ByzantinePrevote(i, r, v)
    \/ \E i \in Validators, r \in Rounds : ByzantinePrevoteNil(i, r)
    \/ \E i \in Validators, r \in Rounds, v \in Values : ByzantinePrecommit(i, r, v)
    \/ \E i \in Validators, r \in Rounds : ByzantinePrecommitNil(i, r)
    \/ \E r \in Rounds, v \in Values : Propose(r, v)
    \/ \E r \in Rounds, v \in Values : ByzantinePropose(r, v)
    \/ \E i \in Validators, r \in Rounds : PrevoteBlock(i, r)
    \/ \E i \in Validators, r \in Rounds : PrevoteNil(i, r)
    \/ \E i \in Validators, r \in Rounds, v \in Values : PrecommitBlock(i, r, v)
    \/ \E i \in Validators, r \in Rounds : PrecommitNil(i, r)
    \/ \E i \in Validators, r \in Rounds : PrecommitTimeout(i, r)
    \/ \E i \in Validators, r \in Rounds, v \in Values : Decide(i, r, v)
    \/ \E i \in Validators, r \in Rounds : NextRound(i, r)

Spec == Init /\ [][Next]_vars

(* Agreement: no two honest validators decide different values *)
Agreement ==
    \A i \in Validators : \A j \in Validators :
        (~faulty[i] /\ ~faulty[j] /\ decision[i] # -1 /\ decision[j] # -1)
        => decision[i] = decision[j]

=====================================================================
