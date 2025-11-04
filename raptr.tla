------------------------------ MODULE Raptr ------------------------------
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)
CONSTANTS
  VAL,        \* set of validators, e.g., {v1,v2,v3,v4}
  ROUNDS,     \* finite range of round indices, e.g., 0..5
  f,          \* byzantine bound (toy: 1 when |VAL|=4)
  leader,     \* leader schedule: [ROUNDS -> VAL]
  Honest      \* honesty map: [VAL -> BOOLEAN] (used for liveness later)

(***************************************************************************)
(* BASIC HELPERS                                                           *)
(***************************************************************************)
Quorum(S) == Cardinality(S) >= 2*f + 1

Parent(r) == IF r = 0 THEN -1 ELSE r - 1

Extends(r2, r1) == r1 # -1 /\ Parent(r2) = r1

(***************************************************************************)
(* MESSAGE SHAPES (no network ordering; we use a set of records)          *)
(***************************************************************************)
Message ==
  [ type  : {"Proposal","Vote","QC"},
    round : ROUNDS,
    v     : (VAL \cup {Nil}) ]
  \* For Proposal/QC, v = Nil. For Vote, v is the voter.

(***************************************************************************)
(* STATE VARIABLES — these change over time                                *)
(***************************************************************************)
VARIABLES
  msgs,        \* SET of Message currently in the "network"
  qc,          \* [ROUNDS -> BOOLEAN] : has a QC for round r formed?
  proposed,    \* [ROUNDS -> BOOLEAN] : has round r been proposed?
  voted,       \* [VAL -> [ROUNDS -> BOOLEAN]] : has v voted in r?
  isOpt,       \* [ROUNDS -> BOOLEAN] : was the proposal for r optimistic?
  buffer,      \* [VAL -> SUBSET ROUNDS] : rounds v will vote later (optimistic)
  GST          \* BOOLEAN: have we entered the post-GST synchronous period?

(***************************************************************************)
(* TYPE/SHAPE INVARIANT —               *)
(***************************************************************************)


(***************************************************************************)
(* INITIAL STATES                                                          *)
(***************************************************************************)
Init ==
  /\ msgs = {}
  /\ qc = [r \in ROUNDS |-> FALSE]
  /\ proposed = [r \in ROUNDS |-> FALSE]
  /\ voted = [v \in VAL |-> [r \in ROUNDS |-> FALSE]]
  /\ isOpt = [r \in ROUNDS |-> FALSE]
  /\ buffer = [v \in VAL |-> {}]
  /\ GST = FALSE


=============================================================================
