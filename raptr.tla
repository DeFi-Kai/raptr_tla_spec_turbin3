------------------------------ MODULE Raptr ------------------------------
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* CONSTANTS (set in TLC)                                                  *)
(***************************************************************************)
CONSTANTS
  VAL,                 \* validators, e.g., {v1,v2,v3,v4,v5}
  ROUNDS,              \* finite rounds, e.g., 0..4
  f,                   \* BFT bound: |VAL| = 3*f + 1 (toy, unweighted)
  BATCH,               \* pool of batch ids, e.g., 0..7
  MAXLEN               \* max batches per proposal (small, e.g., 2)

(***************************************************************************)
(* HELPERS                                                                 *)
(***************************************************************************)
Quorum(S) == Cardinality(S) >= 2*f + 1

Parent(r) == IF r = 0 THEN -1 ELSE r - 1

\* prefix operator for sequences: Prefix(S, k) = first k elements of S
Prefix(S, k) == SubSeq(S, 1, k)

\* Does Seq S2 extend Seq S1 by prefix of length k? (k may be 0)
ExtendsByPrefix(S2, S1, k) ==
  /\ k \in Nat
  /\ k <= Len(S1) /\ k <= Len(S2)
  /\ Prefix(S2, k) = Prefix(S1, k)

(***************************************************************************)
(* MESSAGES                                                                *)
(***************************************************************************)
Message ==
  [ type  : {"Proposal","Vote","QCPrefix"},
    round : ROUNDS,
    v     : VAL \cup {Nil},
    seq   : Seq(BATCH) \cup {<<>>},     \* proposal’s batch sequence (Proposal only)
    k     : Nat ]                        \* prefix length (Vote/QC only)

(***************************************************************************)
(* STATE                                                                   *)
(***************************************************************************)
VARIABLES
  msgs,               \* SET Message in flight
  proposed,           \* [ROUNDS -> BOOLEAN]
  propSeq,            \* [ROUNDS -> Seq(BATCH)]  proposal sequence per round
  voted,              \* [VAL -> [ROUNDS -> BOOLEAN]]  did v vote in round r?
  voteLen,            \* [VAL -> [ROUNDS -> Nat]]      prefix length v voted for
  qc,                 \* [ROUNDS -> [0..MAXLEN -> BOOLEAN]]  qc[r][k]?
  haveBatch           \* [VAL -> SUBSET BATCH]  local availability

Vars == << msgs, proposed, propSeq, voted, voteLen, qc, haveBatch >>

(***************************************************************************)
(* TYPES / SHAPE                                                           *)
(***************************************************************************)


(***************************************************************************)
(* INIT                                                                    *)
(***************************************************************************)
Init ==
  /\ msgs = {}
  /\ proposed = [r \in ROUNDS |-> FALSE]
  /\ propSeq = [r \in ROUNDS |-> <<>>]
  /\ voted = [v \in VAL |-> [r \in ROUNDS |-> FALSE]]
  /\ voteLen = [v \in VAL |-> [r \in ROUNDS |-> 0]]
  /\ qc = [r \in ROUNDS |-> [k \in 0..MAXLEN |-> FALSE]]
  /\ haveBatch = [v \in VAL |-> {}]

(***************************************************************************)
(* ACTIONS                                                                 *)
(***************************************************************************)


=============================================================================
