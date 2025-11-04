# Raptr.tla — Prefix Consensus Scaffold

This TLA+ module defines the **state and structure** for modeling Raptr’s prefix consensus (from the Aptos Raptr paper).

## About Aptos Raptr

Aptos is a state machine made up of replicas (or nodes).

Raptr integrates data availability certification directly into its consensus process. Validators can optimistically propose batch digests without waiting for global availability proofs, and replicas only sign proposals for data they have locally stored. A committed Quorum Certificate (QC) therefore implies that the referenced data is available.

Raptr allows prefix voting, to handle cases where some replicas lack data, where replicas vote for the portion (prefix) of a block they have received. This ensures consensus can continue even with partial data availability, reducing latency and improving robustness compared to earlier asynchronous quorum store approaches.

_"Its core innovation lies in integrating the low-latency benefits of leader-based protocols with the high throughput of DAG-based BFT systems—without compromising resilience to adversarial failures or adverse network conditions."_

## RAPTR Consensus Summary

RAPTR achieves agreement through a **prefix voting mechanism**, allowing consensus to progress even when some data is unavailable. Consensus proceeds in rounds, with each replica advancing based on a valid entry reason.

- **Block Proposal:** A designated leader proposes a block containing metadata of transaction batches and a reason for entry. Replicas verify the proposal and process its attached Quorum Certificate (QC).

- **Prefix Voting (QC-vote):** Replicas vote on the **longest prefix** of batches they have received, rather than waiting for full data availability. Each vote includes the block hash, round number, and received prefix, enabling progress despite partial data.

- **Forming a QC:** When a replica gathers a quorum of votes, it forms a QC that certifies a prefix of the proposed block. The certified prefix corresponds to the \( S \)-th largest prefix among the votes, where \( S >= f + 1 \).

- **Voting on a QC (CC-vote):** After receiving a QC, replicas update their highest known QC and issue a **CC-vote** for the certified prefix, including the QC for verification.

- **Forming a Commit Certificate (CC):** When a quorum of CC-votes for the same block is collected, a **Commit Certificate** is formed. It commits the smallest certified prefix from the votes, along with all parent prefixes.

- **Timeout (TC):** If progress halts due to faults or delays, replicas exchange signed timeouts. A quorum of these forms a **Timeout Certificate (TC)**.

- **Advancing Rounds:** The new leader decides how to enter the next round:
  - If a full-prefix QC exists, it extends that block.
  - If only a CC exists, it extends the maximum prefix attached to its votes.
  - If the round timed out, it extends the maximum prefix certified by the timeout QCs.

The safety of RAPTR is maintained by the **prefix containment property**, which ensures all committed prefixes extend one another. Combined with quorum intersection, this guarantees that every valid proposal extends an already committed prefix, preserving agreement across replicas.


## What’s Included

### Constants
- **VAL** – Validators (e.g., `{v1,v2,v3,v4,v5}`)  
- **ROUNDS** – Consensus rounds (e.g., `0..4`)  
- **f** – Byzantine fault bound (`|VAL| = 3f + 1`)  
- **BATCH** – Pool of batch IDs (e.g., `0..7`)  
- **MAXLEN** – Maximum batch sequence length per proposal

### Helpers
- `Quorum(S)` – Checks if a validator set forms a quorum (`≥ 2f+1`)
- `Parent(r)` – Returns `r-1` or `-1` for genesis
- `Prefix(S,k)` – Returns the first `k` elements of a sequence
- `ExtendsByPrefix(S2,S1,k)` – True if `S2` and `S1` share the same prefix of length `k`

### Message Type
Each message is represented as a record:

- **Proposal** — Carries batch sequence (`seq`)
- **Vote** — Includes prefix length (`k`) a validator voted for
- **QCPrefix** — Quorum certificate for a prefix length

### State Variables
- **msgs** – Set of messages in flight  
- **proposed** – Tracks if a round has a proposal  
- **propSeq** – Proposed batch sequence for each round  
- **voted** – Whether each validator voted in a round  
- **voteLen** – Prefix length each validator voted for  
- **qc** – Quorum certificates per round and prefix length  
- **haveBatch** – Local batch availability per validator

### Init
Defines the initial system state:
- No messages or proposals (`msgs = {}`, `proposed = FALSE`)
- Empty proposal sequences (`propSeq[r] = <<>>`)
- No votes or QCs (`voted = FALSE`, `qc = FALSE`)
- No local batches available (`haveBatch[v] = {}`)

---

## Next Steps

1. **Add actions** to describe state transitions:
   - `Deliver(v,b)` — a batch becomes available to validator `v`
   - `Propose(r)` — leader proposes a batch sequence
   - `Vote(v,r)` — validator votes for a prefix length based on local batches
   - `FormQCPrefix(r,k)` — form a QC when quorum votes for prefix ≥ `k`

2. **Add invariants** to verify:
   - One proposal per round  
   - One vote per validator per round  
   - Votes respect availability (`k ≤ Len(propSeq[r])`)  
   - Each proposal extends the parent’s highest certified prefix

3. **Run TLC** to confirm `Init` loads, then extend with actions and invariants.

