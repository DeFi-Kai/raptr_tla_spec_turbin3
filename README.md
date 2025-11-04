# Raptr.tla — Prefix Consensus Scaffold

This TLA+ module defines the **state and structure** for modeling Raptr’s prefix consensus (from the Aptos Raptr paper).

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

