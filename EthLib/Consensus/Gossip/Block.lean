module

public import EthLib.Consensus.Gossip.Payload

/-!
# `Consensus.Gossip.Block`

Gossip validation of blocks.

A block must be the first valid block of its proposer in its slot, and must not be early.

It must build on a known parent, after the finalized slot and on the finalized chain.

Its proposer must have signed it, and must be the proposer that the parent state expects.

From Bellatrix the node also reads the status of the payload of the parent.

A parent with no state failed validation, and a parent whose payload is invalid is not built on.

From Gloas a block carries the bid of a builder in place of a payload.

Its lists of operations and the requests of its parent payload must then be within their limits.

A block on the full parent needs the parent payload verified, and its bid must name its parent.

A block on the empty parent must bid on the execution head of the parent state.

The checks run in a fixed order, and the first check that fails gives the outcome.

The checks that read the chain read the state after the head.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-- The statuses of the payloads of known blocks, by root, from Bellatrix.

A block with no status has a payload that is not yet validated. -/
abbrev PayloadStatuses := Std.TreeMap Root PayloadValidationStatus

/-- The status of the payload of a block, or not validated when the node holds none. -/
def PayloadStatuses.get (statuses : PayloadStatuses) (root : Root) : PayloadValidationStatus :=
  statuses[root]?.getD PAYLOAD_STATUS_NOT_VALIDATED

/-- The outcome for a block whose parent is known but has no state, since it failed validation.

From Bellatrix it depends on the payload of the parent, when the chain runs payloads. -/
def parentWithoutStateOutcome (store : Store preset fork) (before : fork < .glamsterdam)
    (body : BeaconBlockBody preset fork) (status : PayloadValidationStatus) :
    Except ForkChoiceError ValidationResult := do
  -- REJECT when the payload of the parent is not yet validated.
  --
  -- The parent then failed for another reason than its payload.
  --
  -- IGNORE when the node processed that payload, since the parent may still be valid.
  let byStatus : ValidationResult :=
    if status == PAYLOAD_STATUS_NOT_VALIDATED then
      .reject "block's parent is invalid and its payload is optimistic"
    else .ignore "block's parent is invalid and its payload is processed"
  -- From Capella the chain always runs payloads, so the status decides.
  if .shapella ≤ fork then return byStatus
  -- At Bellatrix the status decides once the chain runs payloads.
  --
  -- The parent has no state, so the justified state tells whether the merge has passed.
  --
  -- The chain also runs payloads for a block that carries the first payload.
  else if bellatrix : .bellatrix ≤ fork then
    let justified ← store.blockState store.justifiedCheckpoint.root
    if isExecutionEnabled justified body ⟨bellatrix, before⟩ then return byStatus
    -- Otherwise REJECT, since the parent failed validation.
    else return .reject "block's parent is invalid and execution is not enabled"
  -- Before Bellatrix, REJECT, since the parent failed validation.
  else return .reject "block's parent is invalid"

/-- From Bellatrix: the checks of the payload of a block, after the check of its signature. -/
def payloadOutcome (config : Config) (state : BeaconState preset fork)
    (before : fork < .glamsterdam) (block : BeaconBlock preset fork)
    (status : PayloadValidationStatus) : Except ForkChoiceError ValidationResult := do
  if bellatrix : .bellatrix ≤ fork then
    let capella := decide (.shapella ≤ fork)
    -- From Capella the checks always run.
    --
    -- At Bellatrix they run only when the chain runs payloads, by the head state or by the block.
    if capella || isExecutionEnabled state block.body ⟨bellatrix, before⟩ then
      -- REJECT unless the timestamp of the payload is the time of the slot of the block.
      let time ← (computeTimeAtSlot config state.genesisTime block.slot).mapError .arith
      let payload := block.body.executionPayload ⟨bellatrix, before⟩
      return (rejectUnless (payload.timestamp == time)
        "incorrect execution payload timestamp").andThen fun _ =>
        -- At Bellatrix, IGNORE when the payload of the parent is invalid.
        --
        -- From Capella that test runs before the head state is read, so it passes here.
        ignoreUnless (capella || status != PAYLOAD_STATUS_INVALIDATED)
          "block's parent is valid and its payload is invalid"
    else return .accept
  -- Before Bellatrix a block carries no payload.
  else return .accept

/-- From Deneb: whether a block commits to at most the most blobs of its epoch. -/
def blobCountWithinLimit (config : Config) (before : fork < .glamsterdam)
    (block : BeaconBlock preset fork) : Bool :=
  if deneb : .dencun ≤ fork then
    -- The limit `L` of the block.
    let limit :=
      -- From Fulu, the most blobs per block of the blob schedule at the epoch of the block.
      if .fusaka ≤ fork then
        (config.getBlobParameters (computeEpochAtSlot preset block.slot)).maxBlobsPerBlock
      -- At Electra, `MAX_BLOBS_PER_BLOCK_ELECTRA`.
      else if .pectra ≤ fork then config.MAX_BLOBS_PER_BLOCK_ELECTRA
      -- At Deneb, `MAX_BLOBS_PER_BLOCK`.
      else config.MAX_BLOBS_PER_BLOCK
    -- The block holds at most `L` blob commitments.
    (block.body.blobKzgCommitments ⟨deneb, before⟩).data.size ≤ limit.toNat
  -- Before Deneb a block commits to no blob.
  else true

/-- The proposer that the state of the parent expects at the slot of a block.

From Electra, the checks verify the deposit signatures that an epoch boundary reads. -/
def expectedProposer (config : Config) (checks : SignatureChecks)
    (parentState : BeaconState preset fork) (slot : Slot) :
    Except ForkChoiceError ValidatorIndex := do
  -- The state of the parent, advanced through the empty slots up to the slot.
  let state ← (processSlots config checks parentState slot).mapError .transition
  -- The proposer of the slot in that state.
  (getBeaconProposerIndex state).mapError .accessor

/-- From Gloas: the checks of the counts of the operations of a block, each against its limit.

The types of the lists bound none of them from Gloas, so gossip checks each count. -/
def checkBlockBodyLimits (gloas : .glamsterdam ≤ fork) (body : BeaconBlockBody preset fork) :
    ValidationResult :=
  -- REJECT unless the block holds at most `MAX_PROPOSER_SLASHINGS` proposer slashings.
  (rejectUnless (body.proposerSlashings.data.size ≤ preset.MAX_PROPOSER_SLASHINGS.toNat)
    "too many proposer slashings").andThen fun _ =>
  -- REJECT unless it holds at most `MAX_ATTESTER_SLASHINGS_ELECTRA` attester slashings.
  (rejectUnless (body.attesterSlashings.data.size ≤ preset.MAX_ATTESTER_SLASHINGS_ELECTRA.toNat)
    "too many attester slashings").andThen fun _ =>
  -- REJECT unless it holds at most `MAX_ATTESTATIONS_ELECTRA` attestations.
  (rejectUnless (body.attestations.data.size ≤ preset.MAX_ATTESTATIONS_ELECTRA.toNat)
    "too many attestations").andThen fun _ =>
  -- Before Heze, REJECT unless it holds no deposit.
  --
  -- Heze removes the deposits of blocks.
  (if heze : .hegota ≤ fork then .accept
    else rejectUnless ((body.deposits (Nat.lt_of_not_le heze)).data.size == 0)
      "block must not contain deposits").andThen fun _ =>
  -- REJECT unless it holds at most `MAX_VOLUNTARY_EXITS` voluntary exits.
  (rejectUnless (body.voluntaryExits.data.size ≤ preset.MAX_VOLUNTARY_EXITS.toNat)
    "too many voluntary exits").andThen fun _ =>
  -- REJECT unless it holds at most `MAX_BLS_TO_EXECUTION_CHANGES` changes of credentials.
  (rejectUnless ((body.blsToExecutionChanges (Nat.le_trans (by decide) gloas)).data.size ≤
    preset.MAX_BLS_TO_EXECUTION_CHANGES.toNat) "too many bls to execution changes").andThen fun _ =>
  -- REJECT unless it holds at most `MAX_PAYLOAD_ATTESTATIONS` payload attestations.
  rejectUnless ((body.payloadAttestations gloas).data.size ≤ preset.MAX_PAYLOAD_ATTESTATIONS.toNat)
    "too many payload attestations"

/-- From Gloas: the checks of a signed block on its topic, at a time in milliseconds. -/
def validateGloasBeaconBlock (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedBeaconBlock preset fork) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let block := signed.message
  let bid := (block.body.signedExecutionPayloadBid gloas).message
  -- IGNORE unless it is the first valid block of its proposer at its slot.
  (ignoreUnless (!seen.proposerSlots.contains (block.slot, block.proposerIndex))
    "block is not the first valid block for this slot and proposer").andThenM fun _ => do
  -- IGNORE unless its slot starts at most `MAXIMUM_GOSSIP_CLOCK_DISPARITY` after the clock.
  let future ← store.isFutureSlot config block.slot currentTimeMs
  (ignoreUnless (!future) "block is from a future slot").andThenM fun _ => do
  -- IGNORE unless its slot is after the first slot of the finalized epoch.
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot < block.slot)
    "block is not from a slot greater than the latest finalized slot").andThenM fun _ =>
  -- REJECT unless the counts of the operations of the block are within their limits.
  (checkBlockBodyLimits gloas block.body).andThenM fun _ =>
  -- REJECT unless the counts of the requests of the parent payload are within their limits.
  (checkExecutionRequestsLimits gloas (block.body.parentExecutionRequests gloas)).andThenM fun _ =>
  -- IGNORE unless the parent block is known.
  match store.blocks[block.parentRoot]? with
  | none => return .ignore "block's parent has not been seen"
  | some parent =>
  -- REJECT unless the parent has a state, since a parent without one failed validation.
  match store.blockStates[block.parentRoot]? with
  | none => return .reject "block's parent is invalid"
  | some parentState => do
  -- REJECT unless the proposer index names a validator of the state after the head.
  let state ← store.headState config
  match state.validators.data[block.proposerIndex.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer => do
  -- REJECT unless the proposer signed the block, under `DOMAIN_BEACON_PROPOSER` at its epoch.
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER block.slot block
    proposer.pubkey signed.signature
  (rejectUnless valid "invalid proposer signature").andThenM fun _ => do
  -- The parent is full when the bid builds on the block hash of the bid of the parent.
  --
  -- IGNORE when the parent is full and the store holds no verified payload of it.
  let full := Store.parentPayloadStatus block parent == .full
  (ignoreUnless (!full || store.isPayloadVerified gloas block.parentRoot)
    "parent payload is not verified").andThenM fun _ =>
  -- REJECT unless the parent is at an earlier slot than the block.
  (rejectUnless (parent.slot < block.slot)
    "block is not from a higher slot than its parent").andThenM fun _ => do
  -- REJECT unless the finalized checkpoint is on the chain of the parent.
  --
  -- Its root is the ancestor of the parent at the first slot of the finalized epoch.
  let finalizedBlock ← store.getCheckpointBlock block.parentRoot store.finalizedCheckpoint.epoch
  (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
    "finalized checkpoint is not an ancestor of block").andThenM fun _ =>
  -- REJECT unless the bid commits to at most the most blobs per block of the blob schedule.
  --
  -- The schedule is read at the epoch of the block.
  (rejectUnless (bid.blobKzgCommitments.data.size ≤
      (config.getBlobParameters (computeEpochAtSlot preset block.slot)).maxBlobsPerBlock.toNat)
    "too many blob kzg commitments").andThenM fun _ =>
  -- REJECT unless the parent block of the bid is the parent of the block.
  (rejectUnless (bid.parentBlockRoot == block.parentRoot)
    "bid's parent does not equal block's parent").andThenM fun _ => do
  -- The state of the parent, advanced through the empty slots up to the slot of the block.
  let advanced ← (processSlots config checks parentState block.slot).mapError .transition
  -- REJECT unless the proposer of the block is the proposer of its slot in that state.
  let expected ← (getBeaconProposerIndex advanced).mapError .accessor
  (rejectUnless (block.proposerIndex == expected)
    "block proposer_index does not match expected proposer").andThenM fun _ =>
  -- When the parent is empty, REJECT unless the bid builds on the latest block hash of that state.
  return rejectUnless (full || bid.parentBlockHash == advanced.latestBlockHash gloas)
    "bid does not build on the parent's execution head"

/-- The checks of a signed block on its topic, at a time in milliseconds.

The statuses are those of the payloads of known blocks, which the checks read from Bellatrix.

From Gloas the block carries a bid, and the Gloas checks read none of the statuses. -/
def validateBeaconBlock (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (statuses : PayloadStatuses)
    (signed : SignedBeaconBlock preset fork)
    (currentTimeMs : UInt64) : Except ForkChoiceError ValidationResult :=
  -- From Gloas, the checks of a block that carries a bid.
  if gloas : .glamsterdam ≤ fork then
    validateGloasBeaconBlock config checks seen store gloas signed currentTimeMs
  else
  let before : fork < .glamsterdam := Nat.lt_of_not_le gloas
  let block := signed.message
  -- IGNORE unless it is the first valid block of its proposer at its slot.
  (ignoreUnless (!seen.proposerSlots.contains (block.slot, block.proposerIndex))
    "block is not the first valid block for this slot and proposer").andThenM fun _ => do
  -- IGNORE unless its slot starts at most `MAXIMUM_GOSSIP_CLOCK_DISPARITY` after the clock.
  let future ← store.isFutureSlot config block.slot currentTimeMs
  (ignoreUnless (!future) "block is from a future slot").andThenM fun _ => do
  -- IGNORE unless its slot is after the first slot of the finalized epoch.
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot < block.slot)
    "block is not from a slot greater than the latest finalized slot").andThenM fun _ => do
  -- IGNORE unless the parent block is known.
  match store.blocks[block.parentRoot]? with
  | none => return .ignore "block's parent has not been seen"
  | some parent => do
  -- The status of the payload of the parent, not validated when the node holds none.
  let status := statuses.get block.parentRoot
  -- A parent without a state failed validation, and the outcome depends on its payload.
  match store.blockStates[block.parentRoot]? with
  | none => parentWithoutStateOutcome store before block.body status
  | some parentState => do
  -- From Capella, IGNORE when the payload of the parent is invalid.
  (ignoreUnless (!(decide (.shapella ≤ fork)) || status != PAYLOAD_STATUS_INVALIDATED)
    "block's parent is valid and its payload is invalid").andThenM fun _ => do
  -- REJECT unless the proposer index names a validator of the state after the head.
  let state ← store.headState config
  match state.validators.data[block.proposerIndex.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer => do
  -- REJECT unless the proposer signed the block, under `DOMAIN_BEACON_PROPOSER` at its epoch.
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER block.slot block
    proposer.pubkey signed.signature
  (rejectUnless valid "invalid proposer signature").andThenM fun _ => do
  -- From Bellatrix, the checks of the payload of the block.
  (← payloadOutcome config state before block status).andThenM fun _ =>
  -- REJECT unless the parent is at an earlier slot than the block.
  (rejectUnless (parent.slot < block.slot)
    "block is not from a higher slot than its parent").andThenM fun _ => do
  -- REJECT unless the finalized checkpoint is on the chain of the parent.
  --
  -- Its root is the ancestor of the parent at the first slot of the finalized epoch.
  let finalizedBlock ← store.getCheckpointBlock block.parentRoot store.finalizedCheckpoint.epoch
  (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
    "finalized checkpoint is not an ancestor of block").andThenM fun _ =>
  -- From Deneb, REJECT unless the block commits to at most the most blobs of its epoch.
  (rejectUnless (blobCountWithinLimit config before block)
    "too many blob kzg commitments").andThenM fun _ => do
  -- REJECT unless the proposer of the block is the one that the parent state expects.
  let expected ← expectedProposer config checks parentState block.slot
  return rejectUnless (block.proposerIndex == expected)
    "block proposer_index does not match expected proposer"

/-- The keys after a valid block: its slot and its proposer. -/
def Seen.recordBeaconBlock (seen : Seen) (signed : SignedBeaconBlock preset fork) : Seen :=
  { seen with
    proposerSlots := (signed.message.slot, signed.message.proposerIndex) :: seen.proposerSlots }

end EthLib.Consensus
