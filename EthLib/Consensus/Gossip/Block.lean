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

Before Bellatrix the block is rejected.

From Bellatrix it depends on the payload of the parent, when the chain runs payloads.

A parent whose payload is not yet validated failed for another reason, so the block is rejected.

A parent whose payload the node processed may still be valid, so the block is ignored.

At Bellatrix the chain runs payloads once the justified state has passed the merge.

It also runs them for a block that carries the first payload. -/
def parentWithoutStateOutcome (store : Store preset fork) (before : fork < .glamsterdam)
    (body : BeaconBlockBody preset fork) (status : PayloadValidationStatus) :
    Except ForkChoiceError ValidationResult := do
  let byStatus : ValidationResult :=
    if status == PAYLOAD_STATUS_NOT_VALIDATED then
      .reject "block's parent is invalid and its payload is optimistic"
    else .ignore "block's parent is invalid and its payload is processed"
  if .shapella ≤ fork then return byStatus
  else if bellatrix : .bellatrix ≤ fork then
    let justified ← store.blockState store.justifiedCheckpoint.root
    if isExecutionEnabled justified body ⟨bellatrix, before⟩ then return byStatus
    else return .reject "block's parent is invalid and execution is not enabled"
  else return .reject "block's parent is invalid"

/-- From Bellatrix: the checks of the payload of a block, after the check of its signature.

The time of the payload must be the time of the slot of the block.

At Bellatrix both checks run only when the chain runs payloads.

At Bellatrix a parent whose payload is invalid makes the block ignored here.

From Capella that test runs before the head state is read. -/
def payloadOutcome (config : Config) (state : BeaconState preset fork)
    (before : fork < .glamsterdam) (block : BeaconBlock preset fork)
    (status : PayloadValidationStatus) : Except ForkChoiceError ValidationResult := do
  if bellatrix : .bellatrix ≤ fork then
    let capella := decide (.shapella ≤ fork)
    if capella || isExecutionEnabled state block.body ⟨bellatrix, before⟩ then
      let time ← (computeTimeAtSlot config state.genesisTime block.slot).mapError .arith
      let payload := block.body.executionPayload ⟨bellatrix, before⟩
      return (rejectUnless (payload.timestamp == time)
        "incorrect execution payload timestamp").andThen fun _ =>
        ignoreUnless (capella || status != PAYLOAD_STATUS_INVALIDATED)
          "block's parent is valid and its payload is invalid"
    else return .accept
  else return .accept

/-- From Deneb: whether a block commits to at most the most blobs of its epoch.

Electra raises the limit, and from Fulu the blob schedule sets it at the epoch of the block. -/
def blobCountWithinLimit (config : Config) (before : fork < .glamsterdam)
    (block : BeaconBlock preset fork) : Bool :=
  if deneb : .dencun ≤ fork then
    let limit :=
      if .fusaka ≤ fork then
        (config.getBlobParameters (computeEpochAtSlot preset block.slot)).maxBlobsPerBlock
      else if .pectra ≤ fork then config.MAX_BLOBS_PER_BLOCK_ELECTRA
      else config.MAX_BLOBS_PER_BLOCK
    (block.body.blobKzgCommitments ⟨deneb, before⟩).data.size ≤ limit.toNat
  else true

/-- The proposer that the state of the parent expects at the slot of a block.

The state of the parent advances through the empty slots up to that slot.

From Electra, the checks verify the deposit signatures that an epoch boundary reads. -/
def expectedProposer (config : Config) (checks : SignatureChecks)
    (parentState : BeaconState preset fork) (slot : Slot) :
    Except ForkChoiceError ValidatorIndex := do
  let state ← (processSlots config checks parentState slot).mapError .transition
  (getBeaconProposerIndex state).mapError .accessor

/-- From Gloas: the checks of the counts of the operations of a block, each against its limit.

The types of the lists bound none of them from Gloas, so gossip checks each count.

Before Heze a block must also carry no deposit, and Heze removes the deposits of blocks. -/
def checkBlockBodyLimits (gloas : .glamsterdam ≤ fork) (body : BeaconBlockBody preset fork) :
    ValidationResult :=
  (rejectUnless (body.proposerSlashings.data.size ≤ preset.MAX_PROPOSER_SLASHINGS.toNat)
    "too many proposer slashings").andThen fun _ =>
  (rejectUnless (body.attesterSlashings.data.size ≤ preset.MAX_ATTESTER_SLASHINGS_ELECTRA.toNat)
    "too many attester slashings").andThen fun _ =>
  (rejectUnless (body.attestations.data.size ≤ preset.MAX_ATTESTATIONS_ELECTRA.toNat)
    "too many attestations").andThen fun _ =>
  (if heze : .hegota ≤ fork then .accept
    else rejectUnless ((body.deposits (Nat.lt_of_not_le heze)).data.size == 0)
      "block must not contain deposits").andThen fun _ =>
  (rejectUnless (body.voluntaryExits.data.size ≤ preset.MAX_VOLUNTARY_EXITS.toNat)
    "too many voluntary exits").andThen fun _ =>
  (rejectUnless ((body.blsToExecutionChanges (Nat.le_trans (by decide) gloas)).data.size ≤
    preset.MAX_BLS_TO_EXECUTION_CHANGES.toNat) "too many bls to execution changes").andThen fun _ =>
  rejectUnless ((body.payloadAttestations gloas).data.size ≤ preset.MAX_PAYLOAD_ATTESTATIONS.toNat)
    "too many payload attestations"

/-- From Gloas: the checks of a signed block on its topic, at a time in milliseconds.

The block must be new for its slot and proposer, not early, and after the finalized slot.

Its operations and the requests of its parent payload must be within their limits.

Its parent must be known, and is ignored otherwise; it must have a state, and is rejected otherwise.

Its proposer must be a validator of the head state, and must have signed it.

A block on the full parent waits for the parent payload to be verified, and is ignored until then.

It must come after its parent, on the finalized chain, with at most the blobs of its epoch.

Its bid must name its parent, and its proposer must be the one that the parent state expects.

A block on the empty parent must bid on the execution head of the parent state. -/
def validateGloasBeaconBlock (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedBeaconBlock preset fork) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let block := signed.message
  let bid := (block.body.signedExecutionPayloadBid gloas).message
  (ignoreUnless (!seen.proposerSlots.contains (block.slot, block.proposerIndex))
    "block is not the first valid block for this slot and proposer").andThenM fun _ => do
  let future ← store.isFutureSlot config block.slot currentTimeMs
  (ignoreUnless (!future) "block is from a future slot").andThenM fun _ => do
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot < block.slot)
    "block is not from a slot greater than the latest finalized slot").andThenM fun _ =>
  (checkBlockBodyLimits gloas block.body).andThenM fun _ =>
  (checkExecutionRequestsLimits gloas (block.body.parentExecutionRequests gloas)).andThenM fun _ =>
  match store.blocks[block.parentRoot]? with
  | none => return .ignore "block's parent has not been seen"
  | some parent =>
  match store.blockStates[block.parentRoot]? with
  | none => return .reject "block's parent is invalid"
  | some parentState => do
  let state ← store.headState config
  match state.validators.data[block.proposerIndex.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer => do
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER block.slot block
    proposer.pubkey signed.signature
  (rejectUnless valid "invalid proposer signature").andThenM fun _ => do
  let full := Store.parentPayloadStatus block parent == .full
  (ignoreUnless (!full || store.isPayloadVerified gloas block.parentRoot)
    "parent payload is not verified").andThenM fun _ =>
  (rejectUnless (parent.slot < block.slot)
    "block is not from a higher slot than its parent").andThenM fun _ => do
  let finalizedBlock ← store.getCheckpointBlock block.parentRoot store.finalizedCheckpoint.epoch
  (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
    "finalized checkpoint is not an ancestor of block").andThenM fun _ =>
  (rejectUnless (bid.blobKzgCommitments.data.size ≤
      (config.getBlobParameters (computeEpochAtSlot preset block.slot)).maxBlobsPerBlock.toNat)
    "too many blob kzg commitments").andThenM fun _ =>
  (rejectUnless (bid.parentBlockRoot == block.parentRoot)
    "bid's parent does not equal block's parent").andThenM fun _ => do
  let advanced ← (processSlots config checks parentState block.slot).mapError .transition
  let expected ← (getBeaconProposerIndex advanced).mapError .accessor
  (rejectUnless (block.proposerIndex == expected)
    "block proposer_index does not match expected proposer").andThenM fun _ =>
  return rejectUnless (full || bid.parentBlockHash == advanced.latestBlockHash gloas)
    "bid does not build on the parent's execution head"

/-- The checks of a signed block on its topic, at a time in milliseconds.

The statuses are those of the payloads of known blocks, which the checks read from Bellatrix.

From Gloas the block carries a bid, and the Gloas checks read none of the statuses. -/
def validateBeaconBlock (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (statuses : PayloadStatuses)
    (signed : SignedBeaconBlock preset fork)
    (currentTimeMs : UInt64) : Except ForkChoiceError ValidationResult :=
  if gloas : .glamsterdam ≤ fork then
    validateGloasBeaconBlock config checks seen store gloas signed currentTimeMs
  else
  let before : fork < .glamsterdam := Nat.lt_of_not_le gloas
  let block := signed.message
  (ignoreUnless (!seen.proposerSlots.contains (block.slot, block.proposerIndex))
    "block is not the first valid block for this slot and proposer").andThenM fun _ => do
  let future ← store.isFutureSlot config block.slot currentTimeMs
  (ignoreUnless (!future) "block is from a future slot").andThenM fun _ => do
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot < block.slot)
    "block is not from a slot greater than the latest finalized slot").andThenM fun _ => do
  match store.blocks[block.parentRoot]? with
  | none => return .ignore "block's parent has not been seen"
  | some parent => do
  let status := statuses.get block.parentRoot
  match store.blockStates[block.parentRoot]? with
  | none => parentWithoutStateOutcome store before block.body status
  | some parentState => do
  (ignoreUnless (!(decide (.shapella ≤ fork)) || status != PAYLOAD_STATUS_INVALIDATED)
    "block's parent is valid and its payload is invalid").andThenM fun _ => do
  let state ← store.headState config
  match state.validators.data[block.proposerIndex.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer => do
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER block.slot block
    proposer.pubkey signed.signature
  (rejectUnless valid "invalid proposer signature").andThenM fun _ => do
  (← payloadOutcome config state before block status).andThenM fun _ =>
  (rejectUnless (parent.slot < block.slot)
    "block is not from a higher slot than its parent").andThenM fun _ => do
  let finalizedBlock ← store.getCheckpointBlock block.parentRoot store.finalizedCheckpoint.epoch
  (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
    "finalized checkpoint is not an ancestor of block").andThenM fun _ =>
  (rejectUnless (blobCountWithinLimit config before block)
    "too many blob kzg commitments").andThenM fun _ => do
  let expected ← expectedProposer config checks parentState block.slot
  return rejectUnless (block.proposerIndex == expected)
    "block proposer_index does not match expected proposer"

/-- The keys after a valid block: its slot and its proposer. -/
def Seen.recordBeaconBlock (seen : Seen) (signed : SignedBeaconBlock preset fork) : Seen :=
  { seen with
    proposerSlots := (signed.message.slot, signed.message.proposerIndex) :: seen.proposerSlots }

end EthLib.Consensus
