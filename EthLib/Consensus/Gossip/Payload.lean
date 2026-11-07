module

public import EthLib.Consensus.Gossip.Seen
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.Gossip.Payload`

From Gloas: gossip validation of the envelopes of payloads and of the votes on payloads.

A builder reveals the payload of a block in a signed envelope, after the block.

The envelope must match the bid of that block, and its signer must have signed it.

A member of the payload timeliness committee votes on whether the payload of a block came on time.

Its vote is for the current slot, and on a block of that slot.

The first valid envelope of a builder for a block passes, and a later one is ignored.

So does the first valid vote of a member at a slot.

Some steps of the rule can fail, such as a root, or an addition out of range.

Such a failure is an error rather than an outcome.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Envelopes -/

/-- From Gloas: the checks of the counts of the requests of a payload, each against its limit.

The types of the lists bound none of them from Gloas, so gossip checks each count. -/
def checkExecutionRequestsLimits (gloas : .glamsterdam ≤ fork)
    (requests : ExecutionRequests preset fork) : ValidationResult :=
  (rejectUnless (requests.withdrawals.data.size ≤ preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD.toNat)
    "too many withdrawal requests").andThen fun _ =>
  (rejectUnless (requests.consolidations.data.size ≤
    preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat)
    "too many consolidation requests").andThen fun _ =>
  (rejectUnless ((requests.builderDeposits gloas).data.size ≤
    preset.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD.toNat)
    "too many builder deposit requests").andThen fun _ =>
  rejectUnless ((requests.builderExits gloas).data.size ≤
    preset.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD.toNat) "too many builder exit requests"

/-- From Gloas: the checks of a signed envelope on its topic.

The first valid envelope of a builder for a block passes, and a later one is ignored.

The block must be known, and is ignored otherwise; it must have a state, and is rejected otherwise.

A payload from a slot before the first slot of the finalized epoch is ignored.

The payload must be for the slot of the block, and the envelope must match the bid of the block.

The bid fixes the builder, the hash of the payload and the root of its requests.

The counts of the requests and of the withdrawals must be within their limits.

The signer of the envelope must have signed it, in the state after the block. -/
def validateExecutionPayloadEnvelope (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except ForkChoiceError ValidationResult :=
  let envelope := signed.message
  let payload := envelope.payload
  let root := envelope.beaconBlockRoot
  (ignoreUnless (!seen.executionPayloadEnvelopes.contains (root, envelope.builderIndex))
    "already seen envelope for this block root from this builder").andThenM fun _ =>
  match store.blocks[root]? with
  | none => return .ignore "envelope's block has not been seen"
  | some block =>
  match store.blockStates[root]? with
  | none => return .reject "envelope's block failed validation"
  | some state => do
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot ≤ payload.slotNumber gloas)
    "envelope is from a slot before the latest finalized slot").andThenM fun _ => do
  let bid := (block.body.signedExecutionPayloadBid gloas).message
  (rejectUnless (block.slot == payload.slotNumber gloas)
    "block's slot does not match payload's slot number").andThenM fun _ =>
  (rejectUnless (envelope.builderIndex == bid.builderIndex)
    "envelope's builder index does not match the bid's builder index").andThenM fun _ =>
  (rejectUnless (payload.blockHash == bid.blockHash)
    "payload's block hash does not match the bid's block hash").andThenM fun _ => do
  let requestsRoot ← (SszType.hashTreeRoot envelope.executionRequests).mapError .ssz
  (rejectUnless (requestsRoot == bid.executionRequestsRoot)
    "envelope's execution requests root does not match the bid's").andThenM fun _ =>
  (checkExecutionRequestsLimits gloas envelope.executionRequests).andThenM fun _ =>
  let withdrawals := payload.withdrawals (Nat.le_trans (by decide) gloas)
  (rejectUnless (withdrawals.data.size ≤ preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat)
    "too many withdrawals").andThenM fun _ => do
  let valid ←
    (verifyExecutionPayloadEnvelopeSignature config checks state gloas signed).mapError .transition
  return rejectUnless valid "invalid envelope signature"

/-- The keys after a valid envelope: its block root and its builder.

The gas limit of its payload is kept too, by the hash of the payload. -/
def Seen.recordExecutionPayloadEnvelope (seen : Seen)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Seen :=
  let envelope := signed.message
  { seen with
    executionPayloadEnvelopes :=
      (envelope.beaconBlockRoot, envelope.builderIndex) :: seen.executionPayloadEnvelopes
    executionPayloadGasLimits :=
      (envelope.payload.blockHash, envelope.payload.gasLimit) :: seen.executionPayloadGasLimits }

/-! ## Votes on payloads -/

/-- From Gloas: the checks of a vote of the payload timeliness committee, at a time in ms.

The slot of the vote must not come before Gloas.

The first valid vote of a member at a slot passes, and a later one is ignored.

The vote must be for the current slot, and is ignored otherwise.

Its block must be known, and is ignored otherwise; it must have a state, and is rejected otherwise.

A block at another slot than the vote is ignored.

The member must be a validator of the head state, and a member of the committee of the slot there.

It must have signed the vote in the epoch of the slot. -/
def validatePayloadAttestationMessage (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork) (message : PayloadAttestationMessage)
    (currentTimeMs : UInt64) : Except ForkChoiceError ValidationResult :=
  let data := message.data
  let index := message.validatorIndex
  (rejectUnless (config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset data.slot)
    "payload attestation's slot is pre-gloas").andThenM fun _ =>
  (ignoreUnless (!seen.payloadAttestationValidators.contains (data.slot, index))
    "already seen payload attestation from this validator").andThenM fun _ => do
  let current ← store.isCurrentSlot config data.slot currentTimeMs
  (ignoreUnless current "payload attestation is not for the current slot").andThenM fun _ =>
  match store.blocks[data.beaconBlockRoot]? with
  | none => return .ignore "payload attestation's block has not been seen"
  | some block =>
  match store.blockStates[data.beaconBlockRoot]? with
  | none => return .reject "payload attestation's block failed validation"
  | some _ =>
  (ignoreUnless (block.slot == data.slot)
    "payload attestation's block is not at the assigned slot").andThenM fun _ => do
  let state ← store.headState config
  match state.validators.data[index.toNat]? with
  | none => return .reject "validator index out of range"
  | some validator => do
  let committee ← (getPtc config state gloas data.slot).mapError .accessor
  (rejectUnless (committee.toList.contains index)
    "validator is not in the payload timeliness committee").andThenM fun _ => do
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_PTC_ATTESTER data.slot data
    validator.pubkey message.signature
  return rejectUnless valid "invalid payload attestation signature"

/-- The keys after a valid vote on a payload: its slot and its member. -/
def Seen.recordPayloadAttestationMessage (seen : Seen) (message : PayloadAttestationMessage) :
    Seen :=
  { seen with
    payloadAttestationValidators :=
      (message.data.slot, message.validatorIndex) :: seen.payloadAttestationValidators }

end EthLib.Consensus
