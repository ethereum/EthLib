module

public import EthLib.Consensus.Builders
public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Transition.Basic
public import EthLib.Consensus.Transition.Execution

/-!
# `Consensus.Transition.Payload`

From Gloas: the bid of a block for its execution payload, and the signature checks of payloads.

A builder bids for the payload of a slot, and later reveals the payload in an envelope.

The block of the slot carries the bid, which the state keeps until the next block.

A bid with a value records a payment to the proposer, which the builder owes from then on.

A proposer may build its own payload, for no value and with no signature.

Both messages carry a signature under the builder domain, in the current epoch of the state.

A bid is signed by its builder.

An envelope is signed by its builder, or by the proposer of the latest block for a self-build.

The signature checks are an argument, as for the other steps of the transition.

A builder or proposer index outside its registry is an error.

A node checks an envelope against the state after its block, before it trusts the payload.

[EIP-7732] adds the bid, the envelope and the builder domain.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-- The root that a builder signs for a message, under the builder domain of an epoch.

The epoch is by default the current epoch of the state. -/
def builderSigningRoot {α : Type} [Serialization.Ssz.SszType α] (config : Config)
    (state : BeaconState preset fork) (message : α) (epoch : Option Epoch := none) :
    Except TransitionError Root := do
  -- The signing root of the message under `DOMAIN_BEACON_BUILDER` at the epoch.
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_BUILDER epoch)
  liftSsz (computeSigningRoot message domain)

/-- Whether a signed bid carries the signature of its builder, in the current epoch. -/
def verifyExecutionPayloadBidSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) : Except TransitionError Bool := do
  -- The signature verifies under the key of the builder of the bid.
  let builder ← liftAccessor (getBuilder state gloas signed.message.builderIndex)
  let signingRoot ← builderSigningRoot config state signed.message
  return checks.verify builder.pubkey (packBytes signingRoot)
    signed.signature

/-- The key that signs an envelope. -/
def envelopeSignerKey (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (builderIndex : BuilderIndex) : Except TransitionError BLSPubkey :=
  -- For a self-build, the key of the proposer of the latest block.
  if builderIndex = BUILDER_INDEX_SELF_BUILD then
    return (← liftAccessor (getValidator state state.latestBlockHeader.proposerIndex)).pubkey
  -- Else the key of the builder.
  else return (← liftAccessor (getBuilder state gloas builderIndex)).pubkey

/-- Whether a signed envelope carries the signature of its signer, in the current epoch. -/
def verifyExecutionPayloadEnvelopeSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Except TransitionError Bool := do
  -- The signature verifies under the key of the signer, in the current epoch.
  let pubkey ← envelopeSignerKey state gloas signed.message.builderIndex
  let signingRoot ← builderSigningRoot config state signed.message
  return checks.verify pubkey (packBytes signingRoot) signed.signature

/-- From Gloas: the payload request of an envelope, for the execution layer.

A request holds a bounded number of versioned hashes. -/
def ExecutionPayloadEnvelope.newPayloadRequest (envelope : ExecutionPayloadEnvelope preset fork)
    (commitments : Array Cryptography.Kzg.KZGCommitment)
    (bound : commitments.size ≤ preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) :
    NewPayloadRequest preset fork where
  executionPayload := envelope.payload
  -- The versioned hashes of the commitments of the bid, in order.
  versionedHashes _ := ⟨commitments.map commitmentVersionedHash, by simpa using bound⟩
  parentBeaconBlockRoot _ := envelope.parentBeaconBlockRoot
  executionRequests _ := envelope.executionRequests

/-- From Gloas: check an envelope against the state after its block.

[EIP-7732] makes this a pure check: the beacon state changes only at the next block.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#state-transition
-/
def verifyExecutionPayloadEnvelope (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except TransitionError Unit := do
  let envelope := signed.message
  let payload := envelope.payload
  -- The signature of its signer verifies.
  let signatureValid ← verifyExecutionPayloadEnvelopeSignature config checks state gloas signed
  ensure (signatureValid = true)
    (.invalidEnvelopeSignature envelope.builderIndex envelope.beaconBlockRoot)
  -- It names the latest block, whose header takes the root of the state as its state root.
  let stateRoot ← liftSsz (hashTreeRoot state)
  let blockRoot ← liftSsz (hashTreeRoot { state.latestBlockHeader with stateRoot })
  ensure (envelope.beaconBlockRoot = blockRoot)
    (.envelopeWrongBlockRoot envelope.beaconBlockRoot blockRoot)
  -- It names the parent of that block.
  ensure (envelope.parentBeaconBlockRoot = state.latestBlockHeader.parentRoot)
    (.envelopeWrongParentRoot envelope.parentBeaconBlockRoot state.latestBlockHeader.parentRoot)
  -- It agrees with the bid of that block on the builder, the RANDAO mix and the gas limit.
  let bid := state.latestExecutionPayloadBid gloas
  ensure (envelope.builderIndex = bid.builderIndex)
    (.envelopeWrongBuilder envelope.builderIndex bid.builderIndex)
  ensure (payload.prevRandao = bid.prevRandao)
    (.wrongPayloadRandao payload.prevRandao bid.prevRandao)
  ensure (payload.gasLimit = bid.gasLimit) (.wrongPayloadGasLimit payload.gasLimit bid.gasLimit)
  -- It agrees on the block hash and on the root of the requests.
  ensure (payload.blockHash = bid.blockHash)
    (.wrongPayloadBlockHash payload.blockHash bid.blockHash)
  let requestsRoot ← liftSsz (hashTreeRoot envelope.executionRequests)
  ensure (requestsRoot = bid.executionRequestsRoot)
    (.wrongPayloadRequestsRoot requestsRoot bid.executionRequestsRoot)
  -- The payload is for the slot of the state, and extends the latest block hash.
  ensure (payload.slotNumber gloas = state.slot)
    (.wrongPayloadSlot (payload.slotNumber gloas) state.slot)
  ensure (payload.parentHash = state.latestBlockHash gloas)
    (.wrongPayloadParentHash payload.parentHash (state.latestBlockHash gloas))
  -- Its timestamp is the time of the slot.
  let time ← liftAccessor (liftArith (computeTimeAtSlot config state.genesisTime state.slot))
  ensure (payload.timestamp = time) (.wrongPayloadTimestamp payload.timestamp time)
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) gloas
  -- Its withdrawals are those that the state expects, compared by their roots.
  let withdrawalsRoot ← liftSsz (hashTreeRoot (payload.withdrawals capella))
  let expectedRoot ← liftSsz (hashTreeRoot (state.payloadExpectedWithdrawals gloas))
  let carried := (payload.withdrawals capella).data
  let expected := (state.payloadExpectedWithdrawals gloas).data
  ensure (withdrawalsRoot = expectedRoot)
    (.wrongWithdrawals (firstDifference carried expected) carried.size expected.size)
  -- The versioned hashes come from the commitments of the bid.
  --
  -- A request holds at most `MAX_BLOB_COMMITMENTS_PER_BLOCK` of them.
  let commitments := bid.blobKzgCommitments.data
  if bound : commitments.size ≤ preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat then
    -- The execution layer accepts the payload request.
    let request := envelope.newPayloadRequest commitments bound
    let accepted ← liftSsz (engine.verifyAndNotifyNewPayload request)
    ensure (accepted = true) (.invalidExecutionPayload payload.blockHash)
  else throw (.tooManyBlobCommitments commitments.size preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat)

/-- The position in the pending payments of a bid for a slot, in the second epoch of the list.

A preset with no slot in an epoch has no position, and is an error. -/
def bidPaymentPosition (preset : Preset) (slot : Slot) :
    Except TransitionError (Fin (2 * preset.SLOTS_PER_EPOCH.toNat)) :=
  if nonzero : preset.SLOTS_PER_EPOCH = 0 then throw (.accessor (.arith .divisionByZero))
  else
    -- `P + s mod P`, for the slot `s` and `P = SLOTS_PER_EPOCH`.
    return ⟨preset.SLOTS_PER_EPOCH.toNat + (slot % preset.SLOTS_PER_EPOCH).toNat, by
      have := toNat_mod_lt (i := slot) nonzero; omega⟩

/-- The checks of the builder of a bid. -/
def checkBidBuilder (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) : Except TransitionError Unit := do
  let bid := signed.message
  let builder := bid.builderIndex
  -- A self-built bid has a value of 0 and the point at infinity as its signature.
  --
  -- EIP-7732 specifies it.
  if builder = BUILDER_INDEX_SELF_BUILD then
    ensure (bid.value = 0 ∧ signed.signature = Signatures.G2_POINT_AT_INFINITY)
      (.selfBuildBidPaid bid.value)
  else
    -- Otherwise the builder is active.
    let active ← liftAccessor (isActiveBuilder state gloas builder)
    ensure (active = true) (.builderNotActive builder)
    -- It is a payload builder, of version `PAYLOAD_BUILDER_VERSION`.
    let version := (← liftAccessor (getBuilder state gloas builder)).version
    ensure (version = PAYLOAD_BUILDER_VERSION) (.notPayloadBuilder builder)
    -- Its balance covers the value of the bid.
    let covered ← liftAccessor (canBuilderCoverBid state gloas builder bid.value)
    ensure (covered = true) (.bidNotCovered builder)
    -- It signed the bid.
    let valid ← verifyExecutionPayloadBidSignature config checks state gloas signed
    ensure (valid = true) (.invalidBidSignature builder bid.slot)

/-- The checks of the bid of a block. -/
def checkExecutionPayloadBid (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) : Except TransitionError Unit := do
  -- Its builder passes its checks.
  checkBidBuilder config checks state gloas signed
  let bid := signed.message
  -- It commits to at most the blobs of a block, by the blob schedule at the current epoch.
  let limit := (config.getBlobParameters (getCurrentEpoch state)).maxBlobsPerBlock
  ensure (bid.blobKzgCommitments.data.size ≤ limit.toNat)
    (.tooManyBlobCommitments bid.blobKzgCommitments.data.size limit.toNat)
  -- It is for the slot `s` of the state, with `s` after `GENESIS_SLOT`.
  ensure (bid.slot = state.slot) (.bidWrongSlot bid.slot state.slot)
  ensure (GENESIS_SLOT < state.slot) .bidAtGenesis
  -- Its parent block hash is the latest block hash, and its block hash differs from it.
  ensure (bid.parentBlockHash = state.latestBlockHash gloas)
    (.bidWrongParentHash bid.parentBlockHash (state.latestBlockHash gloas))
  ensure (bid.blockHash ≠ bid.parentBlockHash) (.bidRepeatsParentHash bid.blockHash)
  -- Its parent block root is the block root at slot `s - 1`.
  let parentRoot ← liftAccessor (getBlockRootAtSlot state (state.slot - 1))
  ensure (bid.parentBlockRoot = parentRoot) (.bidWrongParentRoot bid.parentBlockRoot parentRoot)
  -- Its previous RANDAO is the mix of the current epoch.
  let mix ← liftAccessor (getRandaoMix state (getCurrentEpoch state))
  ensure (bid.prevRandao = mix) (.bidWrongRandao bid.prevRandao mix)

/-- The payment that a bid with a value owes to the proposer of its block. -/
def bidPayment (bid : ExecutionPayloadBid preset fork) (proposer : ValidatorIndex) :
    BuilderPendingPayment :=
  ⟨0, ⟨bid.feeRecipient, bid.value, bid.builderIndex⟩, proposer⟩

/-- The state with the payment of a bid recorded, when the bid has a value. -/
def recordBidPayment (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (bid : ExecutionPayloadBid preset fork) : Except TransitionError (BeaconState preset fork) :=
  -- A bid with a positive value records a payment to the proposer of the slot.
  --
  -- It sits at the slot's position in the second half of the pending payments: the current epoch.
  if 0 < bid.value then do
    let proposer ← liftAccessor (getBeaconProposerIndex state)
    let position ← bidPaymentPosition preset bid.slot
    let payments := (state.builderPendingPayments gloas).set position (bidPayment bid proposer)
    return { state with builderPendingPayments := fun _ => payments }
  else return state

/-- The state after the bid of a block. -/
def processExecutionPayloadBid (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- The bid passes its checks.
  checkExecutionPayloadBid config checks state gloas signed
  -- A bid with a value records its payment to the proposer.
  let state ← recordBidPayment state gloas signed.message
  -- The state keeps the bid.
  return { state with latestExecutionPayloadBid := fun _ => signed.message }

end EthLib.Consensus
