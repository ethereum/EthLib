module

public import EthLib.Consensus.Builders
public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Transition.Basic

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
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_BUILDER epoch)
  liftSsz (computeSigningRoot message domain)

/-- Whether a signed bid carries the signature of its builder, in the current epoch. -/
def verifyExecutionPayloadBidSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) : Except TransitionError Bool := do
  let builder ← liftAccessor (getBuilder state gloas signed.message.builderIndex)
  let signingRoot ← builderSigningRoot config state signed.message
  return checks.verify (packBytes builder.pubkey) (packBytes signingRoot)
    (packBytes signed.signature)

/-- The key that signs an envelope.

It is the key of the builder, or for a self-build the key of the proposer of the latest block. -/
def envelopeSignerKey (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (builderIndex : BuilderIndex) : Except TransitionError BLSPubkey :=
  if builderIndex = BUILDER_INDEX_SELF_BUILD then
    return (← liftAccessor (getValidator state state.latestBlockHeader.proposerIndex)).pubkey
  else return (← liftAccessor (getBuilder state gloas builderIndex)).pubkey

/-- Whether a signed envelope carries the signature of its signer, in the current epoch. -/
def verifyExecutionPayloadEnvelopeSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Except TransitionError Bool := do
  let pubkey ← envelopeSignerKey state gloas signed.message.builderIndex
  let signingRoot ← builderSigningRoot config state signed.message
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature)

/-- Whether a signature is the encoding of the point at infinity, which no key produces. -/
def isInfinitySignature (signature : BLSSignature) : Bool :=
  signature.toArray == Signatures.G2_POINT_AT_INFINITY.data

/-- The position in the pending payments of a bid for a slot, in the second epoch of the list.

A preset with no slot in an epoch has no position, and is an error. -/
def bidPaymentPosition (preset : Preset) (slot : Slot) :
    Except TransitionError (Fin (2 * preset.SLOTS_PER_EPOCH.toNat)) :=
  if nonzero : preset.SLOTS_PER_EPOCH = 0 then throw (.accessor (.arith .divisionByZero))
  else
    return ⟨preset.SLOTS_PER_EPOCH.toNat + (slot % preset.SLOTS_PER_EPOCH).toNat, by
      have := toNat_mod_lt (i := slot) nonzero; omega⟩

/-- The checks of the builder of a bid.

A self-built bid must have no value and the signature at infinity.

Otherwise its builder must be an active payload builder that can pay it, and must have signed it.
-/
def checkBidBuilder (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) : Except TransitionError Unit := do
  let bid := signed.message
  let builder := bid.builderIndex
  if builder = BUILDER_INDEX_SELF_BUILD then
    ensure (bid.value = 0 ∧ isInfinitySignature signed.signature = true) .selfBuildBidPaid
  else
    let active ← liftAccessor (isActiveBuilder state gloas builder)
    ensure (active = true) (.builderNotActive builder)
    let version := (← liftAccessor (getBuilder state gloas builder)).version
    ensure (version = PAYLOAD_BUILDER_VERSION) (.notPayloadBuilder builder)
    let covered ← liftAccessor (canBuilderCoverBid state gloas builder bid.value)
    ensure (covered = true) (.bidNotCovered builder)
    let valid ← verifyExecutionPayloadBidSignature config checks state gloas signed
    ensure (valid = true) .invalidBidSignature

/-- The checks of the bid of a block.

Its builder must pass its checks.

The bid must commit to at most the blobs of a block, at the slot of the state after genesis.

It must extend the latest payload with a new one, on the previous block and the current RANDAO mix.
-/
def checkExecutionPayloadBid (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) : Except TransitionError Unit := do
  checkBidBuilder config checks state gloas signed
  let bid := signed.message
  let limit := (config.getBlobParameters (getCurrentEpoch state)).maxBlobsPerBlock
  ensure (bid.blobKzgCommitments.data.size ≤ limit.toNat) .tooManyBlobCommitments
  ensure (bid.slot = state.slot) (.bidWrongSlot bid.slot state.slot)
  ensure (GENESIS_SLOT < state.slot) .bidAtGenesis
  ensure (bid.parentBlockHash = state.latestBlockHash gloas) .bidWrongParentHash
  ensure (bid.blockHash ≠ bid.parentBlockHash) .bidRepeatsParentHash
  let parentRoot ← liftAccessor (getBlockRootAtSlot state (state.slot - 1))
  ensure (bid.parentBlockRoot = parentRoot) .bidWrongParentRoot
  let mix ← liftAccessor (getRandaoMix state (getCurrentEpoch state))
  ensure (bid.prevRandao = mix) .bidWrongRandao

/-- The payment that a bid with a value owes to the proposer of its block. -/
def bidPayment (bid : ExecutionPayloadBid preset fork) (proposer : ValidatorIndex) :
    BuilderPendingPayment :=
  ⟨0, ⟨bid.feeRecipient, bid.value, bid.builderIndex⟩, proposer⟩

/-- The state with the payment of a bid recorded, when the bid has a value.

The payment goes to the proposer of the slot, at the slot's position in the next epoch. -/
def recordBidPayment (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (bid : ExecutionPayloadBid preset fork) : Except TransitionError (BeaconState preset fork) :=
  if 0 < bid.value then do
    let proposer ← liftAccessor (getBeaconProposerIndex state)
    let position ← bidPaymentPosition preset bid.slot
    let payments := (state.builderPendingPayments gloas).set position (bidPayment bid proposer)
    return { state with builderPendingPayments := fun _ => payments }
  else return state

/-- The state after the bid of a block.

The bid must pass its checks.

A bid with a value records its payment to the proposer, and the state then keeps the bid. -/
def processExecutionPayloadBid (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  checkExecutionPayloadBid config checks state gloas signed
  let state ← recordBidPayment state gloas signed.message
  return { state with latestExecutionPayloadBid := fun _ => signed.message }

end EthLib.Consensus
