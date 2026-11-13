module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.Builders
public import EthLib.Consensus.Gossip.Bid
public import EthLib.Consensus.Transition.Payload
public import EthLib.Consensus.Containers.ProposerPreferences

/-!
# `Consensus.BuilderApi.GloasBid`

From Gloas, a proposer asks a builder for a bid with a request that names the parent block.

The builder serves the request only when six rules hold, in the order of the source.

The slot must be that of the builder's state, transitioned to that slot.

The key must be that of the proposer of the slot, and that proposer must be active.

The proposer must have sent its preferences on gossip.

The parent hash must be the block hash of the latest bid, or the latest block hash of the state.

The proposer may build on the parent with its payload or without it, so both are allowed.

The parent root must be the root of the latest block header of the state.

The proposer checks a bid it fetched with eight rules, then with the signature of the builder.

These are not the rules of gossip: the proposer reads its own state and its own fee recipient.

The proposer's cap on the execution payment limits how much of it counts in the value of a bid.

It is not a rule of validity.

The [builder specification] gives the builder's rules, and its [validator document] the proposer's.

[builder specification]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md#bidding
[validator document]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/validator.md#validating-a-signedexecutionpayloadbid
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- From Gloas: whether a block hash is that of the parent with its payload, or without it.

The latest bid of the state names the first, and the latest block hash the second. -/
def isParentBlockHash (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (parentHash : Hash32) : Bool :=
  parentHash == (state.latestExecutionPayloadBid gloas).blockHash ||
    parentHash == state.latestBlockHash gloas

/-- From Gloas: whether a builder serves a request for a bid.

The state is the builder's state, transitioned to the slot of the request.

The preferences are those that proposers sent on gossip, by validator index.

The rules run in the order of the source, and the first that fails gives false.

It gives an error when the proposer, its validator or the root of the latest header fails. -/
def isEligibleForBidGloas (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (preferences : ValidatorIndex → Option ProposerPreferences) (slot : Slot)
    (parentHash : Hash32) (parentRoot : Root) (pubkey : BLSPubkey) :
    Except TransitionError Bool := do
  if slot ≠ state.slot then return false
  let index ← liftAccessor (getBeaconProposerIndex state)
  let proposer ← liftAccessor (getValidator state index)
  if proposer.pubkey ≠ pubkey then return false
  if !isActiveValidator proposer (getCurrentEpoch state) then return false
  if (preferences index).isNone then return false
  if !isParentBlockHash state gloas parentHash then return false
  return parentRoot == (← liftSsz (SszType.hashTreeRoot state.latestBlockHeader))

/-- Why a proposer refuses a bid it fetched from a builder. -/
inductive ValidateBidError where
  /-- The builder of the bid is not active. -/
  | inactiveBuilder
  /-- The slot of the bid is not that of the state. -/
  | wrongSlot
  /-- The fee recipient of the bid is not the proposer's. -/
  | wrongFeeRecipient
  /-- The bid builds on neither the parent with its payload nor the parent without it. -/
  | wrongParentHash
  /-- The parent root of the bid is not the root of the latest block header. -/
  | wrongParentRoot
  /-- The RANDAO mix of the bid is not that of the current epoch. -/
  | wrongPrevRandao
  /-- The gas limit of the bid is not the step from the parent's limit toward the target. -/
  | incompatibleGasLimit
  /-- The builder cannot pay the value of the bid. -/
  | cannotCoverBid
  /-- A value that the rules read cannot be computed. -/
  | fault (error : TransitionError)
  deriving Repr

/-- From Gloas: whether a proposer accepts a signed bid that it fetched from a builder.

The state is that of the proposal, before the block under construction.

The preferences are the proposer's, and the gas limit is that of the parent payload of the bid.

The rules run in the order of the source, so the first that fails names the error.

The source asserts the rules and returns the signature check, so the signature gives the result. -/
def validateBid (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (preferences : ProposerPreferences) (parentGasLimit : UInt64)
    (signed : SignedExecutionPayloadBid preset fork) (feeRecipient : ExecutionAddress) :
    Except ValidateBidError Bool := do
  let bid := signed.message
  let lift {α : Type} (result : Except TransitionError α) : Except ValidateBidError α :=
    result.mapError .fault
  unless ← lift (liftAccessor (isActiveBuilder state gloas bid.builderIndex)) do
    throw .inactiveBuilder
  unless bid.slot = state.slot do throw .wrongSlot
  unless bid.feeRecipient = feeRecipient do throw .wrongFeeRecipient
  unless isParentBlockHash state gloas bid.parentBlockHash do throw .wrongParentHash
  unless bid.parentBlockRoot = (← lift (liftSsz (SszType.hashTreeRoot state.latestBlockHeader))) do
    throw .wrongParentRoot
  unless bid.prevRandao = (← lift (liftAccessor (getRandaoMix state (getCurrentEpoch state)))) do
    throw .wrongPrevRandao
  unless ← lift (liftAccessor (liftArith
      (isGasLimitTargetCompatible parentGasLimit bid.gasLimit preferences.targetGasLimit))) do
    throw .incompatibleGasLimit
  if 0 < bid.value then
    unless ← lift (liftAccessor (canBuilderCoverBid state gloas bid.builderIndex bid.value)) do
      throw .cannotCoverBid
  lift (verifyExecutionPayloadBidSignature config checks state gloas signed)

end EthLib.Consensus.BuilderApi
