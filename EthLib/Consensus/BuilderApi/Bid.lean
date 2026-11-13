module

public import EthLib.Consensus.BuilderApi.Registration

/-!
# `Consensus.BuilderApi.Bid`

From Bellatrix to Fulu, a proposer asks a builder for a bid on the payload of its slot.

The builder serves the request only when four rules hold, in the order of the source.

The slot must be that of the builder's state, transitioned to that slot.

The key must have a registration that the builder keeps.

The key must be that of the proposer of the slot.

The parent hash must be the block hash of the latest payload header of the state.

The builder then bids with the header of its payload, the value and its own key.

From Deneb the bid also carries the commitments to the blobs, and from Electra the requests.

The source gives no function that fills either, so the bid takes them as inputs.

The proposer accepts a bid only when three rules hold, in the order of the source.

The parent hash of the header must be the block hash of the latest payload header of the state.

The fee recipient of the header must be the one the proposer registered.

The signature of the builder must verify.

The source calls the signature check without asserting its result, and EthLib refuses a bid that fails it.

The [builder specification] gives the builder's rules, and its [validator document] the proposer's.

[`header.yaml`] gives the 200, 204, 400 and 500 responses to a request.

[builder specification]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/builder.md#bidding
[validator document]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/validator.md#bid-processing
[`header.yaml`]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/apis/builder/header.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- From Bellatrix to Fulu: whether a builder serves a request for a bid.

The state is the builder's state, transitioned to the slot of the request.

The rules run in the order of the source, and the first that fails gives false.

It fails when the proposer of the state or its validator cannot be found. -/
def isEligibleForBid (state : BeaconState preset fork) (range : HasBuilderApi fork)
    (registry : Registry) (slot : Slot) (parentHash : Hash32) (pubkey : BLSPubkey) :
    Except AccessorError Bool := do
  if slot ≠ state.slot then return false
  if (registry.find? pubkey).isNone then return false
  let index ← getBeaconProposerIndex state
  let proposer ← getValidator state index
  if pubkey ≠ proposer.pubkey then return false
  return parentHash == (state.latestExecutionPayloadHeader range).blockHash

/-- From Bellatrix to Fulu: the status of a request for a header.

It is 500, an internal error, when the proposer of the slot or its validator cannot be found.

It is 400 when the builder does not serve the request.

Otherwise it is 200 when the builder offers a bid, and 204 when it has none. -/
def getHeaderStatus (state : BeaconState preset fork) (range : HasBuilderApi fork)
    (registry : Registry) (slot : Slot) (parentHash : Hash32) (pubkey : BLSPubkey)
    (offered : Bool) : Nat :=
  match isEligibleForBid state range registry slot parentHash pubkey with
  | .error _ => 500
  | .ok false => 400
  | .ok true => if offered then 200 else 204

/-- The bid of a builder on a payload: its header, the value to the proposer and the builder's key.

From Deneb the commitments to the blobs, and from Electra the requests, are given as they are.

It is defined at every fork, and the Builder API uses it from Bellatrix to Fulu.

It fails when the header of the payload cannot be computed, which never happens. -/
def getBid (payload : ExecutionPayload preset fork) (value : U256) (pubkey : BLSPubkey)
    (blobKzgCommitments : Since .dencun fork (BlobKZGCommitments preset fork))
    (executionRequests : Since .pectra fork (ExecutionRequests preset fork)) :
    Except Err (BuilderBid preset fork) := do
  return ⟨← payload.header, blobKzgCommitments, executionRequests, value, pubkey⟩

/-- Why a proposer refuses a bid. -/
inductive BidError where
  /-- The parent hash of the header is not the latest block hash of the state. -/
  | wrongParentHash
  /-- The fee recipient of the header is not the one the proposer registered. -/
  | wrongFeeRecipient
  /-- The signature does not verify. -/
  | badSignature
  /-- The signing root cannot be computed. -/
  | root (fault : Err)
  deriving DecidableEq, Repr

/-- From Bellatrix to Fulu: whether a proposer accepts a signed bid.

The state is that of the proposal, before the block under construction.

The fee recipient is the one the proposer registered last.

The rules run in the order of the source, so the first that fails names the error.

The source does not assert the signature check, and EthLib refuses a bid whose signature does not verify. -/
def processBid (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (range : HasBuilderApi fork) (signed : SignedBuilderBid preset fork)
    (feeRecipient : ExecutionAddress) : Except BidError Unit := do
  let header := signed.message.header
  unless header.parentHash = (state.latestExecutionPayloadHeader range).blockHash do
    throw .wrongParentHash
  unless header.feeRecipient = feeRecipient do throw .wrongFeeRecipient
  match verifyBuilderBidSignature config checks signed with
  | .error fault => throw (.root fault)
  | .ok false => throw .badSignature
  | .ok true => pure ()

end EthLib.Consensus.BuilderApi
