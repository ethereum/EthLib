module

public import EthLib.Consensus.BuilderApi.Registration

/-!
# `Consensus.BuilderApi.Bid`

From Bellatrix to Fulu, a proposer asks a builder for a bid on the payload of its slot.

The builder serves the request only when four rules hold, and then bids under its own key.

From Deneb the bid also carries the commitments to the blobs, and from Electra the requests.

The source gives no function that fills either, so the bid takes them as inputs.

The proposer accepts a bid only when three rules hold.

The [builder specification] gives the builder's rules, and its [validator document] the proposer's.

[`header.yaml`] gives the 200, 204, 400 and 500 responses to a request.

[builder specification]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/specs/bellatrix/builder.md#bidding
[validator document]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/specs/bellatrix/validator.md#bid-processing
[`header.yaml`]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/apis/builder/header.yaml
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
  -- Verify slot: the slot of the request is the slot of the state.
  if slot ≠ state.slot then return false
  -- Verify the key: it is that of a validator whose registration the builder keeps.
  if (registry.find? pubkey).isNone then return false
  -- Verify the key: it is that of the proposer of the slot.
  let index ← getBeaconProposerIndex state
  let proposer ← getValidator state index
  if pubkey ≠ proposer.pubkey then return false
  -- Verify parent hash: it is the block hash of the latest payload header of the state.
  return parentHash == (state.latestExecutionPayloadHeader range).blockHash

/-- From Bellatrix to Fulu: the status of a request for a header. -/
def getHeaderStatus (state : BeaconState preset fork) (range : HasBuilderApi fork)
    (registry : Registry) (slot : Slot) (parentHash : Hash32) (pubkey : BLSPubkey)
    (offered : Bool) : Nat :=
  match isEligibleForBid state range registry slot parentHash pubkey with
  -- A proposer or validator that cannot be found is an internal error, 500, which the API lists.
  | .error _ => 500
  -- The API: a request that the builder does not serve is invalid, and gets 400.
  | .ok false => 400
  -- The API: 200 with the bid, and 204 when the builder cannot produce a header.
  | .ok true => if offered then 200 else 204

/-- The bid of a builder on a payload: its header, the value to the proposer and the builder's key.

From Deneb the commitments to the blobs, and from Electra the requests, are given as they are.

It is defined at every fork, and the Builder API uses it from Bellatrix to Fulu.

It fails when the header of the payload cannot be computed, which never happens. -/
def getBid (payload : ExecutionPayload preset fork) (value : U256) (pubkey : BLSPubkey)
    (blobKzgCommitments : Since .dencun fork (BlobKZGCommitments preset fork))
    (executionRequests : Since .pectra fork (ExecutionRequests preset fork)) :
    Except Err (BuilderBid preset fork) := do
  -- Constructing the bid: the header of the payload, its lists replaced by their roots.
  --
  -- Then the commitments and the requests as given, the value, and the key of the builder.
  return ⟨← payload.header, blobKzgCommitments, executionRequests, value, pubkey⟩

/-- Why a proposer refuses a bid. -/
inductive BidError where
  /-- The parent hash of the header is not the latest block hash of the state.

  The error gives the latest block hash, then the parent hash of the header. -/
  | wrongParentHash (expected actual : Hash32)
  /-- The fee recipient of the header is not the one the proposer registered.

  The error gives the registered fee recipient, then that of the header. -/
  | wrongFeeRecipient (expected actual : ExecutionAddress)
  /-- The signature does not verify against the builder key that the error gives. -/
  | badSignature (pubkey : BLSPubkey)
  /-- The signing root cannot be computed. -/
  | root (fault : Err)
  deriving DecidableEq, Repr

/-- From Bellatrix to Fulu: whether a proposer accepts a signed bid.

The state is that of the proposal, before the block under construction.

The fee recipient is the one the proposer registered last.

The rules run in the order of the source, so the first that fails names the error. -/
def processBid (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (range : HasBuilderApi fork) (signed : SignedBuilderBid preset fork)
    (feeRecipient : ExecutionAddress) : Except BidError Unit := do
  let header := signed.message.header
  -- Verify the header: its parent hash is the block hash of the latest payload header.
  unless header.parentHash = (state.latestExecutionPayloadHeader range).blockHash do
    throw (.wrongParentHash (state.latestExecutionPayloadHeader range).blockHash header.parentHash)
  -- Its fee recipient is the one that the proposer registered last.
  unless header.feeRecipient = feeRecipient do
    throw (.wrongFeeRecipient feeRecipient header.feeRecipient)
  -- Verify the bid signature, under the builder key of the bid.
  match verifyBuilderBidSignature config checks signed with
  | .error fault => throw (.root fault)
  | .ok false => throw (.badSignature signed.message.pubkey)
  | .ok true => pure ()

end EthLib.Consensus.BuilderApi
