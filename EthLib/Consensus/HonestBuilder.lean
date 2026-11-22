module

public import EthLib.Consensus.Transition.Payload

/-!
# `Consensus.HonestBuilder`

From Gloas: the bid and the envelope of an honest builder, and the signatures on them.

A builder bids for a payload that it built, on a state.

The bid takes its parent hash, block hash, RANDAO mix and gas limit from the payload.

Its parent root is the root of the latest block header of the state.

It commits to the root of the requests of the payload.

It asks for no payment on the execution layer.

A proposer may build its own payload, with a bid from the reserved builder index.

That bid has no value, and the signature at infinity.

Once a block carries the bid, the envelope reveals the payload and its requests.

It names the builder of the bid, the root of the block and the parent of the block.

A builder signs a bid under the builder domain of the epoch of the bid's slot.

It signs an envelope under the builder domain of the current epoch of the state.

The payload, its requests and the commitments of its blobs come from the execution layer.

The builder chooses the slot, the fee recipient and the value of its bid.

Those choices read the fork choice and the network, so they are all inputs here.

The gossip of the bid and of the envelope is not specified here.

[EIP-7732] describes the honest builder.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#honest-validator-and-builder-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- From Gloas: the bid of a builder for a payload that it built on a state.

The slot, the fee recipient, the builder and the value are given.

From Heze the bits of the inclusion lists that the builder saw are given too.

It fails when the root of the header or of the requests fails. -/
def getExecutionPayloadBid (state : BeaconState preset fork)
    (payload : ExecutionPayload preset fork) (requests : ExecutionRequests preset fork)
    (blobKzgCommitments : BlobKZGCommitments preset fork) (slot : Slot)
    (feeRecipient : ExecutionAddress) (builderIndex : BuilderIndex) (value : Gwei)
    (inclusionListBits : Since .hegota fork (InclusionListBits preset)) :
    Except Err (ExecutionPayloadBid preset fork) := do
  -- The parent root is the root of the latest block header of the state.
  let parentBlockRoot ← SszType.hashTreeRoot state.latestBlockHeader
  -- The root of the requests of the payload.
  let executionRequestsRoot ← SszType.hashTreeRoot requests
  return {
    -- It builds on the parent hash of the payload.
    parentBlockHash := payload.parentHash
    parentBlockRoot := parentBlockRoot
    -- It commits to the block hash, the RANDAO mix and the gas limit of the payload.
    blockHash := payload.blockHash
    prevRandao := payload.prevRandao
    feeRecipient := feeRecipient
    gasLimit := payload.gasLimit
    builderIndex := builderIndex
    slot := slot
    value := value
    -- It asks for no payment on the execution layer.
    executionPayment := 0
    -- It commits to the commitments of the blobs of the payload, and to the root of its requests.
    blobKzgCommitments := blobKzgCommitments
    executionRequestsRoot := executionRequestsRoot
    inclusionListBits := inclusionListBits }

/-- From Gloas: the signed bid of a proposer that builds its own payload.

It fails when the bid fails. -/
def getSelfBuiltExecutionPayloadBid (state : BeaconState preset fork)
    (payload : ExecutionPayload preset fork) (requests : ExecutionRequests preset fork)
    (blobKzgCommitments : BlobKZGCommitments preset fork) (feeRecipient : ExecutionAddress)
    (inclusionListBits : Since .hegota fork (InclusionListBits preset)) :
    Except Err (SignedExecutionPayloadBid preset fork) := do
  -- The bid is for the slot of the state.
  --
  -- Its builder index is `BUILDER_INDEX_SELF_BUILD` and its value 0, as EIP-7732 specifies.
  let bid ← getExecutionPayloadBid state payload requests blobKzgCommitments state.slot
    feeRecipient BUILDER_INDEX_SELF_BUILD 0 inclusionListBits
  -- Its signature is the point at infinity, as EIP-7732 specifies.
  return ⟨bid, Signatures.G2_POINT_AT_INFINITY⟩

/-- From Gloas: the envelope that reveals a payload and its requests, after the block of its bid.

It fails when the root of the block fails. -/
def getExecutionPayloadEnvelope (block : BeaconBlock preset fork) (gloas : .glamsterdam ≤ fork)
    (payload : ExecutionPayload preset fork) (requests : ExecutionRequests preset fork) :
    Except Err (ExecutionPayloadEnvelope preset fork) := do
  let beaconBlockRoot ← SszType.hashTreeRoot block
  return {
    payload := payload
    executionRequests := requests
    -- It names the builder of the bid of the block.
    builderIndex := (block.body.signedExecutionPayloadBid gloas).message.builderIndex
    -- It names the root of the block, and the parent root of the block.
    beaconBlockRoot := beaconBlockRoot
    parentBeaconBlockRoot := block.parentRoot }

/-- An error of a builder that signs a message. -/
inductive BuilderSigningError where
  /-- The domain or the root of the message has no value. -/
  | root (error : TransitionError)
  /-- The BLS signature fails. -/
  | bls (error : BlsError)

/-- The signature of a bid by a builder with a secret key. -/
def getExecutionPayloadBidSignature (config : Config) (state : BeaconState preset fork)
    (bid : ExecutionPayloadBid preset fork) (key : Signatures.SecretKey) :
    Except BuilderSigningError BLSSignature := do
  -- The signing root under `DOMAIN_BEACON_BUILDER`, at the epoch of the slot of the bid.
  let root ← (builderSigningRoot config state bid
    (some (computeEpochAtSlot preset bid.slot))).mapError .root
  -- The BLS signature of that root with the key.
  (Signatures.sign key (packBytes root)).mapError .bls

/-- The signature of an envelope by a builder with a secret key. -/
def getExecutionPayloadEnvelopeSignature (config : Config) (state : BeaconState preset fork)
    (envelope : ExecutionPayloadEnvelope preset fork) (key : Signatures.SecretKey) :
    Except BuilderSigningError BLSSignature := do
  -- The signing root under `DOMAIN_BEACON_BUILDER`, at the current epoch of the state.
  let root ← (builderSigningRoot config state envelope
    (some (computeEpochAtSlot preset state.slot))).mapError .root
  -- The BLS signature of that root with the key.
  (Signatures.sign key (packBytes root)).mapError .bls

end EthLib.Consensus
