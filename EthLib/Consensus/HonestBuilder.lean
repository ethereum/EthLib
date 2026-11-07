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

It builds on the parent hash of the payload, and on the root of the latest block header.

It commits to the block hash, the RANDAO mix and the gas limit of the payload.

It also commits to the root of the requests of the payload, and to the commitments of its blobs.

The slot, the fee recipient, the builder and the value are given.

It asks for no payment on the execution layer.

From Heze the bits of the inclusion lists that the builder saw are given too.

It fails when the root of the header or of the requests fails. -/
def getExecutionPayloadBid (state : BeaconState preset fork)
    (payload : ExecutionPayload preset fork) (requests : ExecutionRequests preset fork)
    (blobKzgCommitments : BlobKZGCommitments preset fork) (slot : Slot)
    (feeRecipient : ExecutionAddress) (builderIndex : BuilderIndex) (value : Gwei)
    (inclusionListBits : Since .hegota fork (InclusionListBits preset)) :
    Except Err (ExecutionPayloadBid preset fork) := do
  let parentBlockRoot ← SszType.hashTreeRoot state.latestBlockHeader
  let executionRequestsRoot ← SszType.hashTreeRoot requests
  return {
    parentBlockHash := payload.parentHash
    parentBlockRoot := parentBlockRoot
    blockHash := payload.blockHash
    prevRandao := payload.prevRandao
    feeRecipient := feeRecipient
    gasLimit := payload.gasLimit
    builderIndex := builderIndex
    slot := slot
    value := value
    executionPayment := 0
    blobKzgCommitments := blobKzgCommitments
    executionRequestsRoot := executionRequestsRoot
    inclusionListBits := inclusionListBits }

/-- From Gloas: the signed bid of a proposer that builds its own payload.

The bid is for the slot of the state, from the reserved builder index, with no value.

Its signature is the signature at infinity.

It fails when the bid fails. -/
def getSelfBuiltExecutionPayloadBid (state : BeaconState preset fork)
    (payload : ExecutionPayload preset fork) (requests : ExecutionRequests preset fork)
    (blobKzgCommitments : BlobKZGCommitments preset fork) (feeRecipient : ExecutionAddress)
    (inclusionListBits : Since .hegota fork (InclusionListBits preset)) :
    Except Err (SignedExecutionPayloadBid preset fork) := do
  let bid ← getExecutionPayloadBid state payload requests blobKzgCommitments state.slot
    feeRecipient BUILDER_INDEX_SELF_BUILD 0 inclusionListBits
  return ⟨bid, Signatures.infinitySignature⟩

/-- From Gloas: the envelope that reveals a payload and its requests, after the block of its bid.

It names the builder of the bid of the block, the root of the block and the parent of the block.

It fails when the root of the block fails. -/
def getExecutionPayloadEnvelope (block : BeaconBlock preset fork) (gloas : .glamsterdam ≤ fork)
    (payload : ExecutionPayload preset fork) (requests : ExecutionRequests preset fork) :
    Except Err (ExecutionPayloadEnvelope preset fork) := do
  let beaconBlockRoot ← SszType.hashTreeRoot block
  return {
    payload := payload
    executionRequests := requests
    builderIndex := (block.body.signedExecutionPayloadBid gloas).message.builderIndex
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
  let root ← (builderSigningRoot config state bid
    (some (computeEpochAtSlot preset bid.slot))).mapError .root
  (Signatures.sign key (packBytes root)).mapError .bls

/-- The signature of an envelope by a builder with a secret key. -/
def getExecutionPayloadEnvelopeSignature (config : Config) (state : BeaconState preset fork)
    (envelope : ExecutionPayloadEnvelope preset fork) (key : Signatures.SecretKey) :
    Except BuilderSigningError BLSSignature := do
  let root ← (builderSigningRoot config state envelope
    (some (computeEpochAtSlot preset state.slot))).mapError .root
  (Signatures.sign key (packBytes root)).mapError .bls

end EthLib.Consensus
