module

public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Transition.Execution

/-!
# `Consensus.BeaconApi.Blocks`

The answers of the Beacon API that read one signed block and the blobs of its commitments.

The [blocks endpoints] give the block, its root, its attestations and its blinded form.

The [blobs endpoint] gives the blobs of a block, in the order of its commitments.

Each answer takes the block, and the blobs, as inputs.

Which blocks and blobs a node keeps, and how it finds them, is its own matter.

The flags `execution_optimistic` and `finalized` come from the store, not from the block.

SOUNDNESS.md records the points that the source leaves open.

[blocks endpoints]: https://github.com/ethereum/beacon-APIs/tree/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/blocks
[blobs endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/blobs/blobs.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz Cryptography.Kzg

variable {preset : Preset} {fork : Fork}

/-! ## Blocks -/

instance : ApiSpelling (Attestations preset fork) := .unmarked

/-- The root of a signed block: the hash tree root of its message.

It is also the root of the header of the block. -/
def blockRoot (block : SignedBeaconBlock preset fork) : Except Err Root :=
  SszType.hashTreeRoot block.message

/-- The attestations of a signed block, in the order of its body. -/
def blockAttestations (block : SignedBeaconBlock preset fork) : Attestations preset fork :=
  block.message.body.attestations

/-- From Bellatrix to Fulu: the signed block with the header of its payload in place of the payload.

The signature is that of the block. -/
def blindedBlock (block : SignedBeaconBlock preset fork) (range : HasBuilderApi fork) :
    Except Err (SignedBlindedBeaconBlock preset fork) := do
  return ⟨← block.message.blind range, block.signature⟩

/-- The response of the block endpoint, without the two flags that come from the store. -/
def blockResponse (block : SignedBeaconBlock preset fork) : Except ErrorMessage ApiEnvelope :=
  versioned fork (.ok block)

/-- The response of the block root endpoint, without the two flags that come from the store. -/
def blockRootResponse (block : SignedBeaconBlock preset fork) :
    Except ErrorMessage ApiEnvelope := do
  let root ← (blockRoot block).mapError fun fault => internalError (reprStr fault)
  return { data := Json.mkObj [("root", .str (toHex root.toArray))] }

/-- The response of the block attestations endpoint, without the two flags from the store. -/
def blockAttestationsResponse (block : SignedBeaconBlock preset fork) :
    Except ErrorMessage ApiEnvelope :=
  versioned fork (.ok (blockAttestations block))

/-- The blinded form of a signed block that the blinded block endpoint gives.

Before Bellatrix it is the block itself, and to Fulu the blinded block.

From Gloas a block has no blinded form, and the answer is the error with code 400. -/
def blindedBlockResponse (block : SignedBeaconBlock preset fork) :
    Except ErrorMessage ApiEnvelope :=
  if range : HasBuilderApi fork then do
    let blinded ← (blindedBlock block range).mapError fun fault => internalError (reprStr fault)
    versioned fork (.ok blinded)
  else if fork < .bellatrix then versioned fork (.ok block)
  else .error { code := 400, message := "Blocks from Gloas on do not have a blinded form" }

/-! ## Blobs -/

/-- The blob commitments of a block, in the order of the block.

Before Deneb there are none, to Fulu they are in the body, and from Gloas in the bid. -/
def blockCommitments (block : BeaconBlock preset fork) : List KZGCommitment :=
  if gloas : .glamsterdam ≤ fork then (block.bidCommitments gloas).data.toList
  else if deneb : .dencun ≤ fork then
    (block.body.blobKzgCommitments ⟨deneb, Nat.lt_of_not_le gloas⟩).data.toList
  else []

/-- The blobs of a block, in the order of their commitments.

The blobs pair with the commitments in order.

Each blob is kept when no hashes are given, or when they hold the versioned hash of its commitment.
-/
def blockBlobs (blobs : List Blob) (commitments : List KZGCommitment)
    (hashes : Option (List VersionedHash)) : List Blob :=
  ((blobs.zip commitments).filter fun (_, commitment) =>
    hashes.all (·.contains (kzgCommitmentToVersionedHash commitment))).map (·.1)

/-- The blobs of a signed block that the blobs endpoint gives, from the blobs of its commitments.

The input holds one blob for each commitment of the block, in order.

Another count of blobs gives the error with code 500. -/
def blobsOf (block : SignedBeaconBlock preset fork) (blobs : List Blob)
    (hashes : Option (List VersionedHash)) : Except ErrorMessage (List Blob) :=
  let commitments := blockCommitments block.message
  if blobs.length = commitments.length then .ok (blockBlobs blobs commitments hashes)
  else .error (internalError "the blobs do not match the commitments of the block")

/-- The response of the blobs endpoint, without the two flags that come from the store.

Each blob is written as hex. -/
def blobsResponse (block : SignedBeaconBlock preset fork) (blobs : List Blob)
    (hashes : Option (List VersionedHash)) : Except ErrorMessage ApiEnvelope := do
  let kept ← blobsOf block blobs hashes
  return { data := .arr (kept.map fun blob => Json.str (toHex blob.toArray)).toArray }

/-- The SSZ body of the blobs answer: a list bounded by the commitments that a block may hold. -/
def blobsSsz (block : SignedBeaconBlock preset fork) (blobs : List Blob)
    (hashes : Option (List VersionedHash)) : Except ErrorMessage ByteArray := do
  let kept := (← blobsOf block blobs hashes).toArray
  if bound : kept.size ≤ preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat then
    apiSszOr500 (SszList.mk kept bound)
  else .error (internalError "more blobs than a block may commit to")

end EthLib.Consensus.BeaconApi
