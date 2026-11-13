module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Transition.Execution

/-!
# `Consensus.BeaconApi.Blocks`

The answers of the Beacon API that read signed blocks, and the data that a node keeps with them.

The [blocks endpoints] give the block, its root, its attestations, its header and its blinded form.

The [blobs endpoint] gives the blobs of a block, in the order of its commitments.

The [columns endpoint] gives the data column sidecars of a block, in any order.

The [envelope endpoint] gives the signed payload envelope of a block, from Gloas.

Each answer takes the blocks, headers, blobs, sidecars or envelope that it reads as inputs.

Which of them a node keeps, and how it finds them, is its own matter.

The flags `execution_optimistic` and `finalized` come from the store, not from the block.

SOUNDNESS.md records the points that the source leaves open.

[blocks endpoints]: https://github.com/ethereum/beacon-APIs/tree/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/blocks
[blobs endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/blobs/blobs.yaml
[columns endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/debug/data_column_sidecars.yaml
[envelope endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/execution_payload/envelope_get.yaml
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

/-- The SSZ body of the block answer: the signed block. -/
def blockSsz (block : SignedBeaconBlock preset fork) : Except ErrorMessage ByteArray :=
  apiSszOr500 block

/-- The SSZ body of the blinded block answer, for the forks where the JSON answer has one.

From Gloas the answer is the error with code 400, as in JSON. -/
def blindedBlockSsz (block : SignedBeaconBlock preset fork) : Except ErrorMessage ByteArray :=
  if range : HasBuilderApi fork then do
    let blinded ← (blindedBlock block range).mapError fun fault => internalError (reprStr fault)
    apiSszOr500 blinded
  else if fork < .bellatrix then apiSszOr500 block
  else .error { code := 400, message := "Blocks from Gloas on do not have a blinded form" }

/-! ## Headers -/

/-- Whether a known block is on the chain of the head.

The ancestor of the head at the slot of the block must be the block itself.

A block that the store does not hold, or a store without a head, gives false. -/
def isCanonical (config : Config) (store : Store preset fork) (root : Root) : Bool :=
  match store.blocks[root]?, headRoot config store with
  | some block, some head => blockAtSlot store head block.slot == some root
  | _, _ => false

/-- One entry of the headers answers: a root, whether its block is canonical, and its header. -/
structure HeaderResponse where
  /-- The root of the block, which is the root of its header. -/
  root : Root
  /-- Whether the block is on the chain of the head. -/
  canonical : Bool
  /-- The header of the block, with the signature of the block. -/
  header : SignedBeaconBlockHeader
  deriving DecidableEq, Repr

/-- The JSON object of one header answer. -/
def HeaderResponse.toJson (response : HeaderResponse) : Except ErrorMessage Json := do
  return Json.mkObj [("root", .str (toHex response.root.toArray)),
    ("canonical", .bool response.canonical), ("header", ← apiJsonOr500 response.header)]

/-- The answer for one signed header: its root, and whether its block is canonical. -/
def headerOf (config : Config) (store : Store preset fork) (header : SignedBeaconBlockHeader) :
    Except ErrorMessage HeaderResponse := do
  let root ← (SszType.hashTreeRoot header.message).mapError fun fault =>
    internalError (reprStr fault)
  return { root, canonical := isCanonical config store root, header }

/-- The response of the header endpoint for a signed block, without the two flags from the store.
-/
def headerResponse (config : Config) (store : Store preset fork)
    (block : SignedBeaconBlock preset fork) : Except ErrorMessage ApiEnvelope := do
  let header ← block.signedHeader.mapError fun fault => internalError (reprStr fault)
  return { data := ← (← headerOf config store header).toJson }

/-- The slot that the headers endpoint filters on.

A requested slot is kept.

With neither a slot nor a parent root, it is the slot of the head.

With only a parent root, there is no slot filter.

A store without a head gives the error with code 500 when the slot of the head is needed. -/
def headersSlot (config : Config) (store : Store preset fork) (slot : Option Slot)
    (parentRoot : Option Root) : Except ErrorMessage (Option Slot) :=
  match slot, parentRoot with
  | some slot, _ => .ok (some slot)
  | none, some _ => .ok none
  | none, none =>
    match (headRoot config store).bind fun head => store.blocks[head]? with
    | some block => .ok (some block.slot)
    | none => .error (internalError "the store has no head")

/-- The signed headers that match the slot and the parent root, in the order of the input. -/
def selectHeaders (headers : List SignedBeaconBlockHeader) (slot : Option Slot)
    (parentRoot : Option Root) : List SignedBeaconBlockHeader :=
  headers.filter fun header =>
    slot.all (· == header.message.slot) && parentRoot.all (· == header.message.parentRoot)

/-- The answers of the headers endpoint, from the signed headers of the blocks that the node holds.

The input is the signed headers of the blocks that the node holds, of any fork. -/
def headersOf (config : Config) (store : Store preset fork)
    (headers : List SignedBeaconBlockHeader) (slot : Option Slot) (parentRoot : Option Root) :
    Except ErrorMessage (List HeaderResponse) := do
  let slot ← headersSlot config store slot parentRoot
  (selectHeaders headers slot parentRoot).mapM (headerOf config store)

/-- The response of the headers endpoint, without the two flags that come from the store. -/
def headersResponse (config : Config) (store : Store preset fork)
    (headers : List SignedBeaconBlockHeader) (slot : Option Slot) (parentRoot : Option Root) :
    Except ErrorMessage ApiEnvelope := do
  let answers ← headersOf config store headers slot parentRoot
  return { data := .arr (← answers.mapM (·.toJson)).toArray }

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

/-! ## Data column sidecars -/

/-- The sidecars with a requested index, in the order of the input; every one without a list. -/
def selectColumns (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex)) : List (DataColumnSidecar preset fork) :=
  sidecars.filter fun sidecar => indices.all (·.contains sidecar.index)

/-- Whether a list of sidecars is valid data for the answer: the requested sidecars, in any order.

It describes the data of the answer from Fulu on; before Fulu the answer is an error.

The source gives no guarantee on the order of the sidecars. -/
def IsColumnsAnswer (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex))
    (answer : List (DataColumnSidecar preset fork)) : Prop :=
  answer.Perm (selectColumns sidecars indices)

/-- The error of a block before Fulu, which has no data column sidecars, with code 400. -/
def columnsBeforeFulu : ErrorMessage :=
  { code := 400, message := "Blocks before Fulu do not have data column sidecars" }

/-- From Fulu: the response of the columns endpoint, without the two flags from the store.

It names the consensus version of the fork.

Before Fulu, the answer is the error with code 400. -/
def columnsResponse (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex)) : Except ErrorMessage ApiEnvelope :=
  if .fusaka ≤ fork then do
    let kept ← (selectColumns sidecars indices).mapM apiJsonOr500
    return { version := fork.consensusVersion?, data := .arr kept.toArray }
  else .error columnsBeforeFulu

/-- From Fulu: the SSZ body of the columns answer, a list bounded by the number of columns.

Before Fulu, the answer is the error with code 400. -/
def columnsSsz (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex)) : Except ErrorMessage ByteArray :=
  let kept := (selectColumns sidecars indices).toArray
  if ¬ .fusaka ≤ fork then .error columnsBeforeFulu
  else if bound : kept.size ≤ preset.NUMBER_OF_COLUMNS.toNat then
    apiSszOr500 (SszList.mk kept bound)
  else .error (internalError "more sidecars than columns")

/-! ## Payload envelopes -/

/-- The error of a block whose payload envelope the node does not hold, with code 404. -/
def envelopeNotFound : ErrorMessage :=
  { code := 404, message := "Execution payload envelope not found" }

/-- From Gloas: the signed envelope of a block, when the store holds its message.

The store keeps envelopes without their signatures, so the signed envelope is an input.

Its signature is not checked; the caller vouches for it.

Its message must have the root of the envelope that the store holds for the block.

Otherwise, and before Gloas, the answer is the error with code 404.

A message without a hash tree root gives the error with code 500. -/
def payloadEnvelopeOf (store : Store preset fork) (root : Root)
    (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except ErrorMessage (SignedExecutionPayloadEnvelope preset fork) :=
  if gloas : .glamsterdam ≤ fork then
    match (store.payloads gloas)[root]? with
    | some stored =>
      match SszType.hashTreeRoot signed.message, SszType.hashTreeRoot stored with
      | .ok given, .ok held => if given = held then .ok signed else .error envelopeNotFound
      | _, _ => .error (internalError "the envelope has no root")
    | none => .error envelopeNotFound
  else .error envelopeNotFound

/-- The response of the envelope endpoint, without the two flags that come from the store. -/
def payloadEnvelopeResponse (store : Store preset fork) (root : Root)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Except ErrorMessage ApiEnvelope :=
  versioned fork (payloadEnvelopeOf store root signed)

/-- The SSZ body of the envelope answer: the signed envelope. -/
def payloadEnvelopeSsz (store : Store preset fork) (root : Root)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Except ErrorMessage ByteArray :=
  payloadEnvelopeOf store root signed >>= apiSszOr500

end EthLib.Consensus.BeaconApi
