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

The [proposer's envelope endpoint] gives a proposer the envelope that its node built, to sign.

Each answer takes the blocks, headers, blobs, sidecars or envelope that it reads as inputs.

Which of them a node keeps, and how it finds them, is its own matter.

The flags `execution_optimistic` and `finalized` come from the store, not from the block.

SOUNDNESS.md records the points that the source leaves open.

[blocks endpoints]: https://github.com/ethereum/beacon-APIs/tree/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/blocks
[blobs endpoint]: https://github.com/ethereum/beacon-APIs/blob/09256e18f0a575e0aef546e06ec773a35fc52938/apis/beacon/blobs/blobs.yaml
[columns endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/debug/data_column_sidecars.yaml
[envelope endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/execution_payload/envelope_get.yaml
[proposer's envelope endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/execution_payload_envelope.yaml
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
  -- The source: the hash tree root of the unsigned block, not of the signed one.
  SszType.hashTreeRoot block.message

/-- The attestations of a signed block, in the order of its body. -/
def blockAttestations (block : SignedBeaconBlock preset fork) : Attestations preset fork :=
  -- The source: the attestations included in the block.
  block.message.body.attestations

/-- From Bellatrix to Fulu: the signed block with the header of its payload in place of the payload.
-/
def blindedBlock (block : SignedBeaconBlock preset fork) (range : HasBuilderApi fork) :
    Except Err (SignedBlindedBeaconBlock preset fork) := do
  -- The blinded message, under the signature of the block.
  return ⟨← block.message.blind range, block.signature⟩

/-- The response of the block endpoint, without the two flags that come from the store. -/
def blockResponse (block : SignedBeaconBlock preset fork) : Except ErrorMessage ApiEnvelope :=
  -- The source: the version of the fork of the block, and the signed block as data.
  versioned fork (.ok block)

/-- The response of the block root endpoint, without the two flags that come from the store. -/
def blockRootResponse (block : SignedBeaconBlock preset fork) :
    Except ErrorMessage ApiEnvelope := do
  -- A block whose root cannot be computed gives code 500.
  let root ← (blockRoot block).mapError fun _ => internalError "no block root"
  -- The source: the data is an object with the root, hex encoded with the 0x prefix.
  return { data := Json.mkObj [("root", .str (toHex ⟨root.toArray⟩))] }

/-- The response of the block attestations endpoint, without the two flags from the store. -/
def blockAttestationsResponse (block : SignedBeaconBlock preset fork) :
    Except ErrorMessage ApiEnvelope :=
  -- The source: the version of the fork of the block, and the array of its attestations as data.
  versioned fork (.ok (blockAttestations block))

/-- The blinded form of a signed block that the blinded block endpoint gives. -/
def blindedBlockResponse (block : SignedBeaconBlock preset fork) :
    Except ErrorMessage ApiEnvelope :=
  -- From Bellatrix to Fulu: the blinded block, with the version of the fork.
  if range : HasBuilderApi fork then do
    -- A block that cannot be blinded gives code 500.
    let blinded ← (blindedBlock block range).mapError fun _ => internalError "no blinded block"
    versioned fork (.ok blinded)
  -- Before Bellatrix: the block itself, as the Phase 0 and Altair schemas of the source say.
  else if fork < .bellatrix then versioned fork (.ok block)
  -- From Gloas: the source says that a block has no blinded form, and names no code for it.
  --
  -- EthLib's choice: code 400.
  else .error { code := 400, message := "Blocks from Gloas on do not have a blinded form" }

/-- The SSZ body of the block answer: the signed block. -/
def blockSsz (block : SignedBeaconBlock preset fork) : Except ErrorMessage ByteArray :=
  -- The SSZ bytes of the signed block; an encoding that fails gives code 500.
  apiSszOr500 block

/-- The SSZ body of the blinded block answer, for the forks where the JSON answer has one. -/
def blindedBlockSsz (block : SignedBeaconBlock preset fork) : Except ErrorMessage ByteArray :=
  -- From Bellatrix to Fulu: the SSZ bytes of the blinded block.
  if range : HasBuilderApi fork then do
    let blinded ← (blindedBlock block range).mapError fun _ => internalError "no blinded block"
    apiSszOr500 blinded
  -- Before Bellatrix: the SSZ bytes of the block itself.
  else if fork < .bellatrix then apiSszOr500 block
  -- From Gloas: code 400, as in JSON.
  else .error { code := 400, message := "Blocks from Gloas on do not have a blinded form" }

/-! ## Headers -/

/-- Whether a known block is on the chain of the head.

The source names the flag but does not define it, so EthLib reads canonical as on that chain. -/
def isCanonical (config : Config) (store : Store preset fork) (root : Root) : Bool :=
  match store.blocks[root]?, headRoot config store with
  -- The ancestor of the head at the slot of the block is the block itself.
  | some block, some head => blockAtSlot store head block.slot == some root
  -- A block that the store does not hold, or a store without a head, is not canonical.
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
  return Json.mkObj [("root", .str (toHex ⟨response.root.toArray⟩)),
    ("canonical", .bool response.canonical), ("header", ← apiJsonOr500 response.header)]

/-- The answer for one signed header: its root, and whether its block is canonical. -/
def headerOf (config : Config) (store : Store preset fork) (header : SignedBeaconBlockHeader) :
    Except ErrorMessage HeaderResponse := do
  -- The root of the header message, which is that of its block; code 500 if it cannot be computed.
  let root ← (SszType.hashTreeRoot header.message).mapError fun _ =>
    internalError "no header root"
  -- The source: the root, whether the block is canonical, and the signed header.
  return { root, canonical := isCanonical config store root, header }

/-- The response of the header endpoint for a signed block, without the two flags from the store.
-/
def headerResponse (config : Config) (store : Store preset fork)
    (block : SignedBeaconBlock preset fork) : Except ErrorMessage ApiEnvelope := do
  -- The header of the block under its signature; code 500 if it cannot be computed.
  let header ← block.signedHeader.mapError fun _ => internalError "no block header"
  -- The data is the one object of that header.
  return { data := ← (← headerOf config store header).toJson }

/-- The slot that the headers endpoint filters on, or none for no slot filter. -/
def headersSlot (config : Config) (store : Store preset fork) (slot : Option Slot)
    (parentRoot : Option Root) : Except ErrorMessage (Option Slot) :=
  match slot, parentRoot with
  -- A requested slot is kept.
  | some slot, _ => .ok (some slot)
  -- EthLib's choice: with only a parent root, there is no slot filter.
  --
  -- The default of the source reads as the request with no filter at all.
  | none, some _ => .ok none
  -- The source: by default, the blocks of the slot of the current head.
  | none, none =>
    match (headRoot config store).bind fun head => store.blocks[head]? with
    | some block => .ok (some block.slot)
    -- A store without a head gives code 500.
    | none => .error (internalError "the store has no head")

/-- The signed headers that match the slot and the parent root, in the order of the input. -/
def selectHeaders (headers : List SignedBeaconBlockHeader) (slot : Option Slot)
    (parentRoot : Option Root) : List SignedBeaconBlockHeader :=
  -- A header matches when its slot and its parent root equal the filters that are present.
  headers.filter fun header =>
    slot.all (· == header.message.slot) && parentRoot.all (· == header.message.parentRoot)

/-- The answers of the headers endpoint, from the signed headers of the blocks that the node holds.

The input is the signed headers of the blocks that the node holds, of any fork. -/
def headersOf (config : Config) (store : Store preset fork)
    (headers : List SignedBeaconBlockHeader) (slot : Option Slot) (parentRoot : Option Root) :
    Except ErrorMessage (List HeaderResponse) := do
  -- The slot filter, with the default of the source.
  let slot ← headersSlot config store slot parentRoot
  -- The answer for each header that matches the filters.
  (selectHeaders headers slot parentRoot).mapM (headerOf config store)

/-- The response of the headers endpoint, without the two flags that come from the store. -/
def headersResponse (config : Config) (store : Store preset fork)
    (headers : List SignedBeaconBlockHeader) (slot : Option Slot) (parentRoot : Option Root) :
    Except ErrorMessage ApiEnvelope := do
  let answers ← headersOf config store headers slot parentRoot
  -- The source: the data is the array of the objects of the matching headers.
  return { data := .arr (← answers.mapM (·.toJson)).toArray }

/-! ## Blobs -/

/-- The blob commitments of a block, in the order of the block. -/
def blockCommitments (block : BeaconBlock preset fork) : List KZGCommitment :=
  -- From Gloas: the commitments of the bid that the block carries.
  if gloas : .glamsterdam ≤ fork then (block.bidCommitments gloas).data.toList
  -- From Deneb to Fulu: the commitments of the body.
  else if deneb : .dencun ≤ fork then
    (block.body.blobKzgCommitments ⟨deneb, Nat.lt_of_not_le gloas⟩).data.toList
  -- Before Deneb a block has none.
  else []

/-- The blobs of a block, each with the versioned hash of the commitment at its place. -/
def blobHashes (blobs : List Blob) (commitments : List KZGCommitment) :
    List (Blob × VersionedHash) :=
  -- The blobs pair with the commitments in order.
  (blobs.zip commitments).map fun (blob, commitment) =>
    (blob, kzgCommitmentToVersionedHash commitment)

/-- The blobs of a block that a list of versioned hashes asks for, each with its hash. -/
def requestedBlobs (requested : List VersionedHash) (blobs : List Blob)
    (commitments : List KZGCommitment) : List (Blob × VersionedHash) :=
  -- The source: only the blobs whose commitment has one of the requested hashes.
  --
  -- One blob for each such hash, also when the block repeats its commitment.
  --
  -- The blob kept is the first, in the order of the block.
  ((blobHashes blobs commitments).filter fun (_, hash) => requested.contains hash).eraseDupsBy
    fun a b => a.2 == b.2

/-- The blobs of a block, in the order of their commitments. -/
def blockBlobs (blobs : List Blob) (commitments : List KZGCommitment) :
    Option (List VersionedHash) → List Blob
  -- Without versioned hashes, every blob of the block.
  | none => (blobs.zip commitments).map (·.1)
  | some requested => (requestedBlobs requested blobs commitments).map (·.1)

/-- The blobs of a signed block that the blobs endpoint gives, from the blobs of its commitments.

The input holds one blob for each commitment of the block, in order. -/
def blobsOf (block : SignedBeaconBlock preset fork) (blobs : List Blob)
    (hashes : Option (List VersionedHash)) : Except ErrorMessage (List Blob) :=
  let commitments := blockCommitments block.message
  -- The source: the kept blobs, in the order of their commitments in the block.
  if blobs.length = commitments.length then .ok (blockBlobs blobs commitments hashes)
  -- Another count of blobs gives code 500.
  else .error (internalError "the blobs do not match the commitments of the block")

/-- The response of the blobs endpoint, without the two flags that come from the store. -/
def blobsResponse (block : SignedBeaconBlock preset fork) (blobs : List Blob)
    (hashes : Option (List VersionedHash)) : Except ErrorMessage ApiEnvelope := do
  let kept ← blobsOf block blobs hashes
  -- The data is the array of the kept blobs, each hex encoded with the 0x prefix.
  return { data := .arr (kept.map fun blob => Json.str (toHex ⟨blob.toArray⟩)).toArray }

/-- The SSZ body of the blobs answer: a list bounded by the commitments that a block may hold. -/
def blobsSsz (block : SignedBeaconBlock preset fork) (blobs : List Blob)
    (hashes : Option (List VersionedHash)) : Except ErrorMessage ByteArray := do
  let kept := (← blobsOf block blobs hashes).toArray
  -- The source: the SSZ bytes of `List[Blob, MAX_BLOB_COMMITMENTS_PER_BLOCK]`.
  if bound : kept.size ≤ preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat then
    apiSszOr500 (SszList.mk kept bound)
  -- More blobs than that bound gives code 500.
  else .error (internalError "more blobs than a block may commit to")

/-! ## Data column sidecars -/

/-- The sidecars with a requested index, in the order of the input; every one without a list. -/
def selectColumns (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex)) : List (DataColumnSidecar preset fork) :=
  -- The source: with indices, only the sidecars of those indices that the node custodies.
  --
  -- Without them, every sidecar of the block that the node custodies.
  --
  -- The input holds the sidecars that the node custodies, so the filter reads only the indices.
  sidecars.filter fun sidecar => indices.all (·.contains sidecar.index)

/-- Whether a list of sidecars is valid data for the answer: the requested sidecars, in any order.

It describes the data of the answer from Fulu on; before Fulu the answer is an error. -/
def IsColumnsAnswer (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex))
    (answer : List (DataColumnSidecar preset fork)) : Prop :=
  -- The source gives no guarantee on the order of the sidecars: any permutation of them.
  answer.Perm (selectColumns sidecars indices)

/-- The error of a block before Fulu, which has no data column sidecars, with code 400. -/
def columnsBeforeFulu : ErrorMessage :=
  -- The source has the versions fulu and gloas only, and names no error for an earlier block.
  --
  -- EthLib's choice: code 400, with its own message.
  { code := 400, message := "Blocks before Fulu do not have data column sidecars" }

/-- From Fulu: the response of the columns endpoint, without the two flags from the store. -/
def columnsResponse (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex)) : Except ErrorMessage ApiEnvelope :=
  if .fusaka ≤ fork then do
    -- A sidecar without JSON gives code 500.
    let kept ← (selectColumns sidecars indices).mapM apiJsonOr500
    -- The source: the consensus version of the fork, and the array of the sidecars as data.
    return { version := fork.consensusVersion?, data := .arr kept.toArray }
  -- Before Fulu: code 400.
  else .error columnsBeforeFulu

/-- From Fulu: the SSZ body of the columns answer, a list bounded by the number of columns. -/
def columnsSsz (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex)) : Except ErrorMessage ByteArray :=
  let kept := (selectColumns sidecars indices).toArray
  -- Before Fulu: code 400, as in JSON.
  if ¬ .fusaka ≤ fork then .error columnsBeforeFulu
  -- The source: the SSZ bytes of `List[DataColumnSidecar, NUMBER_OF_COLUMNS]`.
  else if bound : kept.size ≤ preset.NUMBER_OF_COLUMNS.toNat then
    apiSszOr500 (SszList.mk kept bound)
  -- More sidecars than columns gives code 500.
  else .error (internalError "more sidecars than columns")

/-! ## Payload envelopes -/

/-- The error of a block whose payload envelope the node does not hold, with code 404. -/
def envelopeNotFound : ErrorMessage :=
  -- The example message of the envelope endpoint.
  { code := 404, message := "Execution payload envelope not found" }

/-- From Gloas: the signed envelope of a block, when the store holds its message.

The store keeps envelopes without their signatures, so the signed envelope is an input.

Its signature is not checked; the caller vouches for it. -/
def payloadEnvelopeOf (store : Store preset fork) (root : Root)
    (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except ErrorMessage (SignedExecutionPayloadEnvelope preset fork) :=
  if gloas : .glamsterdam ≤ fork then
    -- The envelope that the store holds for the block.
    match (store.payloads gloas)[root]? with
    | some stored =>
      -- The given message must have the root of that envelope, else code 404.
      match SszType.hashTreeRoot signed.message, SszType.hashTreeRoot stored with
      | .ok given, .ok held => if given = held then .ok signed else .error envelopeNotFound
      -- A message without a hash tree root gives code 500.
      | _, _ => .error (internalError "the envelope has no root")
    -- A block with no envelope in the store: code 404.
    | none => .error envelopeNotFound
  -- Before Gloas no envelope exists: code 404.
  else .error envelopeNotFound

/-- The response of the envelope endpoint, without the two flags that come from the store. -/
def payloadEnvelopeResponse (store : Store preset fork) (root : Root)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Except ErrorMessage ApiEnvelope :=
  -- The source: the version of the fork, and the signed envelope as data.
  versioned fork (payloadEnvelopeOf store root signed)

/-- The SSZ body of the envelope answer: the signed envelope. -/
def payloadEnvelopeSsz (store : Store preset fork) (root : Root)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Except ErrorMessage ByteArray :=
  -- The source: the SSZ bytes of the signed envelope.
  payloadEnvelopeOf store root signed >>= apiSszOr500

/-! ## The envelope that a node built for its proposer -/

/-- From Gloas: the envelope that a node built for the payload of a slot, with that slot.

The envelope names its block by root, but not its slot, so the entry keeps the slot. -/
structure CachedEnvelope (preset : Preset) (fork : Fork) where
  /-- The slot of the payload. -/
  slot : Slot
  /-- The unsigned envelope of the payload. -/
  envelope : ExecutionPayloadEnvelope preset fork

/-- From Gloas: the envelope that a proposer fetches to sign, at a slot and for a block root.

The cache is an input: the caller vouches that it is the one envelope built for the current slot.

The [source] says that the node keeps only that one.

[source]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/execution_payload_envelope.yaml#L1-L77
-/
def cachedEnvelopeOf (cache : Option (CachedEnvelope preset fork)) (slot : Slot) (root : Root) :
    Except ErrorMessage (ExecutionPayloadEnvelope preset fork) :=
  if .glamsterdam ≤ fork then
    match cache with
    | some cached =>
      -- The source: the cached envelope, when it is for the requested slot and block root.
      --
      -- So the answer always names the requested block, and a reorg before the request gives 404.
      if cached.slot = slot ∧ cached.envelope.beaconBlockRoot = root then .ok cached.envelope
      -- The source: no match gives code 404.
      --
      -- EthLib reuses the message of the envelope endpoint, not the example of this one.
      else .error envelopeNotFound
    -- The source: a slot with no cached envelope gives code 404.
    | none => .error envelopeNotFound
  -- Before Gloas no envelope exists: code 404 too.
  else .error envelopeNotFound

/-- The JSON response of the endpoint that gives a proposer its envelope, with the version. -/
def cachedEnvelopeResponse (cache : Option (CachedEnvelope preset fork)) (slot : Slot)
    (root : Root) : Except ErrorMessage ApiEnvelope :=
  -- The source: the version of the fork, and the unsigned envelope as data.
  versioned fork (cachedEnvelopeOf cache slot root)

/-- The SSZ body of the endpoint that gives a proposer its envelope: the unsigned envelope. -/
def cachedEnvelopeSsz (cache : Option (CachedEnvelope preset fork)) (slot : Slot) (root : Root) :
    Except ErrorMessage ByteArray :=
  -- The source: the SSZ bytes of the unsigned envelope.
  cachedEnvelopeOf cache slot root >>= apiSszOr500

end EthLib.Consensus.BeaconApi
