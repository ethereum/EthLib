module

public import EthLib.Engine.BuildPayload
public import EthLib.Engine.NewPayload
public import EthLib.Execution.Transactions.Network

/-!
# `Engine.GetPayload`

The latest completed payload of a build process, read by its eight-byte ID.

The store is a snapshot of completed builds.

The method neither waits for more building nor changes the store.

Each build is what the payload build gives: the block, the state after it, requests and value.

The chain configuration determines the fork at the block's number and timestamp.

Version 1 serves Paris, and version 2 serves Paris and Shapella.

Version 3 serves Dencun, version 4 Pectra, version 5 Fusaka to BPO5, and version 6 Glamsterdam.

The source does not say what version 1 returns for a payload after Paris.

EthLib rejects it as an unsupported fork, as `engine_newPayloadV1` does.

From version 3, the bundle's commitments must hash to the block's blob hashes, in order.

Its proofs are checked, with one per blob before Fusaka and 128 cell proofs per blob from it.

The consensus layer also writes the parameters as JSON: the payload ID alone.

It also reads the result of a version as JSON, at the fork of the payload, and writes it back.

The method follows [version 1][v1], [2][v2], [3][v3], [4][v4], [5][v5] and [6][v6].

The upper bounds of versions 2 to 5 come from the updates of later forks.

They are in [Cancun][c], [Prague][p], [Osaka][o] and [Amsterdam][a].

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_getpayloadv1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_getpayloadv3
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#engine_getpayloadv4
[v5]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/osaka.md#engine_getpayloadv5
[v6]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getpayloadv6
[c]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#update-the-methods-of-previous-forks
[p]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#update-the-methods-of-previous-forks
[o]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/osaka.md#update-the-methods-of-previous-forks
[a]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#update-the-methods-of-previous-forks
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Execution.Blocks (Block)
open EthLib.Execution.Transactions
open EthLib.Serialization.JsonRpc (dataJson fixed paramsArray fields hasExactly field array bytes
  quantity quantityJson listJson)

/-- The blobs, commitments and proofs of the payload's network blob transactions, in order. -/
structure BlobsBundle where
  /-- One blob per versioned hash. -/
  blobs : List Blob
  /-- One commitment per blob. -/
  commitments : List KZGCommitment
  /-- One proof per blob, or per cell from Fusaka. -/
  proofs : List KZGProof

/-- Join the sidecars of the network transactions in payload order. -/
def BlobsBundle.ofNetwork (transactions : List NetworkBlobTransaction) : BlobsBundle :=
  ⟨transactions.flatMap (·.blobs), transactions.flatMap (·.commitments),
    transactions.flatMap (·.proofs)⟩

/-- A completed build, with the fields that the method returns beside its payload. -/
structure StoredPayload where
  /-- The fork at which the payload was built. -/
  fork : Fork
  /-- The block of the build, with its requests and its value. -/
  built : BuiltPayload fork
  /-- The blobs of the network forms of the block's blob transactions. -/
  bundle : BlobsBundle
  /-- Whether the builder recommends its payload over an external builder's. -/
  shouldOverrideBuilder : Bool
  /-- The block access list from Glamsterdam, whose hash the header holds. -/
  blockAccessList : Since .glamsterdam fork ByteArray

/-- A snapshot of build processes, each identified by its payload ID. -/
abbrev PayloadStore := PayloadId → Option StoredPayload

/-- What the method returns: the stored build and the execution payload of its block. -/
structure GetPayloadResponse where
  /-- The stored build. -/
  stored : StoredPayload
  /-- The execution payload of its block. -/
  payload : ExecutionPayload stored.fork

/-- A request error, or malformed data in the supplied snapshot of completed builds. -/
inductive GetPayloadError where
  /-- A request with no build, or for a fork that its version does not support. -/
  | engine (error : EngineError)
  /-- The stored fork is not the fork of the configuration at the block. -/
  | wrongFork
  /-- The stored execution requests are out of order, have no data, or precede Pectra. -/
  | requests
  /-- The stored block value does not fit in 256 bits. -/
  | blockValue
  /-- The block has no payload form: a field does not fit, has no encoding, or is too long.

  The extra data, at most 32 bytes in the Engine API, is the field that can be too long. -/
  | noPayload
  /-- A transaction does not decode, or the payload does not give the stored block hash. -/
  | header (error : PayloadError)
  /-- The stored bundle fails a count, hash or KZG check. -/
  | bundle (error : NetworkError)

/-- The forks whose payloads a version of the method returns. -/
def acceptsGetPayloadFork (version : Nat) (fork : Fork) : Bool :=
  match version with
  | 1 => fork == .paris
  | 2 => fork == .paris || fork == .shapella
  | 3 => fork == .dencun
  | 4 => fork == .pectra
  | 5 => decide (.fusaka ≤ fork) && decide (fork < .glamsterdam)
  | 6 => fork == .glamsterdam
  | _ => false

/-- Whether requests have the shape of their fork: none before Pectra, valid lists from it. -/
def requestsOfFork (fork : Fork) (requests : List ByteArray) : Bool :=
  if .pectra ≤ fork then validRequests requests else requests.isEmpty

/-- The payload form of a block, which exists only from Paris.

Its extra data must hold at most 32 bytes, the bound of [its type][p] in the Engine API.

[p]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#executionpayloadv1 -/
def payloadOfBlock {fork : Fork} (block : Block fork Transaction) :
    Option (ExecutionPayload fork) :=
  if h : .paris ≤ fork then
    (ExecutionPayload.ofBlock h block).filter (·.extraData.size ≤ 32)
  else none

/-- The block that a payload gives back, with the stored requests and access list.

The parent beacon block root and the slot are those of the stored header. -/
def StoredPayload.blockOfPayload (stored : StoredPayload)
    (payload : ExecutionPayload stored.fork) :
    Except PayloadError (Block stored.fork Transaction) :=
  let header := stored.built.block.header
  payload.toBlock header.parentBeaconBlockRoot (fun _ => stored.built.requests)
    stored.blockAccessList header.slotNumber

/-- Read the latest build of an ID, checking its fork and, from version 3, its bundle.

The snapshot supplies the output of the build, including the requests and the block value.

This method checks their shape against the fork, and does not execute the block again.

The payload must give back a block with the stored block hash, as `engine_newPayload` checks.

So that hash commits to the transactions, the requests and the access list it returns. -/
def getPayload (config : ChainConfig) (setup : TrustedSetup) (store : PayloadStore)
    (version : Nat) (id : PayloadId) : Except GetPayloadError GetPayloadResponse := do
  let some stored := store id | throw (.engine .unknownPayload)
  let block := stored.built.block
  unless config.activeFork block.header.number block.header.timestamp.toNat = some stored.fork do
    throw .wrongFork
  unless acceptsGetPayloadFork version stored.fork do throw (.engine .unsupportedFork)
  unless requestsOfFork stored.fork stored.built.requests do throw .requests
  unless stored.built.blockValue < 2 ^ 256 do throw .blockValue
  let some payload := payloadOfBlock block | throw .noPayload
  if let .error e := stored.blockOfPayload payload then throw (.header e)
  if 3 ≤ version then
    (validateBlobs setup stored.fork (ExecutionPayload.blobVersionedHashes block.transactions)
      stored.bundle.blobs stored.bundle.commitments stored.bundle.proofs).mapError .bundle
  return ⟨stored, payload⟩

/-- The single eight-byte payload ID of the request. -/
def getPayloadParams (params : Lean.Json) : Json.Decode PayloadId := do
  match ← paramsArray params with
  | [id] => fixed "payloadId" 8 id
  | values => Json.invalid s!"params: got {values.length}, expected 1"

/-- The parameters of the request as JSON: the payload ID alone. -/
def getPayloadParamsJson (id : PayloadId) : Lean.Json := .arr #[dataJson id.toList]

/-! ## The result -/

/-- The version of the bundle, 1 or 2, that a version of the method returns: 2 from version 5. -/
def blobsBundleVersion (version : Nat) : Nat := if 5 ≤ version then 2 else 1

/-- The proofs per blob in a bundle of a version, 1 or 2: one, or one per cell in version 2. -/
def BlobsBundle.proofsPerBlob (version : Nat) : Nat :=
  if version < 2 then 1 else Constants.CELLS_PER_EXT_BLOB

/-- The length rules of a bundle of a version, 1 or 2: one commitment and its proofs per blob.

[BlobsBundleV1][v1] asks for three arrays of one length.

[BlobsBundleV2][v2] asks for as many commitments as blobs, and `CELLS_PER_EXT_BLOB` proofs per blob.

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#blobsbundlev1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/osaka.md#blobsbundlev2 -/
def BlobsBundle.lengthsHold (version : Nat) (b : BlobsBundle) : Bool :=
  b.commitments.length == b.blobs.length &&
    b.proofs.length == BlobsBundle.proofsPerBlob version * b.blobs.length

/-- A blobs bundle as JSON: its blobs, commitments and proofs, in order. -/
def blobsBundleJson (b : BlobsBundle) : Lean.Json :=
  Lean.Json.mkObj [("blobs", listJson (dataJson ·.toList) b.blobs),
    ("commitments", listJson (dataJson ·.toList) b.commitments),
    ("proofs", listJson (dataJson ·.toList) b.proofs)]

/-- The three fields of a blobs bundle. -/
def blobsBundleFields : List String := ["blobs", "commitments", "proofs"]

/-- A blobs bundle of a version, 1 or 2, which must pass the length rules of that version.

A blob has 131072 bytes, and a commitment and a proof 48 bytes each. -/
def blobsBundleOfJson (version : Nat) (j : Lean.Json) : Json.Decode BlobsBundle := do
  let fs ← fields "blobsBundle" j
  unless hasExactly fs blobsBundleFields do Json.invalid "blobsBundle: not the fields of a bundle"
  let get := field "blobsBundle" fs
  let bundle : BlobsBundle := {
    blobs := ← array "blobs" (fixed "blob" _) (← get "blobs")
    commitments := ← array "commitments" (fixed "commitment" 48) (← get "commitments")
    proofs := ← array "proofs" (fixed "proof" 48) (← get "proofs") }
  unless bundle.lengthsHold version do Json.invalid "blobsBundle: lengths do not match"
  return bundle

/-- What a consensus node reads from the result of the method, at the fork of the payload.

The access list and the slot are those of a payload from Glamsterdam.

The block value is present from version 2, the bundle and the override flag from version 3.

The execution requests are present from version 4.

The writer writes the options that are present, so they must follow the version. -/
structure GetPayloadResult (fork : Fork) where
  /-- The execution payload. -/
  payload : ExecutionPayload fork
  /-- The block access list, from Glamsterdam. -/
  blockAccessList : Since .glamsterdam fork ByteArray
  /-- The slot number, from Glamsterdam. -/
  slotNumber : Since .glamsterdam fork UInt64
  /-- The value of the block to its proposer, in wei. -/
  blockValue : Option Nat
  /-- The blobs, commitments and proofs of the blob transactions of the payload. -/
  blobsBundle : Option BlobsBundle
  /-- Whether the execution layer suggests its own payload over one of an external builder. -/
  shouldOverrideBuilder : Option Bool
  /-- The execution requests of the payload. -/
  executionRequests : Option (List ByteArray)

/-- What a response holds at a version of the method: the fields of that version. -/
def GetPayloadResponse.result (version : Nat) (r : GetPayloadResponse) :
    GetPayloadResult r.stored.fork where
  payload := r.payload
  blockAccessList := r.stored.blockAccessList
  slotNumber := r.stored.built.block.header.slotNumber
  blockValue := if 2 ≤ version then some r.stored.built.blockValue else none
  blobsBundle := if 3 ≤ version then some r.stored.bundle else none
  shouldOverrideBuilder := if 3 ≤ version then some r.stored.shouldOverrideBuilder else none
  executionRequests := if 4 ≤ version then some r.stored.built.requests else none

/-- The execution payload of a result as JSON: of version 4 from Glamsterdam. -/
def GetPayloadResult.payloadJson {fork : Fork} (r : GetPayloadResult fork) : Lean.Json :=
  if h : .glamsterdam ≤ fork then
    Json.executionPayloadV4Json r.payload (r.blockAccessList h) (r.slotNumber h)
  else Json.executionPayloadJson r.payload

/-- A result as JSON: the bare payload without a block value, else an object of its fields.

So the result of version 1 is the payload, and later versions write the fields they hold. -/
def getPayloadResultJson {fork : Fork} (r : GetPayloadResult fork) : Lean.Json :=
  match r.blockValue with
  | none => r.payloadJson
  | some value => Lean.Json.mkObj ([("executionPayload", r.payloadJson),
      ("blockValue", quantityJson value)] ++
      (r.blobsBundle.map fun b => ("blobsBundle", blobsBundleJson b)).toList ++
      (r.shouldOverrideBuilder.map fun o => ("shouldOverrideBuilder", Lean.Json.bool o)).toList ++
      (r.executionRequests.map fun rs =>
        ("executionRequests", listJson (dataJson ·.data.toList) rs)).toList)

/-- The field names of the result object, for a version from 2 on. -/
def getPayloadResultFields (version : Nat) : List String :=
  ["executionPayload", "blockValue"] ++
    (if 3 ≤ version then ["blobsBundle", "shouldOverrideBuilder"] else []) ++
    (if 4 ≤ version then ["executionRequests"] else [])

/-- A JSON boolean, or an invalid parameter that names the field. -/
def boolOfJson (what : String) : Lean.Json → Json.Decode Bool
  | .bool b => pure b
  | _ => Json.invalid s!"{what}: not a boolean"

/-- The execution payload of a result at a fork, of version 4 or of versions 1 to 3. -/
def resultPayloadOfJson (v4 : Bool) (fork : Fork) (j : Lean.Json) :
    Json.Decode (ExecutionPayload fork × Since .glamsterdam fork ByteArray ×
      Since .glamsterdam fork UInt64) := do
  let (any, amsterdam) ← if v4 then
      (fun (any, list, slot) => (any, some (list, slot))) <$> Json.payloadV4 j
    else (·, none) <$> Json.anyPayload j
  return (← any.atFork fork, ← Json.since "blockAccessList" (amsterdam.map (·.1)),
    ← Json.since "slotNumber" (amsterdam.map (·.2)))

/-- The result of a version of the method, for a payload of a fork that the version serves.

The fields are exactly those of the version, and each decodes as its type says.

Version 1 returns the payload, as [`engine_getPayloadV1`][v1] says.

Later versions return an object, whose payload is of version 4 only in [version 6][v6].

The bundle is of version 1 in versions 3 and 4, and of version 2 from version 5.

Execution requests must have increasing types and hold data, as [`engine_getPayloadV4`][v4] asks.

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_getpayloadv1
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#engine_getpayloadv4
[v6]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getpayloadv6 -/
def getPayloadResultOfJson (version : Nat) (fork : Fork) (j : Lean.Json) :
    Json.Decode (GetPayloadResult fork) := do
  unless acceptsGetPayloadFork version fork do
    Json.invalid s!"result: version {version} does not serve the fork"
  if version = 1 then
    let (payload, blockAccessList, slotNumber) ← resultPayloadOfJson false fork j
    return ⟨payload, blockAccessList, slotNumber, none, none, none, none⟩
  let fs ← fields "result" j
  unless hasExactly fs (getPayloadResultFields version) do
    Json.invalid "result: not the fields of its version"
  let get := field "result" fs
  let (payload, blockAccessList, slotNumber) ←
    resultPayloadOfJson (version = 6) fork (← get "executionPayload")
  let blockValue ← quantity "blockValue" 256 (← get "blockValue")
  let blobsBundle ← if 3 ≤ version then
    some <$> blobsBundleOfJson (blobsBundleVersion version) (← get "blobsBundle") else pure none
  let shouldOverrideBuilder ← if 3 ≤ version then
    some <$> boolOfJson "shouldOverrideBuilder" (← get "shouldOverrideBuilder") else pure none
  let executionRequests ← if 4 ≤ version then
    some <$> array "executionRequests" (bytes "request") (← get "executionRequests")
  else pure none
  if let some requests := executionRequests then
    unless validRequests requests do Json.invalid "executionRequests: out of order or too short"
  return ⟨payload, blockAccessList, slotNumber, some blockValue, blobsBundle,
    shouldOverrideBuilder, executionRequests⟩

end EthLib.Engine
