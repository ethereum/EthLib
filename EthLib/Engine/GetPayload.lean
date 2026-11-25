module

public import EthLib.Engine.BuildPayload
public import EthLib.Engine.NewPayload
public import EthLib.Execution.Transactions.Network

/-!
# `Engine.GetPayload`

The latest completed payload of a build process, read by its eight-byte ID, in versions 1 to 6.

A step comment names the version of the method, as in version 3, step 3.

The Engine API names Shanghai, Cancun, Prague, Osaka and Amsterdam by their execution side.

They are Shapella, Dencun, Pectra, Fusaka and Glamsterdam here.

Sources, at commit `1ca0818` of execution-apis:

- versions [1][v1], [2][v2], [3][v3], [4][v4], [5][v5] and [6][v6] of the method
- the updates by [Cancun][c], [Prague][p], [Osaka][o] and [Amsterdam][a]: bounds of versions 2 to 5

[v1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_getpayloadv1
[v2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#engine_getpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#engine_getpayloadv3
[v4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/prague.md#engine_getpayloadv4
[v5]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#engine_getpayloadv5
[v6]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#engine_getpayloadv6
[c]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#update-the-methods-of-previous-forks
[p]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/prague.md#update-the-methods-of-previous-forks
[o]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#update-the-methods-of-previous-forks
[a]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#update-the-methods-of-previous-forks
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Execution.Blocks (Block MAX_EXTRA_DATA_BYTES)
open EthLib.Execution.Transactions
open EthLib.Serialization.JsonRpc (dataJson fixed paramsArray fields hasExactly field array bytes
  quantity quantityJson listJson bool)

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
  /-- The stored fork, `stored`, is not the fork of the configuration at the block, `active`.

  `active` is none when no fork is active at the block. -/
  | wrongFork (stored : Fork) (active : Option Fork)
  /-- The stored execution requests are out of order, have no data, or precede Pectra. -/
  | requests
  /-- The stored block value, `value`, does not fit in 256 bits. -/
  | blockValue (value : Nat)
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
  -- Version 1 states no range of forks.
  --
  -- EthLib takes Paris only, as for `engine_newPayloadV1`, so any other fork is `-38005`.
  | 1 => fork == .paris
  -- Version 2: the forks before Cancun, by the update in `cancun.md`, here Paris and Shapella.
  | 2 => fork == .paris || fork == .shapella
  -- Version 3, step 1: the time frame of Cancun, here Dencun.
  --
  -- The update in `prague.md` also rejects a payload from Prague on.
  | 3 => fork == .dencun
  -- Version 4, step 1: the time frame of Prague, here Pectra.
  --
  -- The update in `osaka.md` also rejects a payload from Osaka on.
  | 4 => fork == .pectra
  -- Version 5, step 1: the time frame of Osaka, here Fusaka.
  --
  -- The update in `amsterdam.md` also rejects a payload from Amsterdam on.
  --
  -- BPO1 to BPO5 change only blob parameters, so EthLib counts them in the time frame of Osaka.
  | 5 => decide (.fusaka ≤ fork) && decide (fork < .glamsterdam)
  -- Version 6, step 1: the time frame of Amsterdam, here Glamsterdam.
  | 6 => fork == .glamsterdam
  -- No other version of the method exists.
  | _ => false

/-- Whether requests have the shape of their fork: none before Pectra, valid lists from it. -/
def requestsOfFork (fork : Fork) (requests : List ByteArray) : Bool :=
  -- Version 4, step 2: from Pectra, each element has over 1 byte, in ascending order of type.
  --
  -- Each type appears at most once, so the types strictly increase.
  --
  -- Before Pectra, a block has no requests of EIP-7685.
  if .pectra ≤ fork then validRequests requests else requests.isEmpty

/-- The payload form of a block, which exists only from Paris.

It keeps the bounds of [its type][p] in the Engine API.

[p]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#executionpayloadv1 -/
def payloadOfBlock {fork : Fork} (block : Block fork Transaction) :
    Option (ExecutionPayload fork) :=
  if h : .paris ≤ fork then
    -- `ExecutionPayloadV1`: `extraData` is `DATA` of 0 to 32 bytes.
    (ExecutionPayload.ofBlock h block).filter (·.extraData.size ≤ MAX_EXTRA_DATA_BYTES)
  -- No version of the structure holds a block before Paris.
  else none

/-- The block that a payload gives back, with the stored requests and access list.

The parent beacon block root and the slot are those of the stored header. -/
def StoredPayload.blockOfPayload (stored : StoredPayload)
    (payload : ExecutionPayload stored.fork) :
    Except PayloadError (Block stored.fork Transaction) :=
  let header := stored.built.block.header
  -- The checks of the block hash of `engine_newPayload`, with the fields passed beside the payload.
  payload.toBlock header.parentBeaconBlockRoot (fun _ => stored.built.requests)
    stored.built.blockAccessList header.slotNumber

/-- Read the latest build of an ID, checking its fork and, from version 3, its bundle.

The snapshot supplies the output of the build, including the requests and the block value.

This method checks their shape against the fork, and does not execute the block again. -/
def getPayload (config : ChainConfig) (setup : TrustedSetup) (store : PayloadStore)
    (version : Nat) (id : PayloadId) : Except GetPayloadError GetPayloadResponse := do
  -- Version 1, step 3: no build process with the ID is `-38001`, unknown payload.
  --
  -- Steps 1 and 2: the most recent payload of the build, at once, so the store is a snapshot.
  --
  -- Step 4 lets the client stop the build, which EthLib leaves out: the store does not change.
  let some stored := store id | throw (.engine (.unknownPayload id))
  let block := stored.built.block
  -- Not in the source: the stored fork is the active fork at the number and the timestamp.
  --
  -- The check of the version reads the stored fork, so EthLib checks the snapshot first.
  let active := config.activeFork block.header.number block.header.timestamp.toNat
  unless active = some stored.fork do throw (.wrongFork stored.fork active)
  -- Step 1 of versions 3 to 6, and the updates of later forks: another fork is `-38005`.
  unless acceptsGetPayloadFork version stored.fork do
    throw (.engine (.unsupportedFork (some stored.fork)))
  -- Version 4, step 2: the requests are in ascending order of unique types, each over 1 byte long.
  --
  -- The method checks the stored requests by their shape, since it does not run the block again.
  unless requestsOfFork stored.fork stored.built.requests do throw .requests
  -- Version 2: `blockValue` is a `QUANTITY` of 256 bits.
  --
  -- Version 2, step 1 leaves its computation to the client, so the snapshot supplies it.
  --
  -- Version 1 returns no block value, and EthLib checks the stored one in every version.
  unless stored.built.blockValue < 2 ^ 256 do throw (.blockValue stored.built.blockValue)
  -- The execution payload of the block, in the bounds of the structure that the version returns.
  let some payload := payloadOfBlock block | throw .noPayload
  -- Not in the source: the payload gives back a block with the stored block hash.
  --
  -- It is the check of `engine_newPayload`.
  --
  -- So the hash commits to the transactions, the requests and the access list that it returns.
  if let .error e := stored.blockOfPayload payload then throw (.header e)
  -- Version 3, step 3: the commitments match the versioned hashes of the transactions, in order.
  --
  -- Step 2: without blob transactions there is no hash, so the bundle is empty.
  --
  -- Before Osaka, step 4: as many blobs and proofs as commitments, and the blob proofs verify.
  --
  -- From Osaka, version 5, step 3: `CELLS_PER_EXT_BLOB = 128` proofs per blob, and they verify.
  --
  -- EthLib checks every count, that of the versioned hashes too, before the hashes of step 3.
  if 3 ≤ version then
    (validateBlobs setup stored.fork (ExecutionPayload.blobVersionedHashes block.transactions)
      stored.bundle.blobs stored.bundle.commitments stored.bundle.proofs).mapError .bundle
  return ⟨stored, payload⟩

/-- The single eight-byte payload ID of the request. -/
def getPayloadParams (params : Lean.Json) : Json.Decode PayloadId := do
  match ← paramsArray params with
  -- Version 1, request: one parameter, `payloadId`, `DATA` of 8 bytes, in every version.
  | [id] => fixed "payloadId" 8 id
  -- The source names no error for another count, and EthLib gives `-32602`, invalid params.
  | values => Json.invalid s!"params: got {values.length}, expected 1"

/-- The request as the consensus layer writes it in JSON: the payload ID alone. -/
def getPayloadParamsJson (id : PayloadId) : Lean.Json := .arr #[dataJson id.toList]

/-! ## The result -/

/-- The version of the bundle, 1 or 2, that a version of the method returns: 2 from version 5. -/
def blobsBundleVersion (version : Nat) : Nat :=
  -- Versions 3 and 4 return `BlobsBundleV1`, and versions 5 and 6 `BlobsBundleV2`.
  if 5 ≤ version then 2 else 1

/-- The proofs per blob in a bundle of a version, 1 or 2: one, or one per cell in version 2. -/
def BlobsBundle.proofsPerBlob (version : Nat) : Nat :=
  -- `BlobsBundleV1` has one proof per blob, and `BlobsBundleV2` one per cell.
  if version < 2 then 1 else Constants.CELLS_PER_EXT_BLOB

/-- The length rules of a bundle of a version, 1 or 2: one commitment and its proofs per blob.

They are those of [BlobsBundleV1][v1] and [BlobsBundleV2][v2].

[v1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#blobsbundlev1
[v2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#blobsbundlev2 -/
def BlobsBundle.lengthsHold (version : Nat) (b : BlobsBundle) : Bool :=
  -- `BlobsBundleV1`: the three arrays have one length.
  --
  -- `BlobsBundleV2`: as many commitments as blobs, and `CELLS_PER_EXT_BLOB` proofs per blob.
  b.commitments.length == b.blobs.length &&
    b.proofs.length == BlobsBundle.proofsPerBlob version * b.blobs.length

/-- A blobs bundle as JSON: its blobs, commitments and proofs, in order. -/
def blobsBundleJson (b : BlobsBundle) : Lean.Json :=
  -- Each array holds `DATA` values, in another order than the source, as RFC 8259, §1 allows.
  --
  -- An object of JSON is an unordered collection of members.
  Lean.Json.mkObj [("blobs", listJson (dataJson ·.toList) b.blobs),
    ("commitments", listJson (dataJson ·.bytes.toList) b.commitments),
    ("proofs", listJson (dataJson ·.bytes.toList) b.proofs)]

/-- The three fields of a blobs bundle. -/
def blobsBundleFields : List String := ["blobs", "commitments", "proofs"]

/-- A blobs bundle of a version, 1 or 2, which must pass the length rules of that version. -/
def blobsBundleOfJson (version : Nat) (j : Lean.Json) : Json.Decode BlobsBundle := do
  let fs ← fields "blobsBundle" j
  -- `BlobsBundleV1` and `BlobsBundleV2`: the fields `blobs`, `commitments` and `proofs`.
  --
  -- Not in the source: EthLib rejects any other member.
  unless hasExactly fs blobsBundleFields do Json.invalid "blobsBundle: not the fields of a bundle"
  let get := field "blobsBundle" fs
  let bundle : BlobsBundle := {
    -- Each blob is `FIELD_ELEMENTS_PER_BLOB * BYTES_PER_FIELD_ELEMENT = 4096 * 32 = 131072` bytes.
    blobs := ← array "blobs" (fixed "blob" _) (← get "blobs")
    -- Each commitment and each proof is 48 bytes.
    commitments := (← array "commitments" (fixed "commitment" 48) (← get "commitments")).map .mk
    proofs := (← array "proofs" (fixed "proof" 48) (← get "proofs")).map .mk }
  -- The length rules of the version of the bundle.
  unless bundle.lengthsHold version do Json.invalid "blobsBundle: lengths do not match"
  return bundle

/-- What a consensus node reads from the result of the method, at the fork of the payload.

The writer writes the options that are present, so they must follow the version. -/
structure GetPayloadResult (fork : Fork) where
  /-- The execution payload. -/
  payload : ExecutionPayload fork
  /-- The block access list of a payload from Glamsterdam. -/
  blockAccessList : Since .glamsterdam fork ByteArray
  /-- The slot number of a payload from Glamsterdam. -/
  slotNumber : Since .glamsterdam fork UInt64
  /-- The value of the block to its proposer, in wei, present from version 2. -/
  blockValue : Option Nat
  /-- The blobs, commitments and proofs of the blob transactions of the payload.

  The bundle is present from version 3. -/
  blobsBundle : Option BlobsBundle
  /-- Whether the execution layer suggests its own payload over one of an external builder.

  The flag is present from version 3. -/
  shouldOverrideBuilder : Option Bool
  /-- The execution requests of the payload, present from version 4. -/
  executionRequests : Option (List ByteArray)

/-- What a response holds at a version of the method: the fields of that version. -/
def GetPayloadResponse.result (version : Nat) (r : GetPayloadResponse) :
    GetPayloadResult r.stored.fork where
  -- `executionPayload`, in every version.
  payload := r.payload
  -- From Glamsterdam, the two fields that `ExecutionPayloadV4` appends.
  blockAccessList := r.stored.built.blockAccessList
  slotNumber := r.stored.built.block.header.slotNumber
  -- Version 2 adds `blockValue`.
  blockValue := if 2 ≤ version then some r.stored.built.blockValue else none
  -- Version 3 adds `blobsBundle` and `shouldOverrideBuilder`.
  blobsBundle := if 3 ≤ version then some r.stored.bundle else none
  shouldOverrideBuilder := if 3 ≤ version then some r.stored.shouldOverrideBuilder else none
  -- Version 4 adds `executionRequests`.
  executionRequests := if 4 ≤ version then some r.stored.built.requests else none

/-- The execution payload of a result as JSON: of version 4 from Glamsterdam. -/
def GetPayloadResult.payloadJson {fork : Fork} (r : GetPayloadResult fork) : Lean.Json :=
  -- Version 6 returns `ExecutionPayloadV4`, and only version 6 serves Glamsterdam.
  --
  -- So EthLib picks the structure by the fork, which makes the same choice.
  if h : .glamsterdam ≤ fork then
    Json.executionPayloadV4Json r.payload (r.blockAccessList h) (r.slotNumber h)
  -- Versions 1 to 5: version 1, 2 or 3 of the structure, the one of the fork.
  else Json.executionPayloadJson r.payload

/-- A result as JSON: the bare payload without a block value, else an object of its fields.

The consensus layer writes it back as JSON. -/
def getPayloadResultJson {fork : Fork} (r : GetPayloadResult fork) : Lean.Json :=
  match r.blockValue with
  -- Version 1: the result is `ExecutionPayloadV1` itself, and only version 1 has no block value.
  | none => r.payloadJson
  -- From version 2: an object, with the fields that the version holds.
  | some value => Lean.Json.mkObj ([("executionPayload", r.payloadJson),
      ("blockValue", quantityJson value)] ++
      (r.blobsBundle.map fun b => ("blobsBundle", blobsBundleJson b)).toList ++
      (r.shouldOverrideBuilder.map fun o => ("shouldOverrideBuilder", Lean.Json.bool o)).toList ++
      (r.executionRequests.map fun rs =>
        ("executionRequests", listJson (dataJson ·.data.toList) rs)).toList)

/-- The field names of the result object, for a version from 2 on. -/
def getPayloadResultFields (version : Nat) : List String :=
  -- Version 2: `executionPayload` and `blockValue`, then the fields that versions 3 and 4 add.
  ["executionPayload", "blockValue"] ++
    (if 3 ≤ version then ["blobsBundle", "shouldOverrideBuilder"] else []) ++
    (if 4 ≤ version then ["executionRequests"] else [])

/-- The execution payload of a result at a fork, of version 4 or of versions 1 to 3. -/
def resultPayloadOfJson (v4 : Bool) (fork : Fork) (j : Lean.Json) :
    Json.Decode (ExecutionPayload fork × Since .glamsterdam fork ByteArray ×
      Since .glamsterdam fork UInt64) := do
  -- `ExecutionPayloadV4`, or version 1, 2 or 3 of the structure by the fields that it holds.
  let (any, amsterdam) ← if v4 then
      (fun (any, list, slot) => (any, some (list, slot))) <$> Json.payloadV4 j
    else (·, none) <$> Json.anyPayload j
  -- The version of the structure is that of the fork, by the rule of version 2.
  --
  -- So version 1 before Shanghai, 2 from it, and 3 from Cancun.
  --
  -- The access list and the slot number are present exactly from Glamsterdam.
  return (← any.atFork fork, ← Json.since "blockAccessList" (amsterdam.map (·.1)),
    ← Json.since "slotNumber" (amsterdam.map (·.2)))

/-- The result of a version of the method, for a payload of a fork that the version serves.

The consensus layer reads it as JSON, at the fork of the payload.

It reads the response of each version, as [version 1][v1], [version 4][v4] and [version 6][v6] say.

[v1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_getpayloadv1
[v4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/prague.md#engine_getpayloadv4
[v6]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#engine_getpayloadv6 -/
def getPayloadResultOfJson (version : Nat) (fork : Fork) (j : Lean.Json) :
    Json.Decode (GetPayloadResult fork) := do
  -- Step 1 of versions 3 to 6, and the updates: the version serves the fork of the payload.
  unless acceptsGetPayloadFork version fork do
    Json.invalid s!"result: version {version} does not serve the fork"
  -- Version 1: the result is `ExecutionPayloadV1`.
  if version = 1 then
    let (payload, blockAccessList, slotNumber) ← resultPayloadOfJson false fork j
    return ⟨payload, blockAccessList, slotNumber, none, none, none, none⟩
  -- From version 2: an object with the fields of the version.
  --
  -- Not in the source: EthLib rejects any other member.
  let fs ← fields "result" j
  unless hasExactly fs (getPayloadResultFields version) do
    Json.invalid "result: not the fields of its version"
  let get := field "result" fs
  -- Version 6: `ExecutionPayloadV4`; versions 2 to 5: version 1, 2 or 3 of the structure.
  let (payload, blockAccessList, slotNumber) ←
    resultPayloadOfJson (version = 6) fork (← get "executionPayload")
  -- `blockValue`: a `QUANTITY` of 256 bits.
  let blockValue ← quantity "blockValue" 256 (← get "blockValue")
  -- From version 3: `BlobsBundleV1` in versions 3 and 4, and `BlobsBundleV2` from version 5.
  let blobsBundle ← if 3 ≤ version then
    some <$> blobsBundleOfJson (blobsBundleVersion version) (← get "blobsBundle") else pure none
  -- From version 3: `shouldOverrideBuilder`, a `BOOLEAN`.
  let shouldOverrideBuilder ← if 3 ≤ version then
    some <$> Json.lift (bool "shouldOverrideBuilder" (← get "shouldOverrideBuilder"))
  else pure none
  -- From version 4: `executionRequests`, an array of `DATA`.
  let executionRequests ← if 4 ≤ version then
    some <$> array "executionRequests" (bytes "request") (← get "executionRequests")
  else pure none
  -- Version 4, step 2: each element is longer than 1 byte, in ascending order of unique types.
  if let some requests := executionRequests then
    unless validRequests requests do Json.invalid "executionRequests: out of order or too short"
  return ⟨payload, blockAccessList, slotNumber, some blockValue, blobsBundle,
    shouldOverrideBuilder, executionRequests⟩

end EthLib.Engine
