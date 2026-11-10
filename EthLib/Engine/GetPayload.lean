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
  /-- The block has no payload form, since a field does not fit or has no encoding. -/
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

/-- The payload form of a block, which exists only from Paris. -/
def payloadOfBlock {fork : Fork} (block : Block fork Transaction) :
    Option (ExecutionPayload fork) :=
  if h : .paris ≤ fork then ExecutionPayload.ofBlock h block else none

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
  match ← Json.paramsArray params with
  | [id] => Json.fixed "payloadId" 8 id
  | values => Json.invalid s!"params: got {values.length}, expected 1"

end EthLib.Engine
