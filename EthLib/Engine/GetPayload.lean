module

public import EthLib.Engine.NewPayload
public import EthLib.Execution.Transactions.Network

/-!
# `Engine.GetPayload`

The latest completed payload of a build process, read by its eight-byte ID.

The store is a snapshot: its lookup gives the latest available payload immediately.

The method neither waits for more building nor changes the store.

The chain configuration determines the fork at the payload's number and timestamp.

Versions 1 and 2 serve Paris and Paris–Shapella respectively.

Versions 3, 4, 5 and 6 serve Dencun, Pectra, Fusaka–BPO5 and Glamsterdam respectively.

The bundle's commitments must hash to the payload's blob hashes, in order.

Its proofs are checked, with one per blob before Fusaka and 128 cell proofs per blob from it.

The method follows [version 1][v1], [2][v2], [3][v3], [4][v4], [5][v5] and [6][v6].

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_getpayloadv1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_getpayloadv3
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#engine_getpayloadv4
[v5]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/osaka.md#engine_getpayloadv5
[v6]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getpayloadv6
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Execution.Transactions

/-- The identifier of a payload build process. -/
abbrev PayloadId := Vector UInt8 8

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

/-- The latest completed payload of one build, with the fields returned beside it. -/
structure StoredPayload where
  /-- The fork at which the payload was built. -/
  fork : Fork
  /-- The execution payload at that fork. -/
  payload : ExecutionPayload fork
  /-- The expected value to the fee recipient, in wei. -/
  blockValue : U256
  /-- The blobs of the network transactions included in the payload. -/
  bundle : BlobsBundle
  /-- The requests of the executed payload, present from Pectra. -/
  requests : Since .pectra fork (List ByteArray)
  /-- Whether the builder recommends its payload over an external builder's. -/
  shouldOverrideBuilder : Bool
  /-- The block access list, from Glamsterdam. -/
  blockAccessList : Since .glamsterdam fork ByteArray
  /-- The beacon slot of the payload, from Glamsterdam. -/
  slotNumber : Since .glamsterdam fork UInt64

/-- A snapshot of build processes, each identified by its payload ID. -/
abbrev PayloadStore := PayloadId → Option StoredPayload

/-- A request error, or malformed data in the supplied snapshot of completed builds. -/
inductive GetPayloadError where
  /-- A request with no build, or for a fork that its version does not support. -/
  | engine (error : EngineError)
  /-- The stored payload's transactions do not decode. -/
  | transaction (error : PayloadError)
  /-- The stored bundle fails a count, hash or KZG check. -/
  | bundle (error : NetworkError)
  /-- The stored execution requests are out of order or have no data. -/
  | requests

/-- The forks whose payloads a version of the method returns. -/
def acceptsGetPayloadFork (version : Nat) (fork : Fork) : Bool :=
  match version with
  | 1 => decide (.paris ≤ fork ∧ fork < .shapella)
  | 2 => decide (.paris ≤ fork ∧ fork < .dencun)
  | 3 => decide (.dencun ≤ fork ∧ fork < .pectra)
  | 4 => decide (.pectra ≤ fork ∧ fork < .fusaka)
  | 5 => decide (.fusaka ≤ fork ∧ fork < .glamsterdam)
  | 6 => fork == .glamsterdam
  | _ => false

/-- Check the counts, ordered versioned hashes and proofs of a returned bundle. -/
def checkPayloadBundle (setup : TrustedSetup) (fork : Fork) (hashes : List Bytes32)
    (bundle : BlobsBundle) : Except NetworkError Unit := do
  unless hashes.length = bundle.blobs.length ∧
      bundle.commitments.length = bundle.blobs.length ∧
      bundle.proofs.length = proofCount fork bundle.blobs.length do
    throw (.countMismatch hashes.length bundle.blobs.length bundle.commitments.length
      bundle.proofs.length)
  unless bundle.commitments.map versionedHash = hashes do throw .versionedHashMismatch
  unless ← (verifyBlobBundle setup fork bundle.blobs bundle.commitments bundle.proofs).mapError
      .kzg do throw .proofRejected

/-- Read the latest payload of an ID, checking its fork and the bundle that it returns.

The snapshot supplies the output of execution, including the requests and the builder's value.

This method checks the requests' shape, and does not execute the payload again. -/
def getPayload (config : ChainConfig) (setup : TrustedSetup) (store : PayloadStore)
    (version : Nat) (id : PayloadId) : Except GetPayloadError StoredPayload :=
  match store id with
  | none => .error (.engine .unknownPayload)
  | some built =>
    if config.activeFork built.payload.blockNumber.toNat built.payload.timestamp.toNat =
        some built.fork ∧ acceptsGetPayloadFork version built.fork = true then
      if (if h : .pectra ≤ built.fork then validRequests (built.requests h) else true) then
        if version ≥ 3 then do
          let transactions ← (decodeTransactions built.fork 0 built.payload.transactions).mapError
            .transaction
          (checkPayloadBundle setup built.fork (ExecutionPayload.blobVersionedHashes transactions)
            built.bundle).mapError .bundle
          return built
        else .ok built
      else .error .requests
    else .error (.engine .unsupportedFork)

/-- The single eight-byte payload ID of the request. -/
def getPayloadParams (params : Lean.Json) : Json.Decode PayloadId := do
  match ← Json.paramsArray params with
  | [id] => Json.fixed "payloadId" 8 id
  | values => Json.invalid s!"params: got {values.length}, expected 1"

end EthLib.Engine
