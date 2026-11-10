module

public import EthLib.Base.Exports.ChainConfig
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Engine.Exports.PayloadBodies
public import EthLib.Engine.GetPayload
public import EthLib.Execution.Exports.Transition

/-!
# `Exports.GetPayload`

The C export of `engine_getPayloadV1` through `engine_getPayloadV6`.

The supplied store is a snapshot of completed builds, with no payload ID twice.

An entry holds an ID, a fork name, and the four results of the payload build export.

They are the block in RLP form, the accounts after it, the requests and the block value in wei.

Then come the network blob transactions, the override flag and the block access list.

Lean decodes the network transactions and joins their sidecars in order.

The method checks this bundle against the block, using the embedded trusted setup.

The configuration determines the fork at the block's number and timestamp.

A malformed store or method name has code 0.

A parameter or request error has code 32602, 38001 or 38005.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)
open EthLib.Execution.Blocks (Block)
open EthLib.Execution.Transactions
open EthLib.Engine.Json (dataJson quantityJson listJson withdrawalJson)

/-- An ID, a fork, a block, accounts, requests, a value, network forms, an override and a list. -/
abbrev PayloadEntry := PayloadId × String × ByteArray × ByteArray × List ByteArray × Nat ×
  List ByteArray × Bool × Option ByteArray

/-- Decode one snapshot entry; the block access list must be given exactly from Glamsterdam. -/
def storedPayloadOf (entry : PayloadEntry) : Result (PayloadId × StoredPayload) := do
  let (id, forkName, block, accounts, requests, blockValue, sidecars, shouldOverrideBuilder,
    accessList) := entry
  let fork ← EthLib.Exports.forkUpTo .glamsterdam forkName.toUTF8
  unless blockValue < 2 ^ 256 do throw (0, "store: block value above 2^256")
  let items : Block fork Serialization.Rlp.Item ← (Block.decode (fun _ => fork) block).mapError
    fun e => (0, s!"store: block rejected: {reprStr e}")
  let transactions ← items.transactions.mapM fun item =>
    (decodeBodyTransaction fork item).mapError fun e =>
      (0, s!"store: transaction rejected: {reprStr e}")
  let state ← (Execution.State.Exports.ofInput accounts).mapError
    fun e => (0, s!"store: {e.message}")
  let blockAccessList ← storeField (f := .glamsterdam) (fork := fork) "block access list"
    accessList
  let network ← sidecars.mapM fun bytes =>
    (decodeNetwork fork bytes).mapError fun e => (0, s!"store: network error {e.code}")
  let built : BuiltPayload fork :=
    { block := ⟨items.header, transactions, items.ommers, items.withdrawals⟩
      state, requests, blockValue }
  return (id, { fork, built, bundle := .ofNetwork network, shouldOverrideBuilder, blockAccessList })

/-- The version of an `engine_getPayloadV1` through `engine_getPayloadV6` method name. -/
def getPayloadVersion (method : String) : Option Nat :=
  ["engine_getPayloadV1", "engine_getPayloadV2", "engine_getPayloadV3", "engine_getPayloadV4",
    "engine_getPayloadV5", "engine_getPayloadV6"].idxOf? method |>.map (· + 1)

/-- The JSON fields of the execution payload, including only fields of its fork. -/
def payloadJson (r : GetPayloadResponse) : Json :=
  let p := r.payload
  let header := r.stored.built.block.header
  Json.mkObj (
    [("parentHash", dataJson p.parentHash.toList),
      ("feeRecipient", dataJson p.feeRecipient.toList), ("stateRoot", dataJson p.stateRoot.toList),
      ("receiptsRoot", dataJson p.receiptsRoot.toList), ("logsBloom", dataJson p.logsBloom.toList),
      ("prevRandao", dataJson p.prevRandao.toList),
      ("blockNumber", quantityJson p.blockNumber.toNat),
      ("gasLimit", quantityJson p.gasLimit.toNat),
      ("gasUsed", quantityJson p.gasUsed.toNat), ("timestamp", quantityJson p.timestamp.toNat),
      ("extraData", dataJson p.extraData.data.toList),
      ("baseFeePerGas", quantityJson p.baseFeePerGas.toNat),
      ("blockHash", dataJson p.blockHash.toList),
      ("transactions", listJson (dataJson ·.data.toList) p.transactions)] ++
    (if h : .shapella ≤ r.stored.fork then
      [("withdrawals", listJson withdrawalJson (p.withdrawals h))] else []) ++
    (if h : .dencun ≤ r.stored.fork then
      [("blobGasUsed", quantityJson (p.blobGasUsed h).toNat),
        ("excessBlobGas", quantityJson (p.excessBlobGas h).toNat)] else []) ++
    (if h : .glamsterdam ≤ r.stored.fork then
      [("blockAccessList", dataJson (r.stored.blockAccessList h).data.toList),
        ("slotNumber", quantityJson (header.slotNumber h).toNat)] else []))

/-- The JSON fields of the blobs bundle: its blobs, commitments and proofs, in order. -/
def blobsBundleJson (bundle : BlobsBundle) : Json :=
  Json.mkObj [("blobs", listJson (dataJson ·.toList) bundle.blobs),
    ("commitments", listJson (dataJson ·.toList) bundle.commitments),
    ("proofs", listJson (dataJson ·.toList) bundle.proofs)]

/-- Version 1 returns the payload alone; later versions append their fields in order. -/
def getPayloadResultJson (version : Nat) (r : GetPayloadResponse) : Json :=
  if version = 1 then payloadJson r else
  Json.mkObj ([("executionPayload", payloadJson r),
    ("blockValue", quantityJson r.stored.built.blockValue)] ++
    (if version ≥ 3 then [("blobsBundle", blobsBundleJson r.stored.bundle),
      ("shouldOverrideBuilder", .bool r.stored.shouldOverrideBuilder)] else []) ++
    (if version ≥ 4 then
      [("executionRequests", listJson (dataJson ·.data.toList) r.stored.built.requests)]
    else []))

/-- The answer to a get-payload request, from a snapshot of build processes. -/
def getPayloadOf (args : PyValue × List PayloadEntry × PyValue) : Result PyValue := do
  let (config, entries, request) := args
  let config ← configOfJson config.toJson
  let entries ← entries.mapM storedPayloadOf
  unless (entries.map (·.1)).Nodup do throw (0, "store: two entries with one payload ID")
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := getPayloadVersion method | throw (0, s!"no method {method}")
  let id ← (getPayloadParams (request.getObjValD "params")).mapError
    fun e => (e.code, s!"engine error: {reprStr e}")
  let setup ← Cryptography.Kzg.Exports.embeddedSetup.mapError
    fun e => (0, s!"setup: {e.message}")
  let r ← (getPayload config setup (fun id => entries.lookup id) version id).mapError fun
    | .engine e => (e.code, s!"engine error: {reprStr e}")
    | .wrongFork => (0, "store: the fork is not the configured fork at the block")
    | .requests => (0, "store: execution requests out of order, too short or before Pectra")
    | .blockAccessList => (0, "store: block access list does not match the header")
    | .noPayload => (0, "store: the block has no payload form")
    | .bundle e => (0, s!"store: bundle error {e.code}")
  return .ofJson (getPayloadResultJson version r)

/-- The answer to an `engine_getPayload` request, from the configuration and a store snapshot.

The arguments are the chain configuration, the entries of the store and the request.

Each entry is the payload ID, the fork name and the four results of the payload build export.

Then come its network blob transactions, the override flag and the block access list or `None`. -/
@[export eth_engine_get_payload]
def getPayloadExport (args : PyValue) : Result PyValue := pyExport getPayloadOf args

end EthLib.Engine.Exports
