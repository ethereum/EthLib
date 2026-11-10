module

public import EthLib.Base.Exports.ChainConfig
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Engine.Exports.PayloadBodies
public import EthLib.Engine.GetPayload

/-!
# `Exports.GetPayload`

The C export of `engine_getPayloadV1` through `engine_getPayloadV6`.

The supplied store is a snapshot of completed builds, with no payload ID twice.

An entry holds an ID, a fork name, the payload's JSON value and its block value in wei.

Then come the network blob transactions, the execution requests and the override flag.

Lean decodes the network transactions and joins their sidecars in order.

The method checks this bundle against the payload, using the embedded trusted setup.

The configuration determines the fork at the payload's timestamp, as for `engine_newPayload`.

A malformed store has code 0; a request error has code 32602, 38001 or 38005.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)
open EthLib.Execution.Transactions
open EthLib.Engine.Json (dataJson quantityJson listJson withdrawalJson)

/-- An ID, fork, payload, block value, network transactions, execution requests and override. -/
abbrev PayloadEntry := PayloadId × String × PyValue × Nat × List ByteArray ×
  Option (List ByteArray) × Bool

/-- Decode one snapshot entry; the payload must have exactly the fields of its fork. -/
def storedPayloadOf (entry : PayloadEntry) : Result (PayloadId × StoredPayload) := do
  let (id, forkName, value, blockValue, sidecars, requests, shouldOverrideBuilder) := entry
  let fork ← EthLib.Exports.forkUpTo .glamsterdam forkName.toUTF8
  unless .paris ≤ fork do throw (0, "store: payload before Paris")
  unless blockValue < 2 ^ 256 do throw (0, "store: block value above 2^256")
  let decode {α : Type} (act : Json.Decode α) : Result α :=
    act.mapError fun e => (0, s!"store: {reprStr e}")
  let (any, extra) ← if .glamsterdam ≤ fork then do
      let (any, accessList, slot) ← decode (Json.payloadV4 value.toJson)
      pure (any, some (accessList, slot))
    else do
      let any ← decode (Json.anyPayload value.toJson)
      pure (any, none)
  let payload ← decode (any.atFork fork)
  let blockAccessList ← storeField (f := .glamsterdam) (fork := fork) "block access list"
    (extra.map (·.1))
  let slotNumber ← storeField (f := .glamsterdam) (fork := fork) "slot number" (extra.map (·.2))
  let requests ← storeField (f := .pectra) (fork := fork) "execution requests" requests
  let transactions ← sidecars.mapM fun bytes =>
    (decodeNetwork fork bytes).mapError fun e => (0, s!"store: network error {e.code}")
  let built : StoredPayload := {
    fork, payload
    blockValue := BitVec.ofNat 256 blockValue
    bundle := .ofNetwork transactions
    requests, shouldOverrideBuilder, blockAccessList, slotNumber }
  return (id, built)

/-- The version of an `engine_getPayloadV1` through `engine_getPayloadV6` method name. -/
def getPayloadVersion (method : String) : Option Nat :=
  ["engine_getPayloadV1", "engine_getPayloadV2", "engine_getPayloadV3", "engine_getPayloadV4",
    "engine_getPayloadV5", "engine_getPayloadV6"].idxOf? method |>.map (· + 1)

/-- The JSON fields of the execution payload, including only fields of its fork. -/
def storedPayloadJson (built : StoredPayload) : Json :=
  let p := built.payload
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
    (if h : .shapella ≤ built.fork then
      [("withdrawals", listJson withdrawalJson (p.withdrawals h))] else []) ++
    (if h : .dencun ≤ built.fork then
      [("blobGasUsed", quantityJson (p.blobGasUsed h).toNat),
        ("excessBlobGas", quantityJson (p.excessBlobGas h).toNat)] else []) ++
    (if h : .glamsterdam ≤ built.fork then
      [("blockAccessList", dataJson (built.blockAccessList h).data.toList),
        ("slotNumber", quantityJson (built.slotNumber h).toNat)] else []))

/-- The JSON fields of the blobs bundle, with its proof layout determined by the fork. -/
def blobsBundleJson (bundle : BlobsBundle) : Json :=
  Json.mkObj [("blobs", listJson (dataJson ·.toList) bundle.blobs),
    ("commitments", listJson (dataJson ·.toList) bundle.commitments),
    ("proofs", listJson (dataJson ·.toList) bundle.proofs)]

/-- Version 1 returns the payload alone; later versions append their fields in order. -/
def getPayloadResultJson (version : Nat) (built : StoredPayload) : Json :=
  if version = 1 then storedPayloadJson built else
  Json.mkObj ([("executionPayload", storedPayloadJson built),
    ("blockValue", quantityJson built.blockValue.toNat)] ++
    (if version ≥ 3 then [("blobsBundle", blobsBundleJson built.bundle),
      ("shouldOverrideBuilder", .bool built.shouldOverrideBuilder)] else []) ++
    (if h : .pectra ≤ built.fork then
      [("executionRequests", listJson (dataJson ·.data.toList) (built.requests h))] else []))

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
  let built ← (getPayload config setup (fun id => entries.lookup id) version id).mapError fun
    | .engine e => (e.code, s!"engine error: {reprStr e}")
    | .transaction e => (0, s!"store: payload error {e.code}")
    | .bundle e => (0, s!"store: bundle error {e.code}")
    | .requests => (0, "store: execution requests out of order or too short")
  return .ofJson (getPayloadResultJson version built)

/-- The answer to a get-payload request, from the configuration and a store snapshot. -/
@[export eth_engine_get_payload]
def getPayloadExport (args : PyValue) : Result PyValue := pyExport getPayloadOf args

end EthLib.Engine.Exports
