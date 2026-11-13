module

public import Lean.Data.Json
public import EthLib.Base.Hex
public import EthLib.Serialization.JsonRpc
public import EthLib.Execution.Rpc.Json
public import EthLib.Engine.Payload

/-!
# `Engine.Json`

The JSON form of the parameters of the Engine API.

It also writes payloads, in the canonical form: lowercase hex, and numbers without leading zeros.

The Engine API is a JSON-RPC interface, with the encodings of the Ethereum JSON-RPC API.

This module reads the base types with readers that the execution JSON-RPC API shares.

An input that such a reader rejects is an invalid parameter, with JSON-RPC code `-32602`.

The base types state the patterns in [`base-types.yaml`][types].

So the extra data of a payload has at most 32 bytes, as its type `bytesMax32` says.

That is also the bound of the extra data of a block header.

Step 1 of [`engine_newPayloadV3`][v3] asks for exactly the expected fields, with `null` as absent.

Version 4 of the payload holds the fields of version 3, the block access list and the slot number.

The list is a byte string, and the slot number a 64-bit number, as [`amsterdam.md`][v4] writes.

A payload without the list is an invalid parameter, by step 2 of `engine_newPayloadV5`.

[types]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/base-types.yaml
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#specification
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#executionpayloadv4
-/

@[expose] public section

namespace EthLib.Engine.Json

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Rpc (withdrawal withdrawalJson)
open EthLib.Execution.Blocks (Withdrawal MAX_EXTRA_DATA_BYTES)

/-- A decoding that fails with an invalid parameter. -/
abbrev Decode := Except EngineError

/-- Fail with an invalid parameter, for a reason. -/
def invalid {α : Type} (reason : String) : Decode α := throw (.invalidParams reason)

/-- A shared reader as a decoding: a rejected input is an invalid parameter, for that reason. -/
def lift {α : Type} (r : Read α) : Decode α := r.mapError .invalidParams

/-- Each shared reader runs in a decoding, where it rejects with an invalid parameter.

The lift applies to every computation that fails with a string, not only to the shared readers. -/
instance : MonadLift Read Decode := ⟨lift⟩

/-- The fields of version 1 of an execution payload. -/
def payloadFieldsV1 : List String :=
  ["parentHash", "feeRecipient", "stateRoot", "receiptsRoot", "logsBloom", "prevRandao",
    "blockNumber", "gasLimit", "gasUsed", "timestamp", "extraData", "baseFeePerGas", "blockHash",
    "transactions"]

/-- The fields of version 2: version 1 and the withdrawals. -/
def payloadFieldsV2 : List String := payloadFieldsV1 ++ ["withdrawals"]

/-- The fields of version 3: version 2 and the two blob gas fields. -/
def payloadFieldsV3 : List String := payloadFieldsV2 ++ ["blobGasUsed", "excessBlobGas"]

/-- An execution payload of any version, with the fields of later versions present or not. -/
structure AnyPayload where
  /-- The version of the structure: 1, 2 or 3. -/
  version : Nat
  /-- The payload at Paris, with the fields of version 1. -/
  common : ExecutionPayload .paris
  /-- The withdrawals, present from version 2. -/
  withdrawals : Option (List Withdrawal)
  /-- The blob gas used, present in version 3. -/
  blobGasUsed : Option UInt64
  /-- The excess blob gas, present in version 3. -/
  excessBlobGas : Option UInt64

/-- An execution payload of version 1, 2 or 3, by the fields that it holds. -/
def anyPayload (j : Json) : Decode AnyPayload := do
  let fs ← fields "payload" j
  let version ←
    if hasExactly fs payloadFieldsV1 then pure 1
    else if hasExactly fs payloadFieldsV2 then pure 2
    else if hasExactly fs payloadFieldsV3 then pure 3
    else invalid "payload: the fields of no version"
  let get := field "payload" fs
  let common : ExecutionPayload .paris := {
    parentHash := ← fixed "parentHash" 32 (← get "parentHash")
    feeRecipient := ← address "feeRecipient" (← get "feeRecipient")
    stateRoot := ← fixed "stateRoot" 32 (← get "stateRoot")
    receiptsRoot := ← fixed "receiptsRoot" 32 (← get "receiptsRoot")
    logsBloom := ← fixed "logsBloom" 256 (← get "logsBloom")
    prevRandao := ← fixed "prevRandao" 32 (← get "prevRandao")
    blockNumber := ← uint64 "blockNumber" (← get "blockNumber")
    gasLimit := ← uint64 "gasLimit" (← get "gasLimit")
    gasUsed := ← uint64 "gasUsed" (← get "gasUsed")
    timestamp := ← uint64 "timestamp" (← get "timestamp")
    extraData := ← bytesMax "extraData" MAX_EXTRA_DATA_BYTES (← get "extraData")
    baseFeePerGas := BitVec.ofNat 256 (← quantity "baseFeePerGas" 256 (← get "baseFeePerGas"))
    blockHash := ← fixed "blockHash" 32 (← get "blockHash")
    transactions := ← array "transactions" (bytes "transaction") (← get "transactions")
    withdrawals := fun h => absurd h (by decide)
    blobGasUsed := fun h => absurd h (by decide)
    excessBlobGas := fun h => absurd h (by decide) }
  let withdrawals ← if version ≥ 2 then
    some <$> array "withdrawals" withdrawal (← get "withdrawals") else pure none
  let blobGasUsed ← if version ≥ 3 then
    some <$> uint64 "blobGasUsed" (← get "blobGasUsed") else pure none
  let excessBlobGas ← if version ≥ 3 then
    some <$> uint64 "excessBlobGas" (← get "excessBlobGas") else pure none
  return ⟨version, common, withdrawals, blobGasUsed, excessBlobGas⟩

/-- The two fields that version 4 of an execution payload appends to version 3. -/
def amsterdamFields : List String := ["blockAccessList", "slotNumber"]

/-- The fields of version 4: version 3, the block access list and the slot number. -/
def payloadFieldsV4 : List String := payloadFieldsV3 ++ amsterdamFields

/-- An execution payload of version 4: the payload of version 3, its access list and its slot.

The fields of version 3 decode as they do in version 3. -/
def payloadV4 (j : Json) : Decode (AnyPayload × ByteArray × UInt64) := do
  let fs ← fields "payload" j
  unless hasExactly fs payloadFieldsV4 do invalid "payload: not the fields of version 4"
  let any ← anyPayload (Json.mkObj (fs.filter fun (name, _) => !amsterdamFields.contains name))
  let blockAccessList ← bytes "blockAccessList" (← field "payload" fs "blockAccessList")
  let slotNumber ← uint64 "slotNumber" (← field "payload" fs "slotNumber")
  return (any, blockAccessList, slotNumber)

/-- A field from fork `f`, which must be present exactly when the fork has it. -/
def since {α : Type} {f fork : Fork} (what : String) : Option α → Decode (Since f fork α)
  | some x => if f ≤ fork then pure fun _ => x else invalid s!"{what}: present before its fork"
  | none =>
    if h : f ≤ fork then invalid s!"{what}: absent at its fork" else pure fun h' => absurd h' h

/-- The payload at a fork, whose fields must be exactly those of the fork's version. -/
def AnyPayload.atFork (p : AnyPayload) (fork : Fork) : Decode (ExecutionPayload fork) := do
  let c := p.common
  return {
    parentHash := c.parentHash, feeRecipient := c.feeRecipient, stateRoot := c.stateRoot,
    receiptsRoot := c.receiptsRoot, logsBloom := c.logsBloom, prevRandao := c.prevRandao,
    blockNumber := c.blockNumber, gasLimit := c.gasLimit, gasUsed := c.gasUsed,
    timestamp := c.timestamp, extraData := c.extraData, baseFeePerGas := c.baseFeePerGas,
    blockHash := c.blockHash, transactions := c.transactions
    withdrawals := ← since "withdrawals" p.withdrawals
    blobGasUsed := ← since "blobGasUsed" p.blobGasUsed
    excessBlobGas := ← since "excessBlobGas" p.excessBlobGas }

/-- The fields of an execution payload that versions 1 to 3 hold, those of its fork only.

They are written in the canonical form: lowercase hex, and numbers without leading zeros. -/
def executionPayloadFields {fork : Fork} (p : ExecutionPayload fork) : List (String × Json) :=
  [("parentHash", dataJson p.parentHash.toList), ("feeRecipient", dataJson p.feeRecipient.toList),
    ("stateRoot", dataJson p.stateRoot.toList), ("receiptsRoot", dataJson p.receiptsRoot.toList),
    ("logsBloom", dataJson p.logsBloom.toList), ("prevRandao", dataJson p.prevRandao.toList),
    ("blockNumber", quantityJson p.blockNumber.toNat), ("gasLimit", quantityJson p.gasLimit.toNat),
    ("gasUsed", quantityJson p.gasUsed.toNat), ("timestamp", quantityJson p.timestamp.toNat),
    ("extraData", dataJson p.extraData.data.toList),
    ("baseFeePerGas", quantityJson p.baseFeePerGas.toNat),
    ("blockHash", dataJson p.blockHash.toList),
    ("transactions", listJson (dataJson ·.data.toList) p.transactions)] ++
  (if h : .shapella ≤ fork then [("withdrawals", listJson withdrawalJson (p.withdrawals h))]
    else []) ++
  (if h : .dencun ≤ fork then
    [("blobGasUsed", quantityJson (p.blobGasUsed h).toNat),
      ("excessBlobGas", quantityJson (p.excessBlobGas h).toNat)] else [])

/-- An execution payload as JSON, with the fields of version 1, 2 or 3 that its fork has.

The source bounds the extra data to 32 bytes, and only then is the result a valid payload. -/
def executionPayloadJson {fork : Fork} (p : ExecutionPayload fork) : Json :=
  Json.mkObj (executionPayloadFields p)

/-- An execution payload of version 4 as JSON: the fields of its fork, the access list and the slot.

Only from Dencun on are they the fields of version 4. -/
def executionPayloadV4Json {fork : Fork} (p : ExecutionPayload fork) (blockAccessList : ByteArray)
    (slotNumber : UInt64) : Json :=
  Json.mkObj (executionPayloadFields p ++
    [("blockAccessList", dataJson blockAccessList.data.toList),
      ("slotNumber", quantityJson slotNumber.toNat)])

/-! ## Payload statuses -/

/-- The status whose name the Engine API writes, or none for any other text. -/
def statusOfName (name : String) : Option Status :=
  [Status.valid, .invalid, .syncing, .accepted, .invalidBlockHash].find? (·.name == name)

/-- A payload status as JSON, with its three fields: `PayloadStatusV1` of [`paris.md`][status].

The latest valid hash and the validation error are `null` when absent.

By step 5 of [payload validation][validation], a client may give the text of the validation error.

That step gives it for an invalid payload; the writer leaves the pairing to its caller.

[status]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payloadstatusv1
[validation]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-validation -/
def payloadStatusJson (s : PayloadStatus) (validationError : Option String) : Json :=
  Json.mkObj [("status", .str s.status.name),
    ("latestValidHash", optionJson (dataJson ·.toList) s.latestValidHash),
    ("validationError", optionJson .str validationError)]

/-- The three fields that a payload status may hold. -/
def payloadStatusFields : List String := ["status", "latestValidHash", "validationError"]

/-- A payload status, with its validation error.

The status is one of the five names, the hash 32 bytes, and the validation error a string.

[`paris.md`][status] lists three fields.

The OpenRPC schema `PayloadStatusV1` in [`payload.yaml`][schema] requires only the status.

So, as for the parameters, a field whose value is `null` counts as absent.

Any other field with a value other than `null` is invalid, a rule stricter than the schema states.

The decoder checks the form only, not which hash or error goes with which status.

A status that does not decode is an invalid parameter, code `-32602`, as for a request.

[status]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payloadstatusv1
[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/openrpc/schemas/payload.yaml -/
def payloadStatusOfJson (j : Json) : Decode (PayloadStatus × Option String) := do
  let fs ← fields "payloadStatus" j
  unless fs.all (payloadStatusFields.contains ·.1) do invalid "payloadStatus: unknown field"
  let name ← string "status" (← field "payloadStatus" fs "status")
  let some status := statusOfName name | invalid s!"payloadStatus: no status {name}"
  let latestValidHash ← lift ((fs.lookup "latestValidHash").mapM (fixed "latestValidHash" 32))
  let validationError ← lift ((fs.lookup "validationError").mapM (string "validationError"))
  return (⟨status, latestValidHash⟩, validationError)

end EthLib.Engine.Json

namespace EthLib.Engine

open EthLib.Base

/-- The value of a field from fork `f`, if the fork has the field. -/
def sinceValue {fork : Fork} {α : Type} {f : Fork} (x : Since f fork α) : Option α :=
  if h : f ≤ fork then some (x h) else none

/-- A request for more items than the node takes at once is too large. -/
def checkRequestSize (maxRequest count : Nat) : Except EngineError Unit :=
  if maxRequest < count then throw .tooLargeRequest else pure ()

/-! ## Errors -/

/-- The message of an error, from the table of [Errors][errors] in `common.md`.

The execution API gives `-32000` another message, so each API keeps its own table.

[errors]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/common.md#errors -/
def EngineError.message : EngineError → String
  | .invalidParams _ => "Invalid params"
  | .unsupportedFork => "Unsupported fork"
  | .invalidForkchoiceState => "Invalid forkchoice state"
  | .tooLargeRequest => "Too large request"
  | .invalidPayloadAttributes => "Invalid payload attributes"
  | .unknownPayload => "Unknown payload"

/-- The error object of an error: the negative of its code, its message, and `null` data.

The source gives every error `null` data, except `-32000`, which no Engine error has.

So the reason of invalid parameters is dropped, while the shared JSON-RPC error keeps it as data. -/
def EngineError.toRpcError (e : EngineError) : Serialization.JsonRpc.RpcError :=
  { code := -(e.code.toNat : Int), message := e.message, data := some .null }

end EthLib.Engine
