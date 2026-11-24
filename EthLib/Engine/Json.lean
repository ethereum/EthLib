module

public import Lean.Data.Json
public import EthLib.Base.Hex
public import EthLib.Serialization.JsonRpc
public import EthLib.Execution.Rpc.Json
public import EthLib.Engine.Payload

/-!
# `Engine.Json`

The JSON form of the parameters of the Engine API, and of its payloads and payload statuses.

The Engine API is a JSON-RPC interface, with the encodings of the Ethereum JSON-RPC API.

The module reads the base types with the readers that the execution JSON-RPC API shares.

Sources, at commit `1ca0818` of execution-apis:

- the [encoding][encoding] and the table of [errors][errors] in `common.md`
- the patterns of the base types in [`base-types.yaml`][types]
- step 1 of [`engine_newPayloadV3`][v3], in Cancun
- the request of [`engine_newPayloadV2`][v2], in Shanghai
- [`ExecutionPayloadV4`][v4] and step 2 of [`engine_newPayloadV5`][v5], in Amsterdam

[encoding]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#encoding
[errors]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#errors
[types]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/base-types.yaml
[v2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#engine_newpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#specification
[v4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#executionpayloadv4
[v5]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#engine_newpayloadv5
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

/-- A shared reader as a decoding: a rejected input is an invalid parameter, for that reason.

Its code is `-32602`, invalid params, in the table of errors. -/
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
  -- `engine_newPayloadV3`, step 1: a field whose value is `null` counts as not provided.
  let fs ← fields "payload" j
  -- Step 1: the fields match one structure exactly, else `-32602`, invalid params.
  --
  -- EthLib reads the version from the fields, and the fork of the payload checks it after.
  let version ←
    if hasExactly fs payloadFieldsV1 then pure 1
    else if hasExactly fs payloadFieldsV2 then pure 2
    else if hasExactly fs payloadFieldsV3 then pure 3
    else invalid "payload: the fields of no version"
  let get := field "payload" fs
  -- `ExecutionPayloadV1`: each field is `DATA` or `QUANTITY`, of the size that the structure sets.
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
    -- `extraData`: `DATA` of 0 to 32 bytes, the type `bytesMax32` of the base types.
    --
    -- That is also the bound of the extra data of a block header.
    extraData := ← bytesMax "extraData" MAX_EXTRA_DATA_BYTES (← get "extraData")
    baseFeePerGas := BitVec.ofNat 256 (← quantity "baseFeePerGas" 256 (← get "baseFeePerGas"))
    blockHash := ← fixed "blockHash" 32 (← get "blockHash")
    -- `transactions`: an `Array of DATA`, each entry a byte list.
    transactions := ← array "transactions" (bytes "transaction") (← get "transactions")
    -- Paris has none of the fields that later versions add.
    withdrawals := fun h => absurd h (by decide)
    blobGasUsed := fun h => absurd h (by decide)
    excessBlobGas := fun h => absurd h (by decide) }
  -- `ExecutionPayloadV2` adds `withdrawals`, an `Array of WithdrawalV1`.
  let withdrawals ← if version ≥ 2 then
    some <$> array "withdrawals" withdrawal (← get "withdrawals") else pure none
  -- `ExecutionPayloadV3` adds `blobGasUsed` and `excessBlobGas`, each a `QUANTITY` of 64 bits.
  let blobGasUsed ← if version ≥ 3 then
    some <$> uint64 "blobGasUsed" (← get "blobGasUsed") else pure none
  let excessBlobGas ← if version ≥ 3 then
    some <$> uint64 "excessBlobGas" (← get "excessBlobGas") else pure none
  return ⟨version, common, withdrawals, blobGasUsed, excessBlobGas⟩

/-- The two fields that version 4 of an execution payload appends to version 3. -/
def amsterdamFields : List String := ["blockAccessList", "slotNumber"]

/-- The fields of version 4: version 3, the block access list and the slot number. -/
def payloadFieldsV4 : List String := payloadFieldsV3 ++ amsterdamFields

/-- An execution payload of version 4: the payload of version 3, its access list and its slot. -/
def payloadV4 (j : Json) : Decode (AnyPayload × ByteArray × UInt64) := do
  -- `engine_newPayloadV3`, step 1: a field whose value is `null` counts as not provided.
  let fs ← fields "payload" j
  -- `ExecutionPayloadV4`: the fields of version 3, then `blockAccessList` and `slotNumber`.
  --
  -- `engine_newPayloadV5`, step 2: a missing `blockAccessList` is `-32602`, invalid params.
  unless hasExactly fs payloadFieldsV4 do invalid "payload: not the fields of version 4"
  -- The fields of version 3 decode as they do in version 3.
  let any ← anyPayload (Json.mkObj (fs.filter fun (name, _) => !amsterdamFields.contains name))
  -- `blockAccessList`: `DATA`, the RLP form of the block access list of EIP-7928.
  --
  -- This reader takes any bytes, and does not check that RLP form.
  let blockAccessList ← bytes "blockAccessList" (← field "payload" fs "blockAccessList")
  -- `slotNumber`: a `QUANTITY` of 64 bits.
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
    -- `engine_newPayloadV2`, request: the structure must be the version of the fork of the payload.
    --
    -- The wrong version of the structure is `-32602`, invalid params.
    withdrawals := ← since "withdrawals" p.withdrawals
    blobGasUsed := ← since "blobGasUsed" p.blobGasUsed
    excessBlobGas := ← since "excessBlobGas" p.excessBlobGas }

/-- The fields of an execution payload that versions 1 to 3 hold, those of its fork only.

They are written in the canonical form: lowercase hex, and numbers without leading zeros. -/
def executionPayloadFields {fork : Fork} (p : ExecutionPayload fork) : List (String × Json) :=
  -- Encoding: `DATA` as `0x` and two hex digits per byte, `QUANTITY` without leading zeros.
  [("parentHash", dataJson p.parentHash.toList), ("feeRecipient", dataJson p.feeRecipient.toList),
    ("stateRoot", dataJson p.stateRoot.toList), ("receiptsRoot", dataJson p.receiptsRoot.toList),
    ("logsBloom", dataJson p.logsBloom.toList), ("prevRandao", dataJson p.prevRandao.toList),
    ("blockNumber", quantityJson p.blockNumber.toNat), ("gasLimit", quantityJson p.gasLimit.toNat),
    ("gasUsed", quantityJson p.gasUsed.toNat), ("timestamp", quantityJson p.timestamp.toNat),
    ("extraData", dataJson p.extraData.data.toList),
    ("baseFeePerGas", quantityJson p.baseFeePerGas.toNat),
    ("blockHash", dataJson p.blockHash.toList),
    ("transactions", listJson (dataJson ·.data.toList) p.transactions)] ++
  -- From Shapella, the `withdrawals` of `ExecutionPayloadV2`.
  (if h : .shapella ≤ fork then [("withdrawals", listJson withdrawalJson (p.withdrawals h))]
    else []) ++
  -- From Dencun, the two blob gas fields of `ExecutionPayloadV3`.
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
  -- `ExecutionPayloadV4` appends `blockAccessList` and `slotNumber`.
  Json.mkObj (executionPayloadFields p ++
    [("blockAccessList", dataJson blockAccessList.data.toList),
      ("slotNumber", quantityJson slotNumber.toNat)])

/-! ## Payload statuses -/

/-- The status whose name the Engine API writes, or none for any other text. -/
def statusOfName (name : String) : Option Status :=
  -- `PayloadStatusV1`: `status` is one of five names.
  [Status.valid, .invalid, .syncing, .accepted, .invalidBlockHash].find? (·.name == name)

/-- The three members of a payload status, with `null` for an absent hash or error. -/
def payloadStatusPairs (s : PayloadStatus) (validationError : Option String) :
    List (String × Json) :=
  -- `PayloadStatusV1`: `status`, an enum.
  [("status", .str s.status.name),
    -- `latestValidHash`: `DATA|null`, 32 bytes.
    ("latestValidHash", optionJson (dataJson ·.toList) s.latestValidHash),
    -- `validationError`: `String|null`.
    ("validationError", optionJson .str validationError)]

/-- A payload status as JSON, with its three fields: `PayloadStatusV1` of [`paris.md`][status].

By step 5 of [payload validation][validation], a client may give the text of the validation error.

That step gives it for an invalid payload, and the writer leaves the pairing to its caller.

[status]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payloadstatusv1
[validation]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payload-validation -/
def payloadStatusJson (s : PayloadStatus) (validationError : Option String) : Json :=
  Json.mkObj (payloadStatusPairs s validationError)

/-- The three fields that a payload status may hold. -/
def payloadStatusFields : List String := ["status", "latestValidHash", "validationError"]

/-- A payload status, with its validation error, as `PayloadStatusV1` of [`paris.md`][status].

The OpenRPC schema `PayloadStatusV1` in [`payload.yaml`][schema] requires only the status.

The decoder checks the form only, not which hash or error goes with which status.

[status]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payloadstatusv1
[schema]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/openrpc/schemas/payload.yaml -/
def payloadStatusOfJson (j : Json) : Decode (PayloadStatus × Option String) := do
  -- A status that does not decode is `-32602`, invalid params, as for a request.
  --
  -- As for the parameters, a field whose value is `null` counts as absent.
  let fs ← fields "payloadStatus" j
  -- Not in the schema: any other field with a value other than `null` is invalid.
  --
  -- That rule is stricter than the schema states.
  unless fs.all (payloadStatusFields.contains ·.1) do invalid "payloadStatus: unknown field"
  -- `status`: one of the five names of the enum, and the one field that the schema requires.
  let name ← string "status" (← field "payloadStatus" fs "status")
  let some status := statusOfName name | invalid s!"payloadStatus: no status {name}"
  -- `latestValidHash`: `DATA|null`, 32 bytes.
  let latestValidHash ← lift ((fs.lookup "latestValidHash").mapM (fixed "latestValidHash" 32))
  -- `validationError`: `String|null`.
  let validationError ← lift ((fs.lookup "validationError").mapM (string "validationError"))
  return (⟨status, latestValidHash⟩, validationError)

/-! ## Bogota -/

/-- A payload status of version 2 as JSON: the three fields of version 1, then one more.

That field says whether the payload satisfies its inclusion list, as a boolean or `null`.

`PayloadStatusV2` of [`bogota.md`][status] asks for `null` unless the status is valid.

Its status is never an invalid block hash.

The writer leaves both rules to its caller.

[status]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#payloadstatusv2 -/
def payloadStatusV2Json (s : PayloadStatus) (validationError : Option String)
    (inclusionListSatisfied : Option Bool) : Json :=
  Json.mkObj (payloadStatusPairs s validationError ++
    -- `PayloadStatusV2` appends `inclusionListSatisfied`, `BOOLEAN|null`.
    [("inclusionListSatisfied", optionJson .bool inclusionListSatisfied)])

/-- A payload status of version 2, with its validation error and its inclusion list verdict.

As for version 1, the decoder checks the form only, not which verdict goes with which status. -/
def payloadStatusV2OfJson (j : Json) :
    Decode (PayloadStatus × Option String × Option Bool) := do
  let fs ← fields "payloadStatus" j
  -- `inclusionListSatisfied`: `BOOLEAN|null`, and a `null` or absent verdict reads as none.
  let satisfied ← lift ((fs.lookup "inclusionListSatisfied").mapM (bool "inclusionListSatisfied"))
  -- `PayloadStatusV2` has the syntax of `PayloadStatusV1` for its other members.
  let (s, e) ← payloadStatusOfJson
    (Json.mkObj (fs.filter fun (name, _) => name != "inclusionListSatisfied"))
  -- Its `status` is `VALID`, `INVALID`, `SYNCING` or `ACCEPTED`, never `INVALID_BLOCK_HASH`.
  if s.status = .invalidBlockHash then invalid "payloadStatus: not a status of version 2"
  return (s, e, satisfied)

/-- The transactions of an inclusion list as JSON: an array of byte strings. -/
def inclusionListJson (transactions : List ByteArray) : Json :=
  listJson (dataJson ·.data.toList) transactions

/-- The transactions of an inclusion list: an array of byte strings.

Each entry may be any byte string, by [`bogota.md`][bogota].

[bogota]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#engine_newpayloadv6 -/
def inclusionListOfJson (j : Json) : Read (List ByteArray) :=
  -- `engine_newPayloadV6`, parameter 5: an `Array of DATA`, each entry a byte list.
  --
  -- Step 4: an entry that is no valid transaction still reads, and the method must tolerate it.
  array "inclusionListTransactions" (bytes "inclusionListTransaction") j

end EthLib.Engine.Json

namespace EthLib.Engine

open EthLib.Base

/-- The value of a field from fork `f`, if the fork has the field. -/
def sinceValue {fork : Fork} {α : Type} {f : Fork} (x : Since f fork α) : Option α :=
  if h : f ≤ fork then some (x h) else none

/-- A request for more items than the node takes at once is too large. -/
def checkRequestSize (maxRequest count : Nat) : Except EngineError Unit :=
  -- `-38004`, too large request: the number of requested entities is too large.
  if maxRequest < count then throw (.tooLargeRequest count maxRequest) else pure ()

/-! ## Errors -/

/-- The message of an error, from the table of [Errors][errors] in `common.md`.

The execution API gives `-32000` another message, so each API keeps its own table.

[errors]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#errors -/
def EngineError.message : EngineError → String
  -- `-32602`: invalid method parameters.
  | .invalidParams _ => "Invalid params"
  -- `-38005`: the payload belongs to a fork that is not supported.
  | .unsupportedFork _ => "Unsupported fork"
  -- `-38002`: the forkchoice state is invalid or inconsistent.
  | .invalidForkchoiceState .. => "Invalid forkchoice state"
  -- `-38004`: the number of requested entities is too large.
  | .tooLargeRequest .. => "Too large request"
  -- `-38003`: the payload attributes are invalid or inconsistent.
  | .invalidPayloadAttributes => "Invalid payload attributes"
  -- `-38001`: the payload does not exist or is not available.
  | .unknownPayload _ => "Unknown payload"
  -- `-38006`: the depth of the reorganization exceeds the limit.
  | .tooDeepReorg => "Too deep reorg"

/-- The error object of an error: the negative of its code, its message, and `null` data. -/
def EngineError.toRpcError (e : EngineError) : Serialization.JsonRpc.RpcError :=
  -- Errors: each error returns a `null` data value, except `-32000`, which no Engine error has.
  --
  -- So the reason of invalid parameters is dropped.
  --
  -- The shared JSON-RPC error keeps it as data.
  { code := -(e.code.toNat : Int), message := e.message, data := some .null }

end EthLib.Engine
