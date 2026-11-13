module

public import Lean.Data.Json
public import EthLib.Base.Hex
public import EthLib.Serialization.JsonRpc
public import EthLib.Execution.Rpc.Json
public import EthLib.Engine.Payload

/-!
# `Engine.Json`

The JSON form of the parameters of the Engine API.

The Engine API is a JSON-RPC interface, with the encodings of the Ethereum JSON-RPC API.

This module reads the base types with readers that the execution JSON-RPC API shares.

An input that such a reader rejects is an invalid parameter, with JSON-RPC code `-32602`.

The base types state the patterns in [`base-types.yaml`][types].

So the extra data of a payload has at most 32 bytes, as its type `bytesMax32` says.

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
open EthLib.Execution.Rpc (withdrawal)
open EthLib.Execution.Blocks (Withdrawal)

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
    extraData := ← bytesMax "extraData" 32 (← get "extraData")
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

end EthLib.Engine.Json

namespace EthLib.Engine

open EthLib.Base

/-- The value of a field from fork `f`, if the fork has the field. -/
def sinceValue {fork : Fork} {α : Type} {f : Fork} (x : Since f fork α) : Option α :=
  if h : f ≤ fork then some (x h) else none

/-- A request for more items than the node takes at once is too large. -/
def checkRequestSize (maxRequest count : Nat) : Except EngineError Unit :=
  if maxRequest < count then throw .tooLargeRequest else pure ()

end EthLib.Engine
