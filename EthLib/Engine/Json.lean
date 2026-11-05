module

public import Lean.Data.Json
public import EthLib.Engine.Payload

/-!
# `Engine.Json`

The JSON form of the parameters of the Engine API.

The Engine API is a JSON-RPC interface, with the encodings of the Ethereum JSON-RPC API.

A byte string is lowercase hex behind `0x`, two digits for each byte.

An address may also use uppercase digits.

A number is lowercase hex behind `0x`, without leading zeros, and `0x0` for zero.

An object must hold exactly the fields of its structure.

A field whose value is `null` counts as absent.

Any other input is an invalid parameter, with JSON-RPC code `-32602`.

The base types state the patterns in [`base-types.yaml`][types].

So the extra data of a payload has at most 32 bytes, as its type `bytesMax32` says.

Step 1 of [`engine_newPayloadV3`][v3] asks for exactly the expected fields, with `null` as absent.

[types]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/base-types.yaml
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#specification
-/

@[expose] public section

namespace EthLib.Engine.Json

open Lean (Json)
open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)

/-- A decoding that fails with an invalid parameter. -/
abbrev Decode := Except EngineError

/-- Fail with an invalid parameter, for a reason. -/
def invalid {α : Type} (reason : String) : Decode α := throw (.invalidParams reason)

/-- The value of a hex digit, given as its ASCII byte; uppercase only when `upper` allows it. -/
def hexValue (upper : Bool) (c : UInt8) : Option UInt8 :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if upper ∧ 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- The ASCII bytes of a JSON string after its `0x` marker. -/
def hexDigits (what : String) : Json → Decode ByteArray
  | .str s =>
    let b := s.toUTF8
    if b.size ≥ 2 ∧ b[0]! = 48 ∧ b[1]! = 120 then pure (b.extract 2 b.size)
    else invalid s!"{what}: no 0x marker"
  | _ => invalid s!"{what}: not a string"

/-- The bytes of a byte string, with uppercase digits only when `upper` allows them. -/
def bytesOf (what : String) (upper : Bool) (j : Json) : Decode ByteArray := do
  let digits ← hexDigits what j
  if digits.size % 2 ≠ 0 then invalid s!"{what}: odd number of hex digits" else
  let mut out := ByteArray.emptyWithCapacity (digits.size / 2)
  for i in [0:digits.size / 2] do
    match hexValue upper digits[2 * i]!, hexValue upper digits[2 * i + 1]! with
    | some high, some low => out := out.push (16 * high + low)
    | _, _ => invalid s!"{what}: not a hex digit"
  return out

/-- A byte string of any length. -/
def bytes (what : String) (j : Json) : Decode ByteArray := bytesOf what false j

/-- A byte string of exactly `n` bytes. -/
def fixed (what : String) (n : Nat) (j : Json) (upper : Bool := false) :
    Decode (Vector UInt8 n) := do
  let b ← bytesOf what upper j
  if h : b.data.size = n then pure ⟨b.data, h⟩
  else invalid s!"{what}: {b.size} bytes, not {n}"

/-- An address of 20 bytes, whose hex digits may be uppercase. -/
def address (what : String) (j : Json) : Decode Address := fixed what 20 j (upper := true)

/-- A number below `2^bits`, without leading zeros. -/
def quantity (what : String) (bits : Nat) (j : Json) : Decode Nat := do
  let digits ← hexDigits what j
  if digits.size = 0 then invalid s!"{what}: no digits" else
  if digits.size > 1 ∧ digits[0]! = 48 then invalid s!"{what}: leading zero" else
  let mut value := 0
  for i in [0:digits.size] do
    match hexValue false digits[i]! with
    | some d => value := 16 * value + d.toNat
    | none => invalid s!"{what}: not a hex digit"
  if value < 2 ^ bits then pure value else invalid s!"{what}: above 2^{bits}"

/-- A byte string of at most `n` bytes. -/
def bytesMax (what : String) (n : Nat) (j : Json) : Decode ByteArray := do
  let b ← bytes what j
  if b.size ≤ n then pure b else invalid s!"{what}: {b.size} bytes, more than {n}"

/-- A 64-bit number. -/
def uint64 (what : String) (j : Json) : Decode UInt64 :=
  return (← quantity what 64 j).toUInt64

/-- A list of values, each decoded by `f`. -/
def array {α : Type} (what : String) (f : Json → Decode α) : Json → Decode (List α)
  | .arr items => items.toList.mapM f
  | _ => invalid s!"{what}: not an array"

/-- The fields of an object with a value other than `null`, by name. -/
def fields (what : String) : Json → Decode (List (String × Json))
  | .obj kvs => pure (kvs.toList.filter fun (_, v) => v != .null)
  | _ => invalid s!"{what}: not an object"

/-- Whether an object has exactly the named fields, ignoring those whose value is `null`. -/
def hasExactly (fs : List (String × Json)) (names : List String) : Bool :=
  fs.length == names.length && names.all fun name => fs.any (·.1 == name)

/-- The value of a field that an object holds. -/
def field (what : String) (fs : List (String × Json)) (name : String) : Decode Json :=
  match fs.lookup name with
  | some v => pure v
  | none => invalid s!"{what}: no field {name}"

/-- A withdrawal, with exactly its four fields. -/
def withdrawal (j : Json) : Decode Withdrawal := do
  let fs ← fields "withdrawal" j
  unless hasExactly fs ["index", "validatorIndex", "address", "amount"] do
    invalid "withdrawal: wrong fields"
  return {
    index := ← uint64 "index" (← field "withdrawal" fs "index")
    validatorIndex := ← uint64 "validatorIndex" (← field "withdrawal" fs "validatorIndex")
    address := ← address "address" (← field "withdrawal" fs "address")
    amount := ← uint64 "amount" (← field "withdrawal" fs "amount") }

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
