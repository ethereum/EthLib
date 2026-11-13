module

public import Lean.Data.Json
public import EthLib.Base.Address
public import EthLib.Base.Hex

/-!
# `Serialization.JsonRpc`

The JSON form of the base types that the Ethereum JSON-RPC APIs exchange.

The Engine API and the execution JSON-RPC API share these types.

A byte string is lowercase hex behind `0x`, two digits for each byte.

An address may also use uppercase digits.

A number is lowercase hex behind `0x`, without leading zeros, and `0x0` for zero.

The base types state the patterns in [`base-types.yaml`][types].

Object readers require exactly the named fields, as step 1 of [`engine_newPayloadV3`][v3] asks.

They count a field whose value is `null` as absent, as that step also asks.

A reader that rejects its input gives the reason as a string.

A caller turns that reason into its own error, such as an invalid parameter of the Engine API.

The writers write the canonical form: lowercase hex, and numbers without leading zeros.

A failed request answers with an error object of [JSON-RPC 2.0][rpc]: a code, a message and data.

Its data is optional, and a member `data` set to `null` holds the data `null`.

JSON-RPC 2.0 reserves the codes from `-32768` to `-32000`; each API keeps its own table of the rest.

[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#specification
[rpc]: https://www.jsonrpc.org/specification#error_object
[types]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/base-types.yaml
-/

@[expose] public section

namespace EthLib.Serialization.JsonRpc

open Lean (Json)
open EthLib.Base

/-- A reading that fails with a reason. -/
abbrev Read := Except String

/-- Reject the input, for a reason. -/
def reject {α : Type} (reason : String) : Read α := throw reason

/-- The value of a hex digit, given as its ASCII byte; uppercase only when `upper` allows it. -/
def hexValue (upper : Bool) (c : UInt8) : Option UInt8 :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if upper ∧ 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- The ASCII bytes of a JSON string after its `0x` marker. -/
def hexDigits (what : String) : Json → Read ByteArray
  | .str s =>
    let b := s.toUTF8
    if b[0]? = some 48 ∧ b[1]? = some 120 then pure (b.extract 2 b.size)
    else reject s!"{what}: no 0x marker"
  | _ => reject s!"{what}: not a string"

/-- The bytes of a byte string, with uppercase digits only when `upper` allows them. -/
def bytesOf (what : String) (upper : Bool) (j : Json) : Read ByteArray := do
  let digits ← hexDigits what j
  if digits.size % 2 ≠ 0 then reject s!"{what}: odd number of hex digits" else
  let mut out := ByteArray.emptyWithCapacity (digits.size / 2)
  for i in [0:digits.size / 2] do
    match digits[2 * i]?, digits[2 * i + 1]? with
    | some c, some d =>
      match hexValue upper c, hexValue upper d with
      | some high, some low => out := out.push (16 * high + low)
      | _, _ => reject s!"{what}: not a hex digit"
    -- The count is even, so both digits of each byte exist and this case never happens.
    | _, _ => reject s!"{what}: odd number of hex digits"
  return out

/-- A byte string of any length. -/
def bytes (what : String) (j : Json) : Read ByteArray := bytesOf what false j

/-- A byte string of exactly `n` bytes. -/
def fixed (what : String) (n : Nat) (j : Json) (upper : Bool := false) :
    Read (Vector UInt8 n) := do
  let b ← bytesOf what upper j
  if h : b.data.size = n then pure ⟨b.data, h⟩
  else reject s!"{what}: {b.size} bytes, not {n}"

/-- An address of 20 bytes, whose hex digits may be uppercase. -/
def address (what : String) (j : Json) : Read Address := fixed what 20 j (upper := true)

/-- A number below `2^bits`, without leading zeros. -/
def quantity (what : String) (bits : Nat) (j : Json) : Read Nat := do
  let digits ← hexDigits what j
  if digits.size = 0 then reject s!"{what}: no digits" else
  if digits.size > 1 ∧ digits[0]? = some 48 then reject s!"{what}: leading zero" else
  let mut value := 0
  for c in digits do
    match hexValue false c with
    | some d => value := 16 * value + d.toNat
    | none => reject s!"{what}: not a hex digit"
  if value < 2 ^ bits then pure value else reject s!"{what}: above 2^{bits}"

/-- A byte string of at most `n` bytes. -/
def bytesMax (what : String) (n : Nat) (j : Json) : Read ByteArray := do
  let b ← bytes what j
  if b.size ≤ n then pure b else reject s!"{what}: {b.size} bytes, more than {n}"

/-- A 64-bit number. -/
def uint64 (what : String) (j : Json) : Read UInt64 :=
  return (← quantity what 64 j).toUInt64

/-- The parameters of a request, which must be a JSON array. -/
def paramsArray : Json → Read (List Json)
  | .arr items => pure items.toList
  | _ => reject "params: not an array"

/-- A list of values, each read by `f`. -/
def array {α : Type} (what : String) (f : Json → Read α) : Json → Read (List α)
  | .arr items => items.toList.mapM f
  | _ => reject s!"{what}: not an array"

/-- The fields of an object with a value other than `null`, by name. -/
def fields (what : String) : Json → Read (List (String × Json))
  | .obj kvs => pure (kvs.toList.filter fun (_, v) => !v.isNull)
  | _ => reject s!"{what}: not an object"

/-- Whether a list of fields holds exactly the named fields. -/
def hasExactly (fs : List (String × Json)) (names : List String) : Bool :=
  fs.length == names.length && names.all fun name => fs.any (·.1 == name)

/-- The value of a field that an object holds. -/
def field (what : String) (fs : List (String × Json)) (name : String) : Read Json :=
  match fs.lookup name with
  | some v => pure v
  | none => reject s!"{what}: no field {name}"

/-- Bytes as data: `0x`, then two hex digits per byte. -/
def dataJson (bytes : List UInt8) : Json :=
  .str (hexString bytes)

/-- The JSON of a value, or `null`. -/
def optionJson {α : Type} (f : α → Json) : Option α → Json
  | some a => f a
  | none => .null

/-- The JSON of a list. -/
def listJson {α : Type} (f : α → Json) (items : List α) : Json := .arr (items.toArray.map f)

/-- A number as a quantity: `0x`, then its hex digits without leading zeros. -/
def quantityJson (n : Nat) : Json :=
  .str ("0x" ++ String.ofList (Nat.toDigits 16 n))

/-! ## The error object -/

/-- An integer: a JSON number whose value is an integer, such as `-32602`, `1e3` or `1.0`. -/
def integer (what : String) : Json → Read Int
  | .num ⟨m, e⟩ =>
    if m % 10 ^ e = 0 then pure (m / 10 ^ e) else reject s!"{what}: not an integer"
  | _ => reject s!"{what}: not an integer"

/-- A JSON string. -/
def string (what : String) : Json → Read String
  | .str s => pure s
  | _ => reject s!"{what}: not a string"

/-- The error object of a JSON-RPC response.

It holds an integer code, a message, and optional data.

Section 5.1 of [JSON-RPC 2.0][rpc] defines it.

[rpc]: https://www.jsonrpc.org/specification#error_object -/
structure RpcError where
  /-- The code: the kind of the error. -/
  code : Int
  /-- A short description of the error. -/
  message : String
  /-- More about the error, absent when the error has nothing to add. -/
  data : Option Json := none

/-- The error of invalid parameters, code `-32602`, with the reason as its data.

The code and the message are those of section 5.1 of [JSON-RPC 2.0][rpc].

[rpc]: https://www.jsonrpc.org/specification#error_object -/
def RpcError.invalidParams (reason : String) : RpcError :=
  { code := -32602, message := "Invalid params", data := some (.str reason) }

/-- The error object as JSON: the code, the message, and the data when it has some. -/
def rpcErrorJson (e : RpcError) : Json :=
  Json.mkObj ([("code", .num (.fromInt e.code)), ("message", .str e.message)] ++
    match e.data with
    | some d => [("data", d)]
    | none => [])

/-- An error object: a code, a message and optional data.

It rejects any other member, a stricter rule than section 5.1 of [JSON-RPC 2.0][rpc] states.

A member `data` set to `null` reads as the data `null`, not as absent data.

[rpc]: https://www.jsonrpc.org/specification#error_object -/
def rpcErrorOfJson : Json → Read RpcError
  | .obj kvs => do
    let members := kvs.toList
    unless members.all fun (name, _) => name == "code" || name == "message" || name == "data" do
      reject "error: a member other than code, message and data"
    let code ← integer "code" (← field "error" members "code")
    let message ← string "message" (← field "error" members "message")
    return ⟨code, message, members.lookup "data"⟩
  | _ => reject "error: not an object"

end EthLib.Serialization.JsonRpc
