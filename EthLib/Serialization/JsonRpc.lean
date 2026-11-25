module

public import Lean.Data.Json
public import EthLib.Base.Address
public import EthLib.Base.Hex

/-!
# `Serialization.JsonRpc`

The JSON form of the base types that the Engine API and the execution JSON-RPC API share.

Sources:

- [`base-types.yaml`][types], at commit `1ca0818` of execution-apis: the patterns the steps quote
- step 1 of [`engine_newPayloadV3`][v3], at the same commit: the rules of the object readers
- section 4.2 of [JSON-RPC 2.0][params]: the parameters of a request
- section 5.1 of [JSON-RPC 2.0][rpc]: the error object of a failed request

[v3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#specification
[params]: https://www.jsonrpc.org/specification#parameter_structures
[rpc]: https://www.jsonrpc.org/specification#error_object
[types]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/base-types.yaml
-/

@[expose] public section

namespace EthLib.Serialization.JsonRpc

open Lean (Json)
open EthLib.Base

/-- A reading that fails with a reason, given as a string.

A caller turns that reason into its own error, such as an invalid parameter of the Engine API. -/
abbrev Read := Except String

/-- Reject the input, for a reason. -/
def reject {α : Type} (reason : String) : Read α := throw reason

/-- The value of a hex digit, given as its ASCII byte; uppercase only when `upper` allows it. -/
def hexValue (upper : Bool) (c : UInt8) : Option UInt8 :=
  -- The base types: the digits `0-9` and `a-f`, and `A-F` only in the address pattern.
  Base.hexValue? (Char.ofUInt8 c) upper

/-- The ASCII bytes of a JSON string after its `0x` marker. -/
def hexDigits (what : String) : Json → Read ByteArray
  | .str s =>
    let b := s.toUTF8
    -- Every hex base type is a string that starts with `0x`.
    if b[0]? = some 48 ∧ b[1]? = some 120 then pure (b.extract 2 b.size)
    else reject s!"{what}: no 0x marker"
  | _ => reject s!"{what}: not a string"

/-- The bytes of a byte string, with uppercase digits only when `upper` allows them. -/
def bytesOf (what : String) (upper : Bool) (j : Json) : Read ByteArray := do
  let digits ← hexDigits what j
  -- bytes: `^0x[0-9a-f]*$`, with `A-F` also allowed for an address.
  --
  -- EthLib also refuses an odd count of digits, which the pattern admits but no byte string has.
  if digits.size % 2 ≠ 0 then reject s!"{what}: odd number of hex digits" else
  let chars := digits.data.toList.map Char.ofUInt8
  -- Where the pattern refuses `A-F`, any uppercase letter is not a hex digit.
  if !upper && chars.any Char.isUpper then reject s!"{what}: not a hex digit" else
  -- Byte `i` is `16 * d_(2i) + d_(2i+1)`, the high digit first, as Base reads hex.
  match Base.hexBytes? chars with
  | some out => pure out
  | none => reject s!"{what}: not a hex digit"

/-- A byte string of any length. -/
def bytes (what : String) (j : Json) : Read ByteArray := bytesOf what false j

/-- A byte string of exactly `n` bytes. -/
def fixed (what : String) (n : Nat) (j : Json) (upper : Bool := false) :
    Read (Vector UInt8 n) := do
  -- bytesN and hash32: exactly `n` bytes, `2n` digits, as `^0x[0-9a-f]{2n}$` asks.
  --
  -- An address allows `A-F` as well.
  exactBytes n (← bytesOf what upper j) fun size => s!"{what}: {size} bytes, not {n}"

/-- An address of 20 bytes, whose hex digits may be uppercase, as `^0x[0-9a-fA-F]{40}$` allows. -/
def address (what : String) (j : Json) : Read Address := fixed what 20 j (upper := true)

/-- A number of any size, without leading zeros. -/
def uint (what : String) (j : Json) : Read Nat := do
  let digits ← hexDigits what j
  -- uint: `^0x(0|[1-9a-f][0-9a-f]*)$`, so at least one digit, and `0` leads only in `0x0`.
  if digits.size = 0 then reject s!"{what}: no digits" else
  if digits.size > 1 ∧ digits[0]? = some 48 then reject s!"{what}: leading zero" else
  let mut value := 0
  -- The digits are read high first: `v = 16 v + d` for each lowercase digit `d`.
  for c in digits do
    match hexValue false c with
    | some d => value := 16 * value + d.toNat
    | none => reject s!"{what}: not a hex digit"
  return value

/-- A number below `2^bits`, without leading zeros. -/
def quantity (what : String) (bits : Nat) (j : Json) : Read Nat := do
  let value ← uint what j
  -- uint32, uint64 and uint256: the uint pattern with at most `bits / 4` digits.
  --
  -- Without leading zeros, that is a value below `2^bits`.
  if value < 2 ^ bits then pure value else reject s!"{what}: above 2^{bits}"

/-- A byte string of at most `n` bytes. -/
def bytesMax (what : String) (n : Nat) (j : Json) : Read ByteArray := do
  let b ← bytes what j
  -- bytesMax32: `^0x[0-9a-f]{0,64}$`, at most 32 bytes; here at most `n`.
  if b.size ≤ n then pure b else reject s!"{what}: {b.size} bytes, more than {n}"

/-- A 64-bit number. -/
def uint64 (what : String) (j : Json) : Read UInt64 :=
  return (← quantity what 64 j).toUInt64

/-- The parameters of a request, which must be a JSON array. -/
def paramsArray : Json → Read (List Json)
  -- JSON-RPC 2.0, section 4.2, by-position: params MUST be an Array.
  --
  -- EthLib reads the parameters by position only, and refuses the by-name form.
  --
  -- It also refuses absent params, which section 4.2 allows.
  | .arr items => pure items.toList
  | _ => reject "params: not an array"

/-- A list of values, each read by `f`. -/
def array {α : Type} (what : String) (f : Json → Read α) : Json → Read (List α)
  | .arr items => items.toList.mapM f
  | _ => reject s!"{what}: not an array"

/-- A value read by the given reader, or no value for `null`. -/
def nullable {α : Type} (f : Json → Read α) : Json → Read (Option α)
  -- A null value stands for no value.
  | .null => pure none
  | j => some <$> f j

/-- The fields of an object with a value other than `null`, by name. -/
def fields (what : String) : Json → Read (List (String × Json))
  -- Step 1 of `engine_newPayloadV3`: a field with the value null counts as not provided.
  | .obj kvs => pure (kvs.toList.filter fun (_, v) => !v.isNull)
  | _ => reject s!"{what}: not an object"

/-- Whether a list of fields holds exactly the named fields. -/
def hasExactly (fs : List (String × Json)) (names : List String) : Bool :=
  -- Step 1 of `engine_newPayloadV3`: the fields strictly match the expected ones.
  --
  -- The names of an object and the expected names are each distinct.
  --
  -- So the same count and every expected name present suffice.
  fs.length == names.length && names.all fun name => fs.any (·.1 == name)

/-- Whether each of a list of fields has one of the names. -/
def hasOnly (fs : List (String × Json)) (names : List String) : Bool :=
  fs.all fun (name, _) => names.contains name

/-- The value of a field that an object holds. -/
def field (what : String) (fs : List (String × Json)) (name : String) : Read Json :=
  match fs.lookup name with
  | some v => pure v
  | none => reject s!"{what}: no field {name}"

/-- Bytes as data: `0x`, then two hex digits per byte. -/
def dataJson (bytes : List UInt8) : Json :=
  -- bytes: `0x`, then two lowercase digits per byte, the canonical form of the pattern.
  .str (hexString bytes)

/-- The JSON of a value, or `null`. -/
def optionJson {α : Type} (f : α → Json) : Option α → Json
  | some a => f a
  | none => .null

/-- The JSON of a list. -/
def listJson {α : Type} (f : α → Json) (items : List α) : Json := .arr (items.toArray.map f)

/-- A number as a quantity: `0x`, then its hex digits without leading zeros. -/
def quantityJson (n : Nat) : Json :=
  -- uint: `0x`, then lowercase digits without leading zeros, and `0x0` for zero.
  .str ("0x" ++ String.ofList (Nat.toDigits 16 n))

/-! ## The error object -/

/-- An integer: a JSON number whose value is an integer, such as `-32602`, `1e3` or `1.0`. -/
def integer (what : String) : Json → Read Int
  -- JSON-RPC 2.0, section 5.1: the code MUST be an integer.
  --
  -- A JSON number `m * 10^(-e)` is one when `10^e` divides `m`.
  | .num ⟨m, e⟩ =>
    if m % 10 ^ e = 0 then pure (m / 10 ^ e) else reject s!"{what}: not an integer"
  | _ => reject s!"{what}: not an integer"

/-- A JSON boolean. -/
def bool (what : String) : Json → Read Bool
  | .bool b => pure b
  | _ => reject s!"{what}: not a boolean"

/-- A JSON string. -/
def string (what : String) : Json → Read String
  | .str s => pure s
  | _ => reject s!"{what}: not a string"

/-- The error object of a JSON-RPC response.

It holds an integer code, a message, and optional data.

Section 5.1 of [JSON-RPC 2.0][rpc] defines it.

[rpc]: https://www.jsonrpc.org/specification#error_object -/
structure RpcError where
  -- JSON-RPC 2.0 reserves the codes from `-32768` to `-32000`.
  --
  -- Each API keeps its own table of the rest.
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

/-- The error of an invalid request object, code `-32600`, with the reason as its data.

The code and the message are those of section 5.1 of [JSON-RPC 2.0][rpc].

The error groups of the execution API write the message with a lowercase `r`.

[rpc]: https://www.jsonrpc.org/specification#error_object -/
def RpcError.invalidRequest (reason : String) : RpcError :=
  { code := -32600, message := "Invalid Request", data := some (.str reason) }

/-- The error object as JSON: the code, the message, and the data when it has some. -/
def rpcErrorJson (e : RpcError) : Json :=
  -- Section 5.1: the members code and message, then data, which may be omitted.
  Json.mkObj ([("code", .num (.fromInt e.code)), ("message", .str e.message)] ++
    match e.data with
    | some d => [("data", d)]
    | none => [])

/-- An error object: a code, a message and optional data, as in section 5.1 of [JSON-RPC 2.0][rpc].

[rpc]: https://www.jsonrpc.org/specification#error_object -/
def rpcErrorOfJson : Json → Read RpcError
  | .obj kvs => do
    let members := kvs.toList
    -- EthLib's own rule: no member besides code, message and data, which section 5.1 lists.
    unless members.all fun (name, _) => name == "code" || name == "message" || name == "data" do
      reject "error: a member other than code, message and data"
    -- Section 5.1: code, a Number that MUST be an integer.
    let code ← integer "code" (← field "error" members "code")
    -- Section 5.1: message, a String.
    let message ← string "message" (← field "error" members "message")
    -- Section 5.1: data, a Primitive or Structured value that may be omitted.
    --
    -- A data member set to null holds the value null, so it is kept rather than dropped.
    return ⟨code, message, members.lookup "data"⟩
  | _ => reject "error: not an object"

end EthLib.Serialization.JsonRpc
