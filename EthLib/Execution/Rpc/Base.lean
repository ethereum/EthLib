module

public import EthLib.Serialization.JsonRpc
public import EthLib.Base.Hash32
public import EthLib.Base.U256

/-!
# `Execution.Rpc.Base`

The base types of the execution JSON-RPC API that the shared JSON-RPC readers do not define.

They are those of [`base-types.yaml`][types].

A `byte` is one or two lowercase hex digits behind `0x`, so `0x5` and `0x05` are both the byte 5.

Its writer writes the digits of the number, without a leading zero.

A `uint` is a number of any size, written as a quantity is.

A `uint32` and a `uint256` are quantities below `2^32` and `2^256`.

A `uintDecimal` is a number in decimal digits, without `0x` and without leading zeros.

A fixed byte string, such as `bytes4` or `hash32`, has exactly two lowercase digits per byte.

A `bytesMax32` has at most 64 lowercase digits, an odd count and leading zeros included.

A storage slot takes this type, and its digits write a number on 32 bytes.

The value `notFound` is the JSON `null`, which a method answers when it finds nothing.

A `ratio` is a JSON number from 0 to 1.

The source does not fix how many digits it has, so its writer takes that count as a parameter.

[types]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/base-types.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- A byte: one or two lowercase hex digits, where a leading zero is allowed. -/
def byte (what : String) (j : Json) : Read UInt8 := do
  let digits ← hexDigits what j
  if digits.size = 0 ∨ digits.size > 2 then reject s!"{what}: not one or two hex digits" else
  let mut value : UInt8 := 0
  for c in digits do
    match hexValue false c with
    | some d => value := 16 * value + d
    | none => reject s!"{what}: not a hex digit"
  return value

/-- A byte as JSON: the hex digits of its value, without a leading zero. -/
def byteJson (b : UInt8) : Json := quantityJson b.toNat

/-- A 32-bit number. -/
def uint32 (what : String) (j : Json) : Read UInt32 :=
  return (← quantity what 32 j).toUInt32

/-- A 256-bit number. -/
def uint256 (what : String) (j : Json) : Read U256 :=
  return BitVec.ofNat 256 (← quantity what 256 j)

/-- A number in decimal digits, without leading zeros. -/
def uintDecimal (what : String) : Json → Read Nat
  | .str s => do
    let digits := s.toUTF8
    if digits.size = 0 then reject s!"{what}: no digits" else
    if digits.size > 1 ∧ digits[0]? = some 48 then reject s!"{what}: leading zero" else
    let mut value := 0
    for c in digits do
      if 48 ≤ c ∧ c ≤ 57 then value := 10 * value + (c - 48).toNat
      else reject s!"{what}: not a decimal digit"
    return value
  | _ => reject s!"{what}: not a string"

/-- A number as JSON in decimal digits, without leading zeros. -/
def uintDecimalJson (n : Nat) : Json := .str (String.ofList (Nat.toDigits 10 n))

/-- The answer of a method that finds nothing: the JSON `null`. -/
def notFound : Json := .null

/-- The ratio `num / den` as a JSON number, rounded down to `places` decimal places.

A numerator above the denominator counts as the denominator, so the number lies from 0 to 1.

A denominator of 0 gives 0. -/
def ratioJson (places num den : Nat) : Json :=
  .num ⟨(min num den * 10 ^ places / den : Nat), places⟩

/-- Four bytes. -/
def bytes4 (what : String) (j : Json) : Read (Vector UInt8 4) := fixed what 4 j

/-- Eight bytes. -/
def bytes8 (what : String) (j : Json) : Read (Vector UInt8 8) := fixed what 8 j

/-- Sixteen bytes. -/
def bytes16 (what : String) (j : Json) : Read (Vector UInt8 16) := fixed what 16 j

/-- Thirty-two bytes. -/
def bytes32 (what : String) (j : Json) : Read (Vector UInt8 32) := fixed what 32 j

/-- Forty-eight bytes. -/
def bytes48 (what : String) (j : Json) : Read (Vector UInt8 48) := fixed what 48 j

/-- Sixty-five bytes. -/
def bytes65 (what : String) (j : Json) : Read (Vector UInt8 65) := fixed what 65 j

/-- Ninety-six bytes. -/
def bytes96 (what : String) (j : Json) : Read (Vector UInt8 96) := fixed what 96 j

/-- Two hundred and fifty-six bytes. -/
def bytes256 (what : String) (j : Json) : Read (Vector UInt8 256) := fixed what 256 j

/-- A storage slot: at most 64 lowercase hex digits, read as a number on 32 big-endian bytes. -/
def bytesMax32 (what : String) (j : Json) : Read Bytes32 := do
  let digits ← hexDigits what j
  if digits.size > 64 then reject s!"{what}: more than 64 hex digits" else
  let mut value := 0
  for c in digits do
    match hexValue false c with
    | some d => value := 16 * value + d.toNat
    | none => reject s!"{what}: not a hex digit"
  return Vector.ofFn fun i : Fin 32 => (value / 256 ^ (31 - i.val) % 256).toUInt8

/-- A hash of 32 bytes. -/
def hash32 (what : String) (j : Json) : Read Hash32 := fixed what 32 j

end EthLib.Execution.Rpc
