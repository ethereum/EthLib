module

public import EthLib.Base.U256
public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: basic types and fixed bytes

Booleans, the unsigned integers and fixed byte vectors, as their Lean types.

An integer type holds exactly the range of its SSZ type, so no value is truncated.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

namespace SszType

/--
An unsigned integer of a byte width, read back as a typed value.

A number outside the width names no value, so it is refused rather than wrapped.
-/
def ofUint {α : Type} (width : Nat) (make : Nat → α) : Value → Except Err α
  | .uint n =>
    if n < 2 ^ (8 * width) then .ok (make n) else .error (.uintRange (2 ^ (8 * width)) n)
  | _ => .error .typeMismatch

/--
An unsigned integer of a byte width, read straight from its bytes.

The bytes must be exactly the width, as the untyped decoder asks.
-/
def decodeUint {α : Type} (width : Nat) (make : Nat → α) (data : ByteArray) : Except Err α :=
  if data.size != width then .error (.scope width data.size)
  else .ok (make (readUintBytes data 0 width))

/-- The bytes so far, then the `width` little-endian bytes of `n`, its lowest byte first. -/
def pushUintBytes : (width n : Nat) → ByteArray → ByteArray
  | 0, _, out => out
  | width + 1, n, out => pushUintBytes width (n / 256) (out.push (UInt8.ofNat n))

/--
The `width` little-endian bytes of `n`, written straight into a byte array.

A number past the width loses its high bytes.

A typed value always fits its width, so its bytes are those of the untyped encoder.
-/
def encodeUint (width n : Nat) : Except Err ByteArray :=
  .ok (pushUintBytes width n (ByteArray.emptyWithCapacity width))

end SszType

open SszType

instance : SszType Bool where
  desc := .bool
  toValue := .bool
  ofValue
    | .bool b => .ok b
    | _ => .error .typeMismatch
  decode data := do
    if data.size != 1 then throw (.scope 1 data.size)
    match data[0]?.getD 0 with
    | 0 => return false
    | 1 => return true
    | byte => throw (.notABit byte.toNat)

/-- `uint8`. -/
instance : SszType UInt8 where
  desc := Desc.uint8
  toValue a := .uint a.toNat
  ofValue := ofUint 1 UInt8.ofNat
  encode a := encodeUint 1 a.toNat
  decode := decodeUint 1 UInt8.ofNat

/-- `uint16`. -/
instance : SszType UInt16 where
  desc := Desc.uint16
  toValue a := .uint a.toNat
  ofValue := ofUint 2 UInt16.ofNat
  encode a := encodeUint 2 a.toNat
  decode := decodeUint 2 UInt16.ofNat

/-- `uint32`. -/
instance : SszType UInt32 where
  desc := Desc.uint32
  toValue a := .uint a.toNat
  ofValue := ofUint 4 UInt32.ofNat
  encode a := encodeUint 4 a.toNat
  decode := decodeUint 4 UInt32.ofNat

/-- `uint64`. -/
instance : SszType UInt64 where
  desc := Desc.uint64
  toValue a := .uint a.toNat
  ofValue := ofUint 8 UInt64.ofNat
  encode a := encodeUint 8 a.toNat
  decode := decodeUint 8 UInt64.ofNat

/-- `uint128`, held as a `BitVec 128`, since Lean has no 128-bit machine integer. -/
instance : SszType (BitVec 128) where
  desc := Desc.uint128
  toValue a := .uint a.toNat
  ofValue := ofUint 16 (BitVec.ofNat 128)
  encode a := encodeUint 16 a.toNat
  decode := decodeUint 16 (BitVec.ofNat 128)

/-- `uint256`. -/
instance : SszType Base.U256 where
  desc := Desc.uint256
  toValue a := .uint a.toNat
  ofValue := ofUint 32 (BitVec.ofNat 256)
  encode a := encodeUint 32 a.toNat
  decode := decodeUint 32 (BitVec.ofNat 256)

/--
`ByteVector[n]`, the alias of `Vector[byte, n]`.

It takes precedence over a vector of `uint8` elements, which encodes and roots alike.
-/
instance (priority := high) {n : Nat} : SszType (Vector UInt8 n) where
  desc := .byteVector n
  toValue v := .bytes v.toArray
  ofValue
    | .bytes data =>
      if exact : data.size = n then .ok ⟨data, exact⟩ else .error (.count n data.size)
    | _ => .error .typeMismatch
  -- The bytes are the encoding; a length of `2^32` or more is refused, as for any byte sequence.
  encode v :=
    if n ≥ 2 ^ (8 * bytesPerOffset) then .error (.offsetOverflow n) else .ok ⟨v.toArray⟩

end EthLib.Serialization.Ssz
