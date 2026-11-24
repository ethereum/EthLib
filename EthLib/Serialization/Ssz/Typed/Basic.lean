module

public import EthLib.Base.U256
public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: basic types and fixed bytes

Booleans, the unsigned integers and fixed byte vectors, as their Lean types.

Each type roots as its untyped value, by the SSZ rule of a basic type or a byte vector.

The rules are stated in EthLib's own terms, one step per comment.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

namespace SszType

/-- An unsigned integer of a byte width, read back as a typed value. -/
def ofUint {α : Type} (width : Nat) (make : Nat → α) : Value → Except Err α
  -- uintN, with `N = 8 * width`, holds the integers `0 <= n < 2^N`, and no other.
  --
  -- An integer type holds exactly the range of its SSZ type, so no value is truncated.
  --
  -- A number outside the width names no value, so it is refused rather than wrapped.
  | .uint n =>
    if uintFits width n then .ok (make n) else .error (.uintRange (2 ^ (8 * width)) n)
  | _ => .error .typeMismatch

/-- An unsigned integer of a byte width, read straight from its bytes. -/
def decodeUint {α : Type} (width : Nat) (make : Nat → α) (data : ByteArray) : Except Err α :=
  -- uintN: exactly `N / 8` bytes, read little-endian as the sum of `b_i * 256^i`.
  --
  -- The bytes must be exactly the width, as the untyped decoder asks.
  if data.size != width then .error (.scope width data.size)
  else .ok (make (readUint data.data 0 width))

/-- The bytes so far, then the `width` little-endian bytes of `n`, its lowest byte first. -/
def pushUintBytes : (width n : Nat) → ByteArray → ByteArray
  | 0, _, out => out
  -- Byte `i` of the little-endian encoding is `floor(n / 256^i) mod 256`.
  | width + 1, n, out => pushUintBytes width (n / 256) (out.push (UInt8.ofNat n))

/-- The `width` little-endian bytes of `n`, written straight into a byte array. -/
def encodeUint (width n : Nat) : Except Err ByteArray :=
  -- uintN: `N / 8` bytes, little-endian, written into an array sized once.
  --
  -- A number past the width loses its high bytes.
  --
  -- A typed value always fits its width, so its bytes are those of the untyped encoder.
  .ok (pushUintBytes width n (ByteArray.emptyWithCapacity width))

end SszType

open SszType

instance : SszType Bool where
  desc := .bool
  toValue := .bool
  ofValue
    | .bool b => .ok b
    | _ => .error .typeMismatch
  -- boolean: exactly one byte, `0x00` for false or `0x01` for true; any other byte is refused.
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
    -- ByteVector[N]: exactly `N` bytes.
    | .bytes data => Base.exactArray n data (.count n)
    | _ => .error .typeMismatch
  -- ByteVector[N] serializes to its `N` bytes as they are.
  --
  -- Every SSZ sequence encodes to fewer than `2^32` bytes, since an offset has four bytes.
  --
  -- So a length `N >= 2^32` is refused.
  encode v :=
    if n ≥ 2 ^ (8 * bytesPerOffset) then .error (.offsetOverflow n) else .ok ⟨v.toArray⟩

end EthLib.Serialization.Ssz
