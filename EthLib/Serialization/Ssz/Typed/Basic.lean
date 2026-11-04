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

end SszType

open SszType

instance : SszType Bool where
  desc := .bool
  toValue := .bool
  ofValue
    | .bool b => .ok b
    | _ => .error .typeMismatch

/-- `uint8`. -/
instance : SszType UInt8 where
  desc := Desc.uint8
  toValue a := .uint a.toNat
  ofValue := ofUint 1 UInt8.ofNat

/-- `uint16`. -/
instance : SszType UInt16 where
  desc := Desc.uint16
  toValue a := .uint a.toNat
  ofValue := ofUint 2 UInt16.ofNat

/-- `uint32`. -/
instance : SszType UInt32 where
  desc := Desc.uint32
  toValue a := .uint a.toNat
  ofValue := ofUint 4 UInt32.ofNat

/-- `uint64`. -/
instance : SszType UInt64 where
  desc := Desc.uint64
  toValue a := .uint a.toNat
  ofValue := ofUint 8 UInt64.ofNat

/-- `uint256`. -/
instance : SszType Base.U256 where
  desc := Desc.uint256
  toValue a := .uint a.toNat
  ofValue := ofUint 32 (BitVec.ofNat 256)

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

end EthLib.Serialization.Ssz
