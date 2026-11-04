module

public import EthLib.Serialization.Ssz.Codec.Deserialize
public import EthLib.Serialization.Ssz.Codec.Root

/-!
# Typed SSZ values

A Lean type becomes an SSZ type by naming its declaration and converting its values.

Serialization, deserialization and the root then come from the codec of untyped values.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A Lean type whose values are the values of one SSZ type. -/
class SszType (α : Type) where
  /-- The SSZ type. -/
  desc : Desc
  /-- The untyped value that a typed value stands for. -/
  toValue : α → Value
  /-- The typed value that an untyped value stands for, or why it stands for none. -/
  ofValue : Value → Except Err α

namespace SszType

variable {α : Type} [SszType α]

/-- The bytes of a value. -/
def serialize (a : α) : Except Err ByteArray := do
  return ⟨← Ssz.serialize (desc α) (toValue a)⟩

/-- The value of a type that the bytes encode, or why they encode none. -/
def deserialize (α : Type) [SszType α] (data : ByteArray) : Except Err α := do
  ofValue (← Ssz.deserialize (desc α) data.data)

/--
The 32-byte Merkle root of a value.

The width check never fails on a well-formed type, since every root there is one node.
-/
def hashTreeRoot (a : α) : Except Err (Vector UInt8 32) := do
  let root ← Ssz.hashTreeRoot (desc α) (toValue a)
  if width : root.size = bytesPerChunk then return ⟨root, width⟩
  else throw (.count bytesPerChunk root.size)

end SszType

end EthLib.Serialization.Ssz
