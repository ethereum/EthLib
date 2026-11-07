module

public import EthLib.Serialization.Ssz.Codec.Deserialize
public import EthLib.Serialization.Ssz.Codec.Root

/-!
# Typed SSZ values

A Lean type becomes an SSZ type by naming its declaration and converting its values.

Serialization, deserialization and the root then come from the codec of untyped values.

A type may compute them directly instead, and its laws then tie them to the untyped codec.
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
  /--
  The Merkle root of a value, which is the root of its untyped value.

  A type that keeps the tree of its values reads the root there instead of hashing again.
  -/
  root : α → Except Err Bytes := fun a => Ssz.hashTreeRoot desc (toValue a)
  /--
  The bytes of a value, which are the bytes of its untyped value.

  A type may write its bytes directly instead of building the untyped value.
  -/
  encode : α → Except Err ByteArray := fun a => do return ⟨← Ssz.serialize desc (toValue a)⟩
  /--
  The value that bytes encode, which is the typed value of their untyped decoding.

  A type may read its bytes directly instead of building the untyped value.
  -/
  decode : ByteArray → Except Err α := fun data => do ofValue (← Ssz.deserialize desc data.data)

namespace SszType

variable {α : Type} [SszType α]

/-- The bytes of a value. -/
def serialize (a : α) : Except Err ByteArray := encode a

/-- The value of a type that the bytes encode, or why they encode none. -/
def deserialize (α : Type) [SszType α] (data : ByteArray) : Except Err α := decode data

/--
The 32-byte Merkle root of a value.

The width check never fails on a well-formed type, since every root there is one node.
-/
def hashTreeRoot (a : α) : Except Err (Vector UInt8 32) := do
  toChunk (← root a)

end SszType

end EthLib.Serialization.Ssz
