module

public import EthLib.Base.Bytes

/-!
# Proofs: `Bytes`

The bytes of a fixed-size object have its length.

A read of those bytes returns the object.

So two objects with the same bytes are the same object.

The exclusive or of byte strings is commutative, and applying one string twice undoes it.
-/

@[expose] public section

namespace EthLib.Base

/-- A fixed-size object serializes to exactly its own length. -/
@[simp] theorem size_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).size = n := v.size_toArray

/-- Reading the bytes of an object returns that object. -/
@[simp] theorem readBytes_packBytes {n : Nat} (v : Vector UInt8 n) (h) :
    readBytes (packBytes v) 0 n h = v := by
  apply Vector.ext
  intro i hi
  simp [readBytes, packBytes]

/-- Two objects with the same bytes are the same object. -/
theorem packBytes_injective {n : Nat} :
    Function.Injective (packBytes (n := n)) := by
  -- The bytes are the object's array, and the array determines the vector.
  intro v w h
  exact Vector.toArray_inj.mp (congrArg ByteArray.data h)

/-- The exclusive or of two byte strings does not depend on their order. -/
theorem xorBytes_comm {n : Nat} (a b : Vector UInt8 n) : xorBytes a b = xorBytes b a := by
  apply Vector.ext
  intro i hi
  simp [xorBytes, UInt8.xor_comm]

/-- Applying the same byte string twice gives back the first string. -/
@[simp] theorem xorBytes_xorBytes_cancel_right {n : Nat} (a b : Vector UInt8 n) :
    xorBytes (xorBytes a b) b = a := by
  apply Vector.ext
  intro i hi
  simp [xorBytes, UInt8.xor_assoc]

end EthLib.Base
