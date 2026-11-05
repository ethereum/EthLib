module

public import EthLib.Base.Bytes

/-!
# Proofs: `Bytes`

The bytes of a fixed-size object have its length.

A read of those bytes returns the object.

So two objects with the same bytes are the same object.

The exclusive or of byte strings is commutative, and applying one string twice undoes it.

A byte of a join or a slice is a byte of a part, or zero past its end.

Two strings of one size are equal when they agree on every byte.
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

/-! ## One byte of a buffer -/

/-- A byte of the buffer is the byte of its array, or zero past its end. -/
theorem byteAt_eq_getD (data : ByteArray) (i : Nat) : byteAt data i = data.data.getD i 0 := by
  unfold byteAt
  split
  · rename_i h
    simp [Array.getD_eq_getD_getElem?, ByteArray.getElem_eq_getElem_data,
      Array.getElem?_eq_getElem (by simpa [← ByteArray.size_data] using h)]
  · rename_i h
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
      (by simpa [← ByteArray.size_data] using Nat.le_of_not_lt h)]

/-- Past the end of the buffer every byte reads as zero. -/
theorem byteAt_of_size_le {data : ByteArray} {i : Nat} (h : data.size ≤ i) :
    byteAt data i = 0 := by
  simp [byteAt_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- A byte of two strings joined is a byte of the first, or of the second past its end. -/
theorem byteAt_append (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) i = if i < a.size then byteAt a i else byteAt b (i - a.size) := by
  have hs := @ByteArray.size_append a b
  unfold byteAt
  by_cases ha : i < a.size
  · rw [ite_eq_left ha, dite_eq_left ha, dite_eq_left (show i < (a ++ b).size by omega),
      ByteArray.getElem_append_left ha]
  · rw [ite_eq_right ha]
    by_cases hb : i - a.size < b.size
    · rw [dite_eq_left hb, dite_eq_left (show i < (a ++ b).size by omega),
        ByteArray.getElem_append_right (Nat.le_of_not_lt ha)]
    · rw [dite_eq_right hb, dite_eq_right (show ¬i < (a ++ b).size by omega)]

/-- Padding the buffer with zero bytes on the right changes no byte. -/
theorem byteAt_append_zeros (data : ByteArray) (n i : Nat) :
    byteAt (data ++ ByteArray.mk (Array.replicate n 0)) i = byteAt data i := by
  rw [byteAt_append]
  split
  · rfl
  · rw [byteAt_eq_getD, Nat.not_lt.mp ‹_› |> byteAt_of_size_le |>.symm]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl

/-- A byte of a slice is the byte at the same offset from its start, or zero past its end. -/
theorem byteAt_extract (b : ByteArray) (start stop j : Nat) :
    byteAt (b.extract start stop) j
      = if start + j < min stop b.size then byteAt b (start + j) else 0 := by
  have hs := @ByteArray.size_extract b start stop
  have hm := Nat.min_le_right stop b.size
  unfold byteAt
  by_cases hj : start + j < min stop b.size
  · rw [ite_eq_left hj, dite_eq_left (show j < (b.extract start stop).size by omega),
      dite_eq_left (show start + j < b.size by omega), ByteArray.getElem_extract]
  · rw [ite_eq_right hj, dite_eq_right (show ¬j < (b.extract start stop).size by omega)]

/-- Two strings of one size are equal when they agree on every byte. -/
theorem eq_of_byteAt {a b : ByteArray} (size : a.size = b.size)
    (bytes : ∀ i, byteAt a i = byteAt b i) : a = b := by
  apply ByteArray.ext
  apply Array.ext size
  intro i ha hb
  have h := bytes i
  unfold byteAt at h
  rw [dite_eq_left (show i < a.size from ha), dite_eq_left (show i < b.size from hb)] at h
  exact h

end EthLib.Base
