import EthLib.Cryptography.Xmss.Types

/-!
# Proofs: `Xmss.Types`

Properties of the fixed-size byte objects.
-/

namespace EthLib.Cryptography.Xmss

/-- A fixed-size object serializes to exactly its own length. -/
@[simp] theorem size_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).size = n := v.size_toArray

/-- Reading succeeds exactly when the buffer has room for the object.

Nothing weaker is accepted, so a caller cannot slip a short buffer through. -/
@[simp] theorem isSome_unpackBytes? {n : Nat} (b : ByteArray) (offset : Nat) :
    (unpackBytes? n b offset).isSome ↔ offset + n ≤ b.size := by
  -- Acceptance is the guard itself, so both branches close by case analysis.
  rw [unpackBytes?]
  split <;> simp_all

/-- Reading the bytes of an object returns that object. -/
@[simp] theorem readBytes_packBytes {n : Nat} (v : Vector UInt8 n) (h) :
    readBytes (packBytes v) 0 n h = v := by
  apply Vector.ext
  intro i hi
  simp [readBytes, packBytes]

/-- Writing an object and reading it back returns the same object. -/
@[simp] theorem unpackBytes?_packBytes {n : Nat} (v : Vector UInt8 n) :
    unpackBytes? n (packBytes v) = some v := by
  -- A buffer holding exactly one object has room for it, so the guard passes.
  rw [unpackBytes?, dif_pos (by simp : 0 + n ≤ (packBytes v).size)]
  -- Reading back index `i` gives entry `i`, which rebuilds the object.
  exact congrArg some (readBytes_packBytes v _)

/-- Two objects with the same bytes are the same object. -/
theorem packBytes_injective {n : Nat} :
    Function.Injective (packBytes (n := n)) := by
  -- Reading the bytes back recovers each object.
  intro v w h
  simpa using congrArg (unpackBytes? n) h

/-- Reading a full-length buffer and writing it back returns it unchanged.

So no buffer is unreachable, and no object has two encodings. -/
theorem packBytes_unpackBytes? {n : Nat} {b : ByteArray} (hb : b.size = n) :
    (unpackBytes? n b).map packBytes = some b := by
  -- A buffer of exactly the right length has room, so the guard passes.
  rw [unpackBytes?, dif_pos (by omega : 0 + n ≤ b.size)]
  simp only [Option.map_some, packBytes, readBytes, Vector.toArray_ofFn, Nat.zero_add]
  -- The object's length is the buffer's, so the read indices cover it exactly.
  have hdata : b.data.size = n := hb
  subst hdata
  -- Tabulating every entry of an array rebuilds that array.
  exact congrArg (some ∘ ByteArray.mk) Array.ofFn_getElem

/-- A read that ends inside the first part of a concatenation reads that part. -/
theorem readBytes_append_left {a b : ByteArray} {offset n : Nat} (h)
    (inside : offset + n ≤ a.size) :
    readBytes (a ++ b) offset n h = readBytes a offset n inside := by
  apply Vector.ext
  intro i hi
  simp only [readBytes, Vector.getElem_ofFn, ByteArray.data_append]
  rw [Array.getElem_append_left (by simp only [ByteArray.size] at inside; omega)]

/-- A read that starts after the first part of a concatenation reads the second. -/
theorem readBytes_append_right {a b : ByteArray} {offset n : Nat} (h) :
    readBytes (a ++ b) (a.size + offset) n h
      = readBytes b offset n (by simp only [ByteArray.size_append] at h; omega) := by
  apply Vector.ext
  intro i hi
  simp only [readBytes, Vector.getElem_ofFn, ByteArray.data_append]
  rw [Array.getElem_append_right (by simp only [ByteArray.size]; omega)]
  -- The index past the first part is the index into the second.
  congr 1
  simp only [ByteArray.size]
  omega

/-- Reading back the raw array of an object returns that object. -/
@[simp] theorem unpackBytes?_toArray {n : Nat} (v : Vector UInt8 n) :
    unpackBytes? n ⟨v.toArray⟩ = some v :=
  unpackBytes?_packBytes v

end EthLib.Cryptography.Xmss
