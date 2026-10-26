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

/-- Writing an object and reading it back returns the same object. -/
@[simp] theorem unpackBytes?_packBytes {n : Nat} (v : Vector UInt8 n) :
    unpackBytes? n (packBytes v) = some v := by
  -- A buffer holding exactly one object has room for it, so the guard passes.
  rw [unpackBytes?, dif_pos (by simp : 0 + n ≤ (packBytes v).size)]
  -- Reading back index `i` gives entry `i`, which rebuilds the object.
  simp [packBytes]

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
  simp only [Option.map_some, packBytes, Vector.toArray_ofFn, Nat.zero_add]
  -- The object's length is the buffer's, so the read indices cover it exactly.
  have hdata : b.data.size = n := hb
  subst hdata
  -- Tabulating every entry of an array rebuilds that array.
  refine congrArg some ?_
  exact congrArg ByteArray.mk Array.ofFn_getElem

/-! ## Reading one field out of a concatenation

A signature is a concatenation of fixed-size fields, so every field read is a
read at an offset inside a longer buffer. Three lemmas reduce such a read to
the single-object case already proved above: trailing bytes do not disturb a
read that already fitted, and skipping a prefix is reading the remainder at the
remaining offset. Since `++` is right associative, the second is the one that
peels a record one field at a time.
-/

/-- Appending bytes on the right leaves a read that already fitted unchanged.

So a field keeps its value as later fields are appended after it. -/
theorem unpackBytes?_append_of_fits {n : Nat} (b c : ByteArray) (offset : Nat)
    (h : offset + n ≤ b.size) :
    unpackBytes? n (b ++ c) offset = unpackBytes? n b offset := by
  -- Appending only grows the buffer, so the longer read passes the same guard.
  have hbc : offset + n ≤ (b ++ c).size := by
    rw [ByteArray.size_append]; omega
  rw [unpackBytes?, unpackBytes?, dif_pos hbc, dif_pos h]
  -- Both reads tabulate the same indices, so comparing entrywise suffices.
  refine congrArg some (Vector.ext ?_)
  intro i hi
  simp only [Vector.getElem_ofFn, ByteArray.data_append]
  -- Every index the read touches lies in the left operand, which is unchanged.
  exact Array.getElem_append_left (by simp only [ByteArray.size] at h; omega)

/-- Skipping a prefix is reading the remainder at the remaining offset.

Both directions matter: a read past the prefix succeeds exactly when the
remainder has room, so this rewrites acceptance as well as the value. -/
theorem unpackBytes?_append_add {n : Nat} (b c : ByteArray) (k : Nat) :
    unpackBytes? n (b ++ c) (b.size + k) = unpackBytes? n c k := by
  have hsz : (b ++ c).size = b.size + c.size := ByteArray.size_append
  rw [unpackBytes?, unpackBytes?]
  by_cases h : k + n ≤ c.size
  · rw [dif_pos (by omega : b.size + k + n ≤ (b ++ c).size), dif_pos h]
    refine congrArg some (Vector.ext ?_)
    intro i hi
    have hb : b.data.size = b.size := rfl
    -- Every index the read touches starts at or after the prefix.
    have hp : b.data.size ≤ b.size + k + i := by omega
    simp only [Vector.getElem_ofFn, ByteArray.data_append]
    rw [Array.getElem_append_right hp]
    -- Dropping the prefix from the index recovers the remainder's own index.
    have hidx : b.size + k + i - b.data.size = k + i := by omega
    simp only [hidx]
  · -- Without room in the remainder neither read passes its guard.
    rw [dif_neg (by omega : ¬ b.size + k + n ≤ (b ++ c).size), dif_neg h]

/-- A field at the front of a buffer is read back unchanged. -/
theorem unpackBytes?_append_packBytes_left {n : Nat} (v : Vector UInt8 n)
    (c : ByteArray) : unpackBytes? n (packBytes v ++ c) 0 = some v := by
  -- The field fills the left operand exactly, so the trailing bytes are inert.
  rw [unpackBytes?_append_of_fits _ _ _ (by simp), unpackBytes?_packBytes]

/-- Reading immediately after a prefix returns the object appended to it.

Stated for the buffer shape a record has: `++` is left associative, so the
fields after the one wanted sit outside the parenthesis. -/
theorem unpackBytes?_append_packBytes {n : Nat} (p : ByteArray)
    (v : Vector UInt8 n) (c : ByteArray) :
    unpackBytes? n ((p ++ packBytes v) ++ c) p.size = some v := by
  -- Frame away the trailing fields, which the read never touches.
  rw [unpackBytes?_append_of_fits _ _ _
    (by rw [ByteArray.size_append, size_packBytes]; exact Nat.le_refl _)]
  -- Then skip the prefix and read the field now at the front.
  rw [show p.size = p.size + 0 from rfl, unpackBytes?_append_add]
  simp

end EthLib.Cryptography.Xmss
