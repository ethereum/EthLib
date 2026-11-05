module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.HashSig

/-!
# Proofs: the common frame of the hash-based signatures

A read of a fixed-size object succeeds exactly when the buffer has room, and reads back a write.

A read out of a concatenation reads the part it covers.

In the identity monad, a vector computed in order is the vector of its entries.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open EthLib.Base (packBytes readBytes readBytes_packBytes)

/-! ## Reading fixed-size objects -/

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
  rw [unpackBytes?, dite_eq_left (by simp : 0 + n ≤ (packBytes v).size)]
  -- Reading back index `i` gives entry `i`, which rebuilds the object.
  exact congrArg some (readBytes_packBytes v _)

/-- Reading a full-length buffer and writing it back returns it unchanged.

So no buffer is unreachable, and no object has two encodings. -/
theorem packBytes_unpackBytes? {n : Nat} {b : ByteArray} (hb : b.size = n) :
    (unpackBytes? n b).map packBytes = some b := by
  -- A buffer of exactly the right length has room, so the guard passes.
  rw [unpackBytes?, dite_eq_left (by omega : 0 + n ≤ b.size)]
  simp only [Option.map_some, packBytes, readBytes, Vector.toArray_ofFn, Nat.zero_add]
  -- The object's length is the buffer's, so the read indices cover it exactly.
  have hdata : b.data.size = n := hb
  subst hdata
  -- Tabulating every entry of an array rebuilds that array.
  exact congrArg (some ∘ ByteArray.mk) Array.ofFn_getElem

/-- Reading back the raw array of an object returns that object. -/
@[simp] theorem unpackBytes?_toArray {n : Nat} (v : Vector UInt8 n) :
    unpackBytes? n ⟨v.toArray⟩ = some v :=
  unpackBytes?_packBytes v

/-! ## Reading out of a concatenation -/

/-- Two concatenations with first parts of the same size agree part by part. -/
theorem byteArray_append_inj {a b c d : ByteArray} (h : a ++ b = c ++ d) (hs : a.size = c.size) :
    a = c ∧ b = d := by
  have := congrArg ByteArray.data h
  simp only [ByteArray.data_append] at this
  obtain ⟨ha, hb⟩ := Array.append_inj this hs
  exact ⟨ByteArray.ext ha, ByteArray.ext hb⟩

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

/-- A read that covers exactly the middle part of a concatenation returns that part. -/
theorem readBytes_middle {b a c : ByteArray} {n : Nat} {v : Vector UInt8 n} {offset : Nat}
    (hb : b = a ++ packBytes v ++ c) (ho : offset = a.size) (h : offset + n ≤ b.size) :
    readBytes b offset n h = v := by
  subst hb ho
  -- Strip the last part, then the first, leaving the object itself.
  rw [readBytes_append_left _ (by simp)]
  have past := readBytes_append_right (a := a) (b := packBytes v) (offset := 0) (n := n)
    (by simp)
  simp only [Nat.add_zero] at past
  rw [past, readBytes_packBytes]

/-- The bytes of a read are the slice of the buffer it covers. -/
theorem packBytes_readBytes (b : ByteArray) (offset n : Nat) (h) :
    packBytes (readBytes b offset n h) = ⟨b.data.extract offset (offset + n)⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size] at h
    simp only [packBytes, readBytes, Vector.toArray_ofFn, Array.size_ofFn, Array.size_extract]
    omega
  · intro i h₁ h₂
    simp [packBytes, readBytes]

/-! ## Computing a vector in order -/

/-- In the identity monad, computing a vector in order is building it from its entries. -/
@[simp] theorem ofFnInOrder_run {α : Type} :
    ∀ (n : Nat) (f : Fin n → Id α), (ofFnInOrder n f).run = Vector.ofFn fun i => (f i).run
  | 0, _ => Vector.ext fun _ hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, f => by
    simp only [ofFnInOrder, Id.run_bind, Id.run_pure, ofFnInOrder_run n]
    apply Vector.ext
    intro i hi
    -- Entry 0 is the head, entry `i + 1` is entry `i` of the tail.
    cases i with
    | zero => simp
    | succ i => simp [Fin.succ]

end EthLib.Cryptography.HashSig
