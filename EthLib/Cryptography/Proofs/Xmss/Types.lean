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
  rw [unpackBytes?, dite_eq_left (by simp : 0 + n ≤ (packBytes v).size)]
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
  rw [unpackBytes?, dite_eq_left (by omega : 0 + n ≤ b.size)]
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

/-! ## Little-endian integers -/

/-- The first byte of a little-endian integer is its low byte; the rest encode the quotient. -/
theorem littleEndian_toList_succ (k z : Nat) :
    (littleEndian (k + 1) z).toList = UInt8.ofNat z :: (littleEndian k (z / 256)).toList := by
  simp only [littleEndian, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, Nat.pow_zero,
    Nat.div_one, Fin.val_succ, Nat.pow_succ, Nat.div_div_eq_div_mul, List.cons.injEq, true_and]
  -- Byte `i + 1` of `z` is byte `i` of `z / 256`.
  congr 1
  funext i
  congr 1
  rw [Nat.mul_comm]

/-- Reading an integer back folds over the bytes as a list. -/
theorem fromLittleEndian_eq_foldr {k : Nat} (v : Vector UInt8 k) :
    fromLittleEndian v = v.toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by
  unfold fromLittleEndian
  rw [← Array.foldr_toList]
  rfl

/-- Encoding an integer in `k` bytes and reading it back keeps its low `8k` bits. -/
@[simp] theorem fromLittleEndian_littleEndian (k z : Nat) :
    fromLittleEndian (littleEndian k z) = z % 256 ^ k := by
  rw [fromLittleEndian_eq_foldr]
  induction k generalizing z with
  | zero => simp [littleEndian, Nat.mod_one, Vector.toList_ofFn]
  | succ k ih =>
    -- The low byte plus 256 times the higher bytes is the remainder by `256^(k+1)`.
    rw [littleEndian_toList_succ, List.foldr_cons, ih, Nat.pow_succ, Nat.mul_comm _ 256,
      Nat.mod_mul]
    simp [UInt8.toNat_ofNat']

private theorem foldr_lt (l : List UInt8) :
    l.foldr (fun byte acc => byte.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    -- The low byte is below 256, and the rest is below `256^length`.
    have := b.toNat_lt
    omega

/-- A `k`-byte integer is below `256^k`. -/
theorem fromLittleEndian_lt {k : Nat} (v : Vector UInt8 k) : fromLittleEndian v < 256 ^ k := by
  rw [fromLittleEndian_eq_foldr]
  simpa using foldr_lt v.toList

private theorem littleEndian_foldr (l : List UInt8) :
    (littleEndian l.length (l.foldr (fun byte acc => byte.toNat + 256 * acc) 0)).toList = l := by
  induction l with
  | nil => simp [littleEndian, Vector.toList_ofFn]
  | cons b t ih =>
    rw [List.length_cons, littleEndian_toList_succ, List.foldr_cons]
    have hb := b.toNat_lt
    -- The low byte is below 256, so dividing by 256 leaves the higher bytes.
    have hdiv : (b.toNat + 256 * t.foldr (fun byte acc => byte.toNat + 256 * acc) 0) / 256
        = t.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by omega
    rw [hdiv, ih]
    -- The low byte of the integer is the first byte itself.
    congr 1
    apply UInt8.toNat.inj
    simp

/-- Reading `k` bytes as an integer and encoding it back returns the bytes. -/
@[simp] theorem littleEndian_fromLittleEndian {k : Nat} (v : Vector UInt8 k) :
    littleEndian k (fromLittleEndian v) = v := by
  -- Expose the vector as a list, so its length is the list's own.
  rcases v with ⟨⟨l⟩, rfl⟩
  apply Vector.toList_inj.mp
  rw [fromLittleEndian_eq_foldr]
  exact littleEndian_foldr l

end EthLib.Cryptography.Xmss
