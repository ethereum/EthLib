module

public import EthLib.Base.LittleEndian

/-!
# Proofs: `LittleEndian`

Writing and reading little-endian bytes undo each other.

A number below `256 ^ k` survives the trip through `k` bytes, and `k` bytes survive the trip
through their value.
-/

@[expose] public section

namespace EthLib.Base

/-- The first byte is the low byte, and the rest encode the quotient by 256. -/
theorem uintToBytes_toList_succ (k n : Nat) :
    (uintToBytes (k + 1) n).toList = UInt8.ofNat n :: (uintToBytes k (n / 256)).toList := by
  simp only [uintToBytes, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, Nat.pow_zero,
    Nat.div_one, Fin.val_succ, Nat.pow_succ, Nat.div_div_eq_div_mul, List.cons.injEq, true_and]
  -- Byte `i + 1` of `n` is byte `i` of `n / 256`.
  congr 1
  funext i
  congr 1
  rw [Nat.mul_comm]

/-- Reading a number back folds over the bytes as a list. -/
theorem bytesToUint_eq_foldr {k : Nat} (v : Vector UInt8 k) :
    bytesToUint v = v.toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by
  unfold bytesToUint
  rw [← Array.foldr_toList]
  rfl

/-- Writing a number on `k` bytes and reading it back keeps its low `8k` bits. -/
@[simp] theorem bytesToUint_uintToBytes (k n : Nat) :
    bytesToUint (uintToBytes k n) = n % 256 ^ k := by
  rw [bytesToUint_eq_foldr]
  induction k generalizing n with
  | zero => simp [uintToBytes, Nat.mod_one, Vector.toList_ofFn]
  | succ k ih =>
    -- The low byte plus 256 times the higher bytes is the remainder by `256^(k+1)`.
    rw [uintToBytes_toList_succ, List.foldr_cons, ih, Nat.pow_succ, Nat.mul_comm _ 256,
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

/-- A number read from `k` bytes is below `256^k`. -/
theorem bytesToUint_lt {k : Nat} (v : Vector UInt8 k) : bytesToUint v < 256 ^ k := by
  rw [bytesToUint_eq_foldr]
  simpa using foldr_lt v.toList

private theorem uintToBytes_foldr (l : List UInt8) :
    (uintToBytes l.length (l.foldr (fun byte acc => byte.toNat + 256 * acc) 0)).toList = l := by
  induction l with
  | nil => simp [uintToBytes, Vector.toList_ofFn]
  | cons b t ih =>
    rw [List.length_cons, uintToBytes_toList_succ, List.foldr_cons]
    have hb := b.toNat_lt
    -- The low byte is below 256, so dividing by 256 leaves the higher bytes.
    have hdiv : (b.toNat + 256 * t.foldr (fun byte acc => byte.toNat + 256 * acc) 0) / 256
        = t.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by omega
    rw [hdiv, ih]
    -- The low byte of the number is the first byte itself.
    congr 1
    apply UInt8.toNat.inj
    simp

/-- Reading `k` bytes as a number and writing it back on `k` bytes returns the bytes. -/
@[simp] theorem uintToBytes_bytesToUint {k : Nat} (v : Vector UInt8 k) :
    uintToBytes k (bytesToUint v) = v := by
  -- Expose the vector as a list, so its length is the list's own.
  rcases v with ⟨⟨l⟩, rfl⟩
  apply Vector.toList_inj.mp
  rw [bytesToUint_eq_foldr]
  exact uintToBytes_foldr l

/-- Two numbers below `256^k` with the same `k` bytes are equal. -/
theorem uintToBytes_inj {k x y : Nat} (hx : x < 256 ^ k) (hy : y < 256 ^ k)
    (h : uintToBytes k x = uintToBytes k y) : x = y := by
  -- Reading the bytes back returns each number, unchanged by the bound.
  have := congrArg bytesToUint h
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-! ## Bytes as a list

A decoder that holds its input as a list reads a prefix of unknown length as a vector.

The type of that vector depends on the list, so proofs first turn it into a fold over the list.
-/

/-- A list of bytes, read as a number, is a fold from its last byte down. -/
theorem bytesToUint_toVector (l : List UInt8) :
    bytesToUint l.toArray.toVector = l.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by
  rw [bytesToUint_eq_foldr]
  simp

/-- The bytes of a number, folded back, keep its low `8k` bits. -/
theorem foldr_uintToBytes (k n : Nat) :
    (uintToBytes k n).toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0 = n % 256 ^ k := by
  rw [← bytesToUint_eq_foldr, bytesToUint_uintToBytes]

/-- The `UInt64` read from at most eight bytes is the number they write. -/
@[simp] theorem toNat_bytesToUint64 {k : Nat} (data : Vector UInt8 k) (h : k ≤ 8) :
    (bytesToUint64 data h).toNat = bytesToUint data := by
  -- At most eight bytes write a value below `2^64`, so the conversion keeps it.
  have hlt : bytesToUint data < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (bytesToUint_lt data)
      (by simpa [show (2 : Nat) ^ 64 = 256 ^ 8 from rfl] using Nat.pow_le_pow_right (by decide) h)
  simp [bytesToUint64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-- Writing a `UInt64` on eight bytes and reading them back returns it. -/
@[simp] theorem bytesToUint64_uintToBytes (n : UInt64) :
    bytesToUint64 (uintToBytes 8 n.toNat) = n := by
  apply UInt64.toNat.inj
  simp

/-- Reading eight bytes as a `UInt64` and writing it back returns the bytes. -/
@[simp] theorem uintToBytes_bytesToUint64 (data : Vector UInt8 8) :
    uintToBytes 8 (bytesToUint64 data).toNat = data := by
  simp

end EthLib.Base
