module

public import EthLib.Base.ByteOrder

/-!
# Proofs: `ByteOrder`

Writing and reading little-endian bytes undo each other.

A number below `256 ^ k` survives the trip through `k` bytes.

A vector of `k` bytes survives the trip through its value.
-/

@[expose] public section

namespace EthLib.Base.ByteOrder

/-- Byte `i` of a number is its quotient by `256 ^ i`, truncated to a byte. -/
theorem toLE_eq_div (k n : Nat) :
    toLE k n = Vector.ofFn fun i => UInt8.ofNat (n / 256 ^ i.val) := by
  simp only [toLE, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The first byte is the low byte, and the rest encode the quotient by 256. -/
theorem toList_toLE_succ (k n : Nat) :
    (toLE (k + 1) n).toList = UInt8.ofNat n :: (toLE k (n / 256)).toList := by
  simp only [toLE_eq_div, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, Nat.pow_zero,
    Nat.div_one, Fin.val_succ, Nat.pow_succ, Nat.div_div_eq_div_mul, List.cons.injEq, true_and]
  -- Byte `i + 1` of `n` is byte `i` of `n / 256`.
  congr 1
  funext i
  congr 1
  rw [Nat.mul_comm]

/-- Reading a number back folds over the bytes as a list. -/
theorem ofLE_eq_foldr {k : Nat} (v : Vector UInt8 k) :
    ofLE v = v.toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by
  unfold ofLE
  rw [← Array.foldr_toList]
  rfl

/-- Writing a number on `k` bytes and reading it back keeps its low `8k` bits. -/
@[simp] theorem ofLE_toLE (k n : Nat) :
    ofLE (toLE k n) = n % 256 ^ k := by
  rw [ofLE_eq_foldr]
  induction k generalizing n with
  | zero => simp [toLE_eq_div, Nat.mod_one, Vector.toList_ofFn]
  | succ k ih =>
    -- The low byte plus 256 times the higher bytes is the remainder by `256^(k+1)`.
    rw [toList_toLE_succ, List.foldr_cons, ih, Nat.pow_succ, Nat.mul_comm _ 256,
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
theorem ofLE_lt {k : Nat} (v : Vector UInt8 k) : ofLE v < 256 ^ k := by
  rw [ofLE_eq_foldr]
  simpa using foldr_lt v.toList

private theorem toLE_foldr (l : List UInt8) :
    (toLE l.length (l.foldr (fun byte acc => byte.toNat + 256 * acc) 0)).toList = l := by
  induction l with
  | nil => simp [toLE_eq_div, Vector.toList_ofFn]
  | cons b t ih =>
    rw [List.length_cons, toList_toLE_succ, List.foldr_cons]
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
@[simp] theorem toLE_ofLE {k : Nat} (v : Vector UInt8 k) :
    toLE k (ofLE v) = v := by
  -- Expose the vector as a list, so its length is the list's own.
  rcases v with ⟨⟨l⟩, rfl⟩
  apply Vector.toList_inj.mp
  rw [ofLE_eq_foldr]
  exact toLE_foldr l

/-- Two numbers below `256^k` with the same `k` bytes are equal. -/
theorem toLE_inj {k x y : Nat} (hx : x < 256 ^ k) (hy : y < 256 ^ k)
    (h : toLE k x = toLE k y) : x = y := by
  -- Reading the bytes back returns each number, unchanged by the bound.
  have := congrArg ofLE h
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-! ## Bytes as a list

A decoder that holds its input as a list reads a prefix of unknown length as a vector.

The type of that vector depends on the list, so proofs first turn it into a fold over the list.
-/

/-- A list of bytes, read as a number, is a fold from its last byte down. -/
theorem ofLE_toVector (l : List UInt8) :
    ofLE l.toArray.toVector = l.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by
  rw [ofLE_eq_foldr]
  simp

/-- The bytes of a number, folded back, keep its low `8k` bits. -/
theorem foldr_toLE (k n : Nat) :
    (toLE k n).toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0 = n % 256 ^ k := by
  rw [← ofLE_eq_foldr, ofLE_toLE]

/-- The bytes of a number below `256^k`, folded back, give the number. -/
theorem foldr_toLE_of_lt {k n : Nat} (h : n < 256 ^ k) :
    (toLE k n).foldr (fun byte acc => byte.toNat + 256 * acc) 0 = n := by
  rw [← Vector.foldr_toList, foldr_toLE, Nat.mod_eq_of_lt h]

/-- At most eight bytes read as a number that a `UInt64` holds exactly. -/
theorem toNat_ofNat_ofLE {k : Nat} (data : Vector UInt8 k) (h : k ≤ 8) :
    (UInt64.ofNat (ofLE data)).toNat = ofLE data := by
  -- At most eight bytes write a value below `2^64`, so the conversion keeps it.
  have hlt : ofLE data < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (ofLE_lt data)
      (by simpa [show (2 : Nat) ^ 64 = 256 ^ 8 from rfl] using Nat.pow_le_pow_right (by decide) h)
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-! ## Bytes as an array

A codec that holds its bytes as an array writes and reads a number one byte at a time.
-/

/-- The bytes of a number are its low byte, then the bytes of its quotient by 256. -/
theorem toArray_toLE_succ (k n : Nat) :
    (toLE (k + 1) n).toArray = #[UInt8.ofNat n] ++ (toLE k (n / 256)).toArray := by
  apply Array.toList_inj.mp
  simpa [Vector.toList] using toList_toLE_succ k n

/-- A number read from bytes is the first byte plus 256 times the number the rest read as. -/
theorem ofLE_ofFn_succ {k : Nat} (f : Fin (k + 1) → UInt8) :
    ofLE (Vector.ofFn f)
      = (f 0).toNat + 256 * ofLE (Vector.ofFn fun i => f i.succ) := by
  simp [ofLE_eq_foldr, Vector.toList_ofFn, List.ofFn_succ]

end EthLib.Base.ByteOrder
