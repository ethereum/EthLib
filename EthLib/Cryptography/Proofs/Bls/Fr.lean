module

public import EthLib.Cryptography.Bls.Fr
public import EthLib.Cryptography.Proofs.Montgomery

/-!
# Proofs: `Fr`

Algebraic facts about multiplication, addition and powers in `Fr`, and about its integer.

An element maps to the integer mod `r` that it stands for, and the map is injective.

So each identity follows from the same identity mod `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Fr

open EthLib.Cryptography.Montgomery (toZMod toZMod_injective toZMod_mul toZMod_add toZMod_pow)

instance : NeZero params.p := ⟨by decide⟩

instance : Fact (1 < params.p) := ⟨by decide⟩

/-- `Fr.one` agrees with the `OfNat` numeral `1`. -/
theorem one_eq_one : one = (1 : Fr) := rfl

/-! ## The integer of an element -/

/-- The integer of an element is its value in `ZMod r`. -/
theorem val_eq (a : Fr) : a.val = (toZMod a).val := by
  unfold val
  exact Montgomery.toNat_eq a

/-- The integer of an element is below `r`. -/
theorem val_lt (a : Fr) : a.val < modulus := by
  unfold val
  exact Montgomery.toNat_lt a

/-- Two elements with the same integer are equal. -/
theorem val_injective : Function.Injective (val : Fr → Nat) := by
  intro a b h
  rw [val_eq, val_eq] at h
  exact toZMod_injective (ZMod.val_injective _ h)

/-- Two elements with the same integer are equal. -/
@[ext] theorem ext {a b : Fr} (h : a.val = b.val) : a = b :=
  val_injective h

/-- The element of `n` has the integer `n mod r`. -/
theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := by
  rw [val_eq]
  change (toZMod (Montgomery.ofNat n : Fr)).val = _
  rw [Montgomery.toZMod_ofNat]
  exact ZMod.val_natCast _ n

/-- The element of an integer below `r` has that integer. -/
theorem val_ofNat_of_lt {n : Nat} (h : n < modulus) : (ofNat n).val = n := by
  rw [val_ofNat, Nat.mod_eq_of_lt h]

/-- Zero has the integer `0`. -/
@[simp] theorem val_zero : (0 : Fr).val = 0 := by
  rw [val_eq, Montgomery.toZMod_zero]
  exact ZMod.val_zero

/-- One has the integer `1`. -/
@[simp] theorem val_one : (1 : Fr).val = 1 := by
  rw [val_eq, Montgomery.toZMod_one]
  exact ZMod.val_one _

/-- The integer of a sum is the sum mod `r`. -/
theorem val_add (a b : Fr) : (a + b).val = (a.val + b.val) % modulus := by
  rw [val_eq, val_eq, val_eq, toZMod_add]
  exact ZMod.val_add _ _

/-- The integer of a product is the product mod `r`. -/
theorem val_mul (a b : Fr) : (a * b).val = a.val * b.val % modulus := by
  rw [val_eq, val_eq, val_eq, toZMod_mul]
  exact ZMod.val_mul _ _

/-- `ofNat` always produces a canonical value. -/
theorem val_ofNat_lt (n : Nat) : (ofNat n).val < modulus :=
  val_lt _

/-- `hashToBlsField` always produces a canonical value. -/
theorem val_hashToBlsField_lt (data : ByteArray) :
    (hashToBlsField data).val < modulus :=
  val_ofNat_lt _

/-- `isZero` tests equality with zero. -/
theorem isZero_iff (a : Fr) : a.isZero = true ↔ a = 0 := by
  unfold isZero
  rw [beq_iff_eq]
  rfl

/-! ## Ring identities -/

protected theorem mul_comm (a b : Fr) : a * b = b * a :=
  toZMod_injective (by rw [toZMod_mul, toZMod_mul, mul_comm])

protected theorem mul_assoc (a b c : Fr) : a * b * c = a * (b * c) :=
  toZMod_injective (by rw [toZMod_mul, toZMod_mul, toZMod_mul, toZMod_mul, mul_assoc])

/-- One is neutral for the product. -/
protected theorem mul_one (a : Fr) : a * one = a :=
  toZMod_injective (by rw [toZMod_mul, one_eq_one, Montgomery.toZMod_one, mul_one])

/-- One is neutral for the product, on the left. -/
protected theorem one_mul (a : Fr) : one * a = a := by
  rw [Fr.mul_comm, Fr.mul_one]

/-- A trailing `* one` cancels under an outer multiplication. -/
theorem mul_mul_one (a b : Fr) : a * (b * one) = a * b := by
  rw [Fr.mul_one]

/-- A leading `one *` cancels under an outer multiplication. -/
theorem mul_one_mul (a b : Fr) : a * (one * b) = a * b := by
  rw [Fr.one_mul]

/-- `one *` is the identity on any product. -/
theorem one_mul_mul (a b : Fr) : one * (a * b) = a * b :=
  Fr.one_mul _

/-- Zero is neutral for the sum. -/
protected theorem add_zero (a : Fr) : a + zero = a :=
  toZMod_injective (by rw [toZMod_add, show toZMod zero = 0 from Montgomery.toZMod_zero, add_zero])

/-- Zero is neutral for the sum, on the left. -/
protected theorem zero_add (a : Fr) : zero + a = a :=
  toZMod_injective (by rw [toZMod_add, show toZMod zero = 0 from Montgomery.toZMod_zero, zero_add])

/-- Zero absorbs the product. -/
protected theorem mul_zero (a : Fr) : a * zero = zero :=
  toZMod_injective (by rw [toZMod_mul, show toZMod zero = 0 from Montgomery.toZMod_zero, mul_zero])

/-- Zero absorbs the product, on the left. -/
protected theorem zero_mul (a : Fr) : zero * a = zero := by
  rw [Fr.mul_comm, Fr.mul_zero]

/-- The product distributes over the sum. -/
protected theorem add_mul (a b c : Fr) : (a + b) * c = a * c + b * c :=
  toZMod_injective (by simp only [toZMod_add, toZMod_mul]; ring)

/-- A negation cancels its element. -/
protected theorem neg_add_cancel (a : Fr) : -a + a = zero :=
  toZMod_injective (by
    rw [toZMod_add, Montgomery.toZMod_neg, show toZMod zero = 0 from Montgomery.toZMod_zero,
      neg_add_cancel])

/-- Addition is commutative -/
protected theorem add_comm (a b : Fr) : a + b = b + a :=
  toZMod_injective (by rw [toZMod_add, toZMod_add, add_comm])

/-- Addition is associative -/
protected theorem add_assoc (a b c : Fr) : a + b + c = a + (b + c) :=
  toZMod_injective (by rw [toZMod_add, toZMod_add, toZMod_add, toZMod_add, add_assoc])

/-- Addition is commutative, even with an addition before -/
protected theorem add_right_comm (a b c : Fr) : a + b + c = a + c + b := by
  rw [Fr.add_assoc, Fr.add_comm b, ← Fr.add_assoc]

/-! ## Powers -/

/-- The power maps to the power mod `r`. -/
theorem toZMod_powNat (a : Fr) (e : Nat) : toZMod (powNat a e) = toZMod a ^ e :=
  toZMod_pow a e

/-- 0th power is always one -/
theorem powNat_zero (a : Fr) : powNat a 0 = one :=
  toZMod_injective (by rw [toZMod_powNat, pow_zero, one_eq_one, Montgomery.toZMod_one])

/-- Simple-recursion model of `powNat` (repeated multiplication). -/
def powNatModel (a : Fr) : Nat → Fr
  | 0 => one
  | e + 1 => a * powNatModel a e

private theorem toZMod_powNatModel (a : Fr) (e : Nat) :
    toZMod (powNatModel a e) = toZMod a ^ e := by
  induction e with
  | zero => exact Montgomery.toZMod_one.trans (pow_zero _).symm
  | succ e ih => rw [powNatModel, toZMod_mul, ih, pow_succ']

/-- Square-and-multiply computes repeated multiplication. -/
theorem powNat_eq_powNatModel (a : Fr) (e : Nat) :
    powNat a e = powNatModel a e :=
  toZMod_injective (by rw [toZMod_powNat, toZMod_powNatModel])

theorem powNat_succ (a : Fr) (e : Nat) : powNat a (e + 1) = a * powNat a e := by
  rw [powNat_eq_powNatModel, powNat_eq_powNatModel, powNatModel]

/-- Decoding the 32 bytes of an element gives it back. -/
theorem fromBytesBE_toBytesBE (a : Fr) : fromBytesBE a.toBytesBE = .ok a := by
  unfold fromBytesBE
  have hs : a.toBytesBE.size = 32 := Montgomery.toBytesBE_size a
  rw [hs]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  rw [show a.toBytesBE = Montgomery.toBytesBE a from rfl, Montgomery.ofBytesBE_toBytesBE]

/-- The big-endian fold of the bytes is the integer they write. -/
theorem fromBytesBEAux_eq (acc : Nat) (l : List UInt8) :
    fromBytesBEAux acc l = l.foldl (fun acc b => acc * 256 + b.toNat) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons b rest ih =>
    rw [fromBytesBEAux, ih, List.foldl_cons, ← Nat.shiftLeft_add_eq_or_of_lt b.toNat_lt,
      Nat.shiftLeft_eq]

/-- A successful `fromBytesBE` implies: the input was 32 bytes, the value
is the big-endian decoding, and the value is canonical. -/
theorem fromBytesBE_ok {b : ByteArray} {f : Fr}
    (h : fromBytesBE b = .ok f) :
    b.size = 32 ∧ f.val = fromBytesBEAux 0 b.data.toList ∧
      f.val < modulus := by
  rw [fromBytesBE] at h
  split at h
  · cases h
  · rename_i hsz
    have hs : b.size = 32 := by omega
    have hl : (List.ofFn (n := 32) fun k => b[0 + k.val]!) = b.data.toList := by
      apply List.ext_getElem (by simp [hs])
      intro i h1 h2
      simp only [List.getElem_ofFn, Nat.zero_add, Array.getElem_toList]
      rw [getElem!_pos b i (by simp at h1; omega)]
      rfl
    rw [Montgomery.ofBytesBE_eq, hl] at h
    by_cases hlt : Base.bytesToNat b.data.toList < params.p
    · simp only [hlt, ↓reduceIte] at h
      cases h
      refine ⟨hs, ?_, val_lt _⟩
      rw [show Montgomery.ofNat _ = ofNat _ from rfl, val_ofNat_of_lt hlt, fromBytesBEAux_eq]
      rfl
    · simp only [hlt, ↓reduceIte] at h
      cases h

/-- `powNat` always produces a canonical value. -/
protected theorem powNat_val_lt (a : Fr) (e : Nat) :
    (powNat a e).val < modulus :=
  val_lt _

/-- `a^(m + n) = a^m * a^n`. -/
theorem powNat_add (a : Fr) (m n : Nat) :
    powNat a (m + n) = powNat a m * powNat a n :=
  toZMod_injective (by rw [toZMod_mul, toZMod_powNat, toZMod_powNat, toZMod_powNat, pow_add])

/-- `a^(m * n) = (a^m)^n`. -/
theorem powNat_mul (a : Fr) (m n : Nat) :
    powNat a (m * n) = powNat (powNat a m) n :=
  toZMod_injective (by rw [toZMod_powNat, toZMod_powNat, toZMod_powNat, pow_mul])

end EthLib.Cryptography.Bls.Fr
