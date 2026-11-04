module

public import EthLib.Cryptography.AltBn128.Pairing
public import EthLib.Cryptography.Proofs.AltBn128.Field
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.LinearCombination

/-!
# Proofs: `Fp2` of alt_bn128

`Fp2` is `Fp[i] / (i^2 + 1)`, and it is a field with the operations of the specification.

The norm `c0^2 + c1^2` of `c0 + c1 i` is zero only at zero.

That holds because `-1` is not a square mod `p`, since `p = 3 mod 4`.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128.Fp2

/-! ## Components -/

@[ext]
theorem ext {a b : Fp2} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

instance : Zero Fp2 := ⟨⟨0, 0⟩⟩
instance : One Fp2 := ⟨⟨1, 0⟩⟩

@[simp] theorem zero_c0 : (0 : Fp2).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2).c1 = 0 := rfl
@[simp] theorem ofFp_c0 (x : Fp) : (ofFp x).c0 = x := rfl
@[simp] theorem ofFp_c1 (x : Fp) : (ofFp x).c1 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp2) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp2) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp2) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp2) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

/-! ## The ring

Each law is a polynomial identity on the two components in `Fp`. -/

section Ring

open scoped Fin.CommRing

/-- `n` as an element of `Fp2`: the element `n` of `Fp`. -/
instance : NatCast Fp2 := ⟨fun n => ofFp n⟩

/-- `n` as an element of `Fp2`: the element `n` of `Fp`. -/
instance : IntCast Fp2 := ⟨fun n => ofFp n⟩

@[simp] theorem natCast_c0 (n : Nat) : (n : Fp2).c0 = n := rfl
@[simp] theorem natCast_c1 (n : Nat) : (n : Fp2).c1 = 0 := rfl
@[simp] theorem intCast_c0 (n : Int) : (n : Fp2).c0 = n := rfl
@[simp] theorem intCast_c1 (n : Int) : (n : Fp2).c1 = 0 := rfl

instance : CommRing Fp2 where
  add_assoc _ _ _ := by apply ext <;> simp <;> ring
  zero_add _ := by apply ext <;> simp
  add_zero _ := by apply ext <;> simp
  add_comm _ _ := by apply ext <;> simp <;> ring
  neg_add_cancel _ := by apply ext <;> simp
  sub_eq_add_neg _ _ := by apply ext <;> simp [sub_eq_add_neg]
  mul_assoc _ _ _ := by apply ext <;> simp <;> ring
  one_mul _ := by apply ext <;> simp
  mul_one _ := by apply ext <;> simp
  zero_mul _ := by apply ext <;> simp
  mul_zero _ := by apply ext <;> simp
  left_distrib _ _ _ := by apply ext <;> simp <;> ring
  right_distrib _ _ _ := by apply ext <;> simp <;> ring
  mul_comm _ _ := by apply ext <;> simp <;> ring
  natCast_zero := by apply ext <;> simp
  natCast_succ _ := by apply ext <;> simp
  intCast_ofNat _ := by apply ext <;> simp
  intCast_negSucc _ := by apply ext <;> simp [Int.negSucc_eq]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The element `i`. -/
def i : Fp2 := ⟨0, 1⟩

theorem i_mul_i : i * i = -1 := by
  apply ext <;> simp [i]

/-- The constant `2` of the twist addition is the numeral of `Fp2`. -/
@[simp] theorem ofFp_two : ofFp 2 = 2 := rfl

/-- The constant `3` of the twist addition is the numeral of `Fp2`. -/
@[simp] theorem ofFp_three : ofFp 3 = 3 := rfl

end Ring

/-! ## The inverse -/

-- Euler's criterion evaluates a 256-bit power in the kernel, deeper than the default.
set_option maxRecDepth 8000 in
/-- `-1` is not a square in `Fp`, because `p = 3 mod 4`. -/
theorem mul_self_ne_neg_one (y : ZMod Fp.modulus) : y * y ≠ -1 := by
  intro h
  have hy : y ≠ 0 := by
    rintro rfl
    exact absurd h (by decide)
  -- `y^2 = -1` gives `(-1)^((p - 1) / 2) = y^(p - 1) = 1`.
  have hpow : ((Fp.modulus - 1 : Nat) : ZMod Fp.modulus) ^ ((Fp.modulus - 1) / 2) = 1 := by
    rw [show ((Fp.modulus - 1 : Nat) : ZMod Fp.modulus) = -1 by decide, ← h, ← pow_two, ← pow_mul,
      show 2 * ((Fp.modulus - 1) / 2) = Fp.modulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one hy
  -- The kernel computes that power, and it is `-1`, not `1`.
  rw [PowMod.natCast_pow_eq_one_iff _ 256 _ _ (by decide)] at hpow
  exact absurd hpow (by decide)

/-- The norm `c0^2 + c1^2` is zero only at zero. -/
theorem norm_eq_zero {c0 c1 : ZMod Fp.modulus} (h : c0 * c0 + c1 * c1 = 0) : c0 = 0 ∧ c1 = 0 := by
  by_cases hc1 : c1 = 0
  · subst hc1
    exact ⟨mul_self_eq_zero.mp (by simpa using h), rfl⟩
  · -- Division by `c1^2` gives `(c0 / c1)^2 = -1`, which has no solution.
    refine absurd ?_ (mul_self_ne_neg_one (c0 * c1⁻¹))
    have hinv : c1 * c1⁻¹ = 1 := mul_inv_cancel₀ hc1
    linear_combination (c1⁻¹ * c1⁻¹) * h - (c1 * c1⁻¹ + 1) * hinv

theorem mul_inv_cancel' {a : Fp2} (h : a ≠ 0) : a * a.inv = 1 := by
  have hn : Fp.toZMod (a.c0 * a.c0 + a.c1 * a.c1) ≠ 0 := fun hn =>
    h (ext (norm_eq_zero hn).1 (norm_eq_zero hn).2)
  -- With `w = 1 / N(a)`, the product is `(c0^2 + c1^2) w + (c1 c0 - c0 c1) w i`.
  have hw := mul_inv_cancel₀ hn
  rw [← Fp.toZMod_inv] at hw
  rw [inv]
  generalize (a.c0 * a.c0 + a.c1 * a.c1).inv = w at hw ⊢
  apply ext
  · simp only [mul_c0, one_c0]
    apply Fp.toZMod.injective
    simp only [map_add, map_sub, map_mul, Fp.toZMod_neg, Fp.toZMod_one] at hw ⊢
    linear_combination hw
  · simp only [mul_c1, one_c1]
    apply Fp.toZMod.injective
    simp only [map_add, map_mul, Fp.toZMod_neg, Fp.toZMod_zero]
    ring

theorem inv_zero' : (0 : Fp2).inv = 0 := by
  apply ext <;> simp [inv]

instance instField : Field Fp2 where
  inv := inv
  exists_pair_ne := ⟨0, 1, fun h => absurd (congrArg c0 h) (by decide)⟩
  mul_inv_cancel _ h := mul_inv_cancel' h
  inv_zero := inv_zero'
  nnqsmul := _
  qsmul := _

/-- The inverse of the specification is the field inverse. -/
@[simp] theorem inv_eq_inv (a : Fp2) : a.inv = a⁻¹ := rfl

/-! ## Powers -/

/-- Square and multiply computes `a^e`, when `e < 2^fuel`. -/
theorem powBits_eq_pow (fuel : Nat) (a : Fp2) (e : Nat) (he : e < 2 ^ fuel) :
    powBits fuel a e = a ^ e := by
  induction fuel generalizing a e with
  | zero =>
    obtain rfl : e = 0 := by simpa using he
    rfl
  | succ fuel ih =>
    have h2 : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at he; omega
    -- `a^e = a^(e mod 2) * (a^2)^(e / 2)`.
    rw [powBits, ih _ _ h2, ← pow_two, ← pow_mul]
    split <;> [rw [← pow_succ']; skip] <;> congr 1 <;> omega

end EthLib.Cryptography.AltBn128.Fp2
