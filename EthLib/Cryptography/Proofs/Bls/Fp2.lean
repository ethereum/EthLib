module

public import EthLib.Cryptography.Bls.Fp2
public import EthLib.Cryptography.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.FpZMod
public import EthLib.Cryptography.Proofs.Bls.Compress
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Proofs: `Fp2`

`Fp2` is the quadratic extension `Fp[i] / (i^2 + 1)`.

This file proves that it is a field, with the library's own operations.

Every element `a = c0 + c1*i` has a norm `N(a) = c0^2 + c1^2` in `Fp`.

The norm is zero only at zero, because `-1` is not a square in `Fp`.

That holds since `p = 3 mod 4`, and it makes every nonzero element invertible.

It also proves that the library's exponentiation is the field power, and that a square root it returns squares back to its input.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Fp2

/-! ## Extensionality and basic projections -/

@[ext]
theorem ext {a b : Fp2} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

instance : Zero Fp2 := ⟨zero⟩
instance : One Fp2 := ⟨one⟩

@[simp] theorem zero_eq_zero : zero = (0 : Fp2) := rfl
@[simp] theorem one_eq_one : one = (1 : Fp2) := rfl

@[simp] theorem zero_c0 : (0 : Fp2).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2).c1 = 0 := rfl
@[simp] theorem i_c0 : i.c0 = 0 := rfl
@[simp] theorem i_c1 : i.c1 = 1 := rfl
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
@[simp] theorem conjugate_c0 (a : Fp2) : a.conjugate.c0 = a.c0 := rfl
@[simp] theorem conjugate_c1 (a : Fp2) : a.conjugate.c1 = -a.c1 := rfl

/-! ## Boolean equality and zero check -/

theorem beq_iff_eq {a b : Fp2} : a.beq b = true ↔ a = b := by
  rw [beq, Bool.and_eq_true, G1.beq_iff, G1.beq_iff]
  exact ⟨fun ⟨h0, h1⟩ => ext h0 h1, fun h => ⟨congrArg c0 h, congrArg c1 h⟩⟩

theorem isZero_iff {a : Fp2} : a.isZero = true ↔ a = 0 := by
  rw [isZero, Bool.and_eq_true, G1.isZero_iff, G1.isZero_iff]
  exact ⟨fun ⟨h0, h1⟩ => ext h0 h1, fun h => ⟨congrArg c0 h, congrArg c1 h⟩⟩

instance : LawfulBEq Fp2 where
  eq_of_beq {a b} h := by
    cases a; cases b
    change (_ && _) = true at h
    rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq] at h
    exact ext h.1 h.2
  rfl {a} := by
    cases a
    change (_ && _) = true
    simp

instance : DecidableEq Fp2 := fun a b =>
  if h : a.beq b then isTrue (beq_iff_eq.mp h)
  else isFalse (fun heq => h (beq_iff_eq.mpr heq))

/-! ## Ring axioms and `CommRing Fp2` -/

section FinRing
open scoped Fin.CommRing

protected theorem add_comm (a b : Fp2) : a + b = b + a := by
  apply ext <;> simp <;> ring

protected theorem add_assoc (a b c : Fp2) : a + b + c = a + (b + c) := by
  apply ext <;> simp <;> ring

protected theorem zero_add (a : Fp2) : 0 + a = a := by
  apply ext <;> simp

protected theorem add_zero (a : Fp2) : a + 0 = a := by
  apply ext <;> simp

protected theorem neg_add_cancel (a : Fp2) : -a + a = 0 := by
  apply ext <;> simp

protected theorem sub_eq_add_neg (a b : Fp2) : a - b = a + -b := by
  apply ext <;> simp [_root_.sub_eq_add_neg]

protected theorem mul_comm (a b : Fp2) : a * b = b * a := by
  apply ext <;> simp <;> ring

protected theorem mul_assoc (a b c : Fp2) : a * b * c = a * (b * c) := by
  apply ext <;> simp <;> ring

protected theorem one_mul (a : Fp2) : 1 * a = a := by
  apply ext <;> simp

protected theorem mul_one (a : Fp2) : a * 1 = a := by
  apply ext <;> simp

protected theorem zero_mul (a : Fp2) : 0 * a = 0 := by
  apply ext <;> simp

protected theorem mul_zero (a : Fp2) : a * 0 = 0 := by
  apply ext <;> simp

protected theorem left_distrib (a b c : Fp2) : a * (b + c) = a * b + a * c := by
  apply ext <;> simp <;> ring

protected theorem right_distrib (a b c : Fp2) : (a + b) * c = a * c + b * c := by
  apply ext <;> simp <;> ring

instance : AddCommGroup Fp2 where
  add_assoc := Fp2.add_assoc
  zero_add := Fp2.zero_add
  add_zero := Fp2.add_zero
  neg_add_cancel := Fp2.neg_add_cancel
  add_comm := Fp2.add_comm
  sub_eq_add_neg := Fp2.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : CommRing Fp2 where
  left_distrib := Fp2.left_distrib
  right_distrib := Fp2.right_distrib
  zero_mul := Fp2.zero_mul
  mul_zero := Fp2.mul_zero
  mul_assoc := Fp2.mul_assoc
  one_mul := Fp2.one_mul
  mul_one := Fp2.mul_one
  mul_comm := Fp2.mul_comm

/-! ## Basis, non-residue, conjugation, and norm -/

theorem i_sq : i * i = -1 := by
  apply ext <;> simp

/-- The element `xi = 1 + i`.

It is not a cube in `Fp2`, so `Fp6` adjoins a cube root of it.
-/
def xi : Fp2 := ⟨1, 1⟩

@[simp]
theorem mulByOnePlusI_eq (a : Fp2) : a.mulByOnePlusI = a * xi := by
  apply ext <;> simp [mulByOnePlusI, xi]

theorem conjugate_add (a b : Fp2) : (a + b).conjugate = a.conjugate + b.conjugate := by
  apply ext
  · simp
  · simp; ring

theorem conjugate_sub (a b : Fp2) : (a - b).conjugate = a.conjugate - b.conjugate := by
  apply ext
  · simp
  · simp; ring

theorem conjugate_neg (a : Fp2) : (-a).conjugate = -a.conjugate := by
  apply ext <;> simp

theorem conjugate_mul (a b : Fp2) : (a * b).conjugate = a.conjugate * b.conjugate := by
  apply ext
  · simp
  · simp; ring

@[simp]
theorem conjugate_conjugate (a : Fp2) : a.conjugate.conjugate = a := by
  apply ext <;> simp

/-- The norm `N(c0 + c1*i) = c0^2 + c1^2`, an element of `Fp`.

It equals `a * conjugate a`, and it is multiplicative.
-/
def norm (a : Fp2) : Fp := a.c0 * a.c0 + a.c1 * a.c1

theorem mul_conjugate_eq_norm (a : Fp2) : a * a.conjugate = ofFp (norm a) := by
  apply ext
  · simp [norm]
  · simp; ring

theorem conjugate_mul_eq_norm (a : Fp2) : a.conjugate * a = ofFp (norm a) := by
  rw [Fp2.mul_comm, mul_conjugate_eq_norm]

theorem norm_mul (a b : Fp2) : norm (a * b) = norm a * norm b := by
  simp only [norm, mul_c0, mul_c1]
  ring

@[simp] theorem norm_zero : norm 0 = 0 := by simp [norm]
@[simp] theorem norm_one : norm 1 = 1 := by simp [norm]
@[simp] theorem norm_conjugate (a : Fp2) : norm a.conjugate = norm a := by
  simp [norm]

end FinRing

open scoped EthLib.Cryptography.Bls.Fp

/-! ## Non-squareness of `-1` in `Fp` and `Fp2.inverse` correctness -/

set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
private theorem sq_ne_neg_one_zmod (y : ZMod Fp.modulus) : y * y ≠ -1 := by
  -- Euler's criterion: if `y^2 = -1`, then `(-1)^((p-1)/2) = y^(p-1) = 1`.
  -- The kernel computes `(-1)^((p-1)/2) mod p` and finds `p - 1`, not `1`.
  intro h
  have h2 : y ^ 2 = ((Fp.modulus - 1 : Nat) : ZMod Fp.modulus) := by
    have hm1 : (-1 : ZMod Fp.modulus) = ((Fp.modulus - 1 : Nat) : ZMod Fp.modulus) := by decide
    rw [← hm1]
    linear_combination h
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at h
    revert h; decide
  have hfermat : y ^ (Fp.modulus - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hy
  rw [show Fp.modulus - 1 = 2 * ((Fp.modulus - 1) / 2) by decide,
    pow_mul, h2] at hfermat
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 (Fp.modulus - 1) 2
    (by decide) (by decide) hfermat

/-- `-1` is not a square in `Fp`, because `p = 3 mod 4`. -/
theorem sq_ne_neg_one (y : Fp) : y * y ≠ -1 :=
  sq_ne_neg_one_zmod y

private theorem norm_eq_zero_zmod {c0 c1 : ZMod Fp.modulus}
    (h : c0 * c0 + c1 * c1 = 0) : c0 = 0 ∧ c1 = 0 := by
  by_cases hc1 : c1 = 0
  · have hc0 : c0 * c0 = 0 := by linear_combination h - c1 * hc1
    exact ⟨mul_self_eq_zero.mp hc0, hc1⟩
  -- With `c1 /= 0`, dividing by `c1^2` makes `(c0 / c1)^2 = -1`, which has no solution.
  · exfalso
    have hinv : c1 * c1⁻¹ = 1 := mul_inv_cancel₀ hc1
    have hsq : (c0 * c1⁻¹) * (c0 * c1⁻¹) = -1 := by
      linear_combination (c1⁻¹ * c1⁻¹) * h - (c1 * c1⁻¹ + 1) * hinv
    exact sq_ne_neg_one_zmod (c0 * c1⁻¹) hsq

/-- The norm is zero only at zero. -/
theorem norm_eq_zero_iff (a : Fp2) : norm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := norm_eq_zero_zmod (c0 := a.c0) (c1 := a.c1) h
    exact ext h0 h1
  · rintro rfl
    exact norm_zero

theorem norm_ne_zero_iff (a : Fp2) : norm a ≠ 0 ↔ a ≠ 0 :=
  not_congr (norm_eq_zero_iff a)

private theorem mul_inv_c0_zmod (c0 c1 w : ZMod Fp.modulus)
    (hw : (c0 * c0 + c1 * c1) * w = 1) :
    c0 * (c0 * w) - c1 * -(c1 * w) = 1 := by
  linear_combination hw

private theorem mul_inv_c1_zmod (c0 c1 w : ZMod Fp.modulus) :
    c0 * -(c1 * w) + c1 * (c0 * w) = 0 := by
  ring

open scoped EthLib.Cryptography.Bls.Fp in
private theorem fp_mul_inverse {x : Fp} (hx : x ≠ 0) :
    (x : ZMod Fp.modulus) * (x.inverse : ZMod Fp.modulus) = 1 := by
  rw [Fp.inverse_eq_inv]
  exact mul_inv_cancel₀ hx

theorem mul_inverse_of_norm_ne_zero {a : Fp2} (h : norm a ≠ 0) :
    a * a.inverse = 1 := by
  have hinv := fp_mul_inverse h
  exact ext (mul_inv_c0_zmod a.c0 a.c1 (norm a).inverse hinv)
    (mul_inv_c1_zmod a.c0 a.c1 (norm a).inverse)

theorem mul_inverse_cancel {a : Fp2} (h : a ≠ 0) : a * a.inverse = 1 :=
  mul_inverse_of_norm_ne_zero ((norm_ne_zero_iff a).mpr h)

theorem inverse_mul_cancel {a : Fp2} (h : a ≠ 0) : a.inverse * a = 1 := by
  rw [Fp2.mul_comm, mul_inverse_cancel h]

@[simp]
theorem inverse_zero : (0 : Fp2).inverse = 0 := by
  apply ext <;> simp [inverse, Fin.zero_mul]

instance : Field Fp2 where
  inv := inverse
  exists_pair_ne := ⟨0, 1, fun h => by
    have := congrArg c0 h
    revert this; decide⟩
  mul_inv_cancel := fun a h => mul_inverse_cancel h
  inv_zero := inverse_zero
  div_eq_mul_inv := fun _ _ => rfl
  nnqsmul := _
  qsmul := _

/-! ## Exponentiation (`powNat`) -/

theorem powNat_eq_pow (a : Fp2) (e : Nat) : powNat a e = a ^ e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [powNat]
    split
    · rename_i h
      subst h
      rw [pow_zero, one_eq_one]
    · rename_i h
      rw [ih (e / 2) (by omega)]
      by_cases h2 : e % 2 = 1
      · rw [ite_eq_left h2, ← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · rw [ite_eq_right h2, ← pow_two, ← pow_mul]
        congr 1
        omega

theorem powNat_zero (a : Fp2) : powNat a 0 = one := by
  rw [powNat_eq_pow, pow_zero, one_eq_one]

theorem powNat_one (a : Fp2) : powNat a 1 = a := by
  rw [powNat_eq_pow, pow_one]

theorem powNat_succ (a : Fp2) (e : Nat) : powNat a (e + 1) = a * powNat a e := by
  rw [powNat_eq_pow, powNat_eq_pow, pow_succ']

/-! ## Square-root soundness (`Fp2.sqrt`) -/

private theorem c0_ne_zero_zmod {a0 a1 s' c0 inv2 : ZMod Fp.modulus}
    (ha1 : a1 ≠ 0)
    (hs : s' * s' = a0 * a0 + a1 * a1)
    (h2inv : (2 : ZMod Fp.modulus) * inv2 = 1)
    (hc0 : c0 * c0 = (a0 + s') * inv2) :
    (2 : ZMod Fp.modulus) * c0 ≠ 0 := by
  have h2ne : (2 : ZMod Fp.modulus) ≠ 0 := by decide
  have hc0_2 : 2 * (c0 * c0) = a0 + s' := by
    linear_combination 2 * hc0 + (a0 + s') * h2inv
  have hc0_ne : c0 ≠ 0 := by
    intro hc00
    have h0 : a0 + s' = 0 := by
      linear_combination -hc0_2 + 2 * c0 * hc00
    have ha1_sq : a1 * a1 = 0 := by
      linear_combination -hs + (s' - a0) * h0
    exact ha1 (mul_self_eq_zero.mp ha1_sq)
  exact mul_ne_zero h2ne hc0_ne

private theorem sqrt_c0_zmod {a0 a1 s' c0 w inv2 : ZMod Fp.modulus}
    (hs : s' * s' = a0 * a0 + a1 * a1)
    (h2inv : (2 : ZMod Fp.modulus) * inv2 = 1)
    (hc0 : c0 * c0 = (a0 + s') * inv2)
    (h2c0_inv : (2 * c0) * w = 1) :
    c0 * c0 - (a1 * w) * (a1 * w) = a0 := by
  have hc0_2 : 2 * (c0 * c0) = a0 + s' := by
    linear_combination 2 * hc0 + (a0 + s') * h2inv
  linear_combination
    w * w * hs
    + w * w * (2 * c0 * c0 - a0 + s') * hc0_2
    - (c0 * c0 - a0) * (2 * c0 * w + 1) * h2c0_inv

private theorem sqrt_c1_zmod {a1 c0 w : ZMod Fp.modulus}
    (h2c0_inv : (2 * c0) * w = 1) :
    c0 * (a1 * w) + (a1 * w) * c0 = a1 := by
  linear_combination a1 * h2c0_inv

private theorem neg_sq_eq_zero_sub {s a0 : ZMod Fp.modulus}
    (h : s * s = -a0) : (0 : ZMod Fp.modulus) * 0 - s * s = a0 := by
  linear_combination -h

private theorem sqrt_c0_sub_zmod {a0 a1 s' c0 w inv2 : ZMod Fp.modulus}
    (hs : s' * s' = a0 * a0 + a1 * a1)
    (h2inv : (2 : ZMod Fp.modulus) * inv2 = 1)
    (hc0 : c0 * c0 = (a0 - s') * inv2)
    (h2c0_inv : (2 * c0) * w = 1) :
    c0 * c0 - (a1 * w) * (a1 * w) = a0 := by
  have hc0_2 : 2 * (c0 * c0) = a0 - s' := by
    linear_combination 2 * hc0 + (a0 - s') * h2inv
  linear_combination
    w * w * hs
    + w * w * (2 * c0 * c0 - a0 - s') * hc0_2
    - (c0 * c0 - a0) * (2 * c0 * w + 1) * h2c0_inv

private theorem c0_ne_zero_sub_zmod {a0 a1 s' c0 inv2 : ZMod Fp.modulus}
    (ha1 : a1 ≠ 0)
    (hs : s' * s' = a0 * a0 + a1 * a1)
    (h2inv : (2 : ZMod Fp.modulus) * inv2 = 1)
    (hc0 : c0 * c0 = (a0 - s') * inv2) :
    (2 : ZMod Fp.modulus) * c0 ≠ 0 := by
  have h2ne : (2 : ZMod Fp.modulus) ≠ 0 := by decide
  have hc0_2 : 2 * (c0 * c0) = a0 - s' := by
    linear_combination 2 * hc0 + (a0 - s') * h2inv
  have hc0_ne : c0 ≠ 0 := by
    intro hc00
    have h0 : a0 - s' = 0 := by
      linear_combination -hc0_2 + 2 * c0 * hc00
    have ha1_sq : a1 * a1 = 0 := by
      linear_combination -hs - (s' + a0) * h0
    exact ha1 (mul_self_eq_zero.mp ha1_sq)
  exact mul_ne_zero h2ne hc0_ne

-- `sqrt.match_1` is the matcher of the library's `Fp2.sqrt`, named on purpose so the
-- statement matches that definition's unfolding.
set_option linter.auxLemma false in
private theorem c0Opt_eq_ok {s a0 twoInv c0Fp : Fp}
    (h : sqrt.match_1 (fun _ => Except BlsError Fp) (Fp.sqrt ((a0 + s) * twoInv))
          (fun _ => Fp.sqrt ((a0 + s) * twoInv))
          (fun _ => Fp.sqrt ((a0 - s) * twoInv)) = .ok c0Fp) :
    Fp.sqrt ((a0 + s) * twoInv) = .ok c0Fp ∨
      Fp.sqrt ((a0 - s) * twoInv) = .ok c0Fp := by
  cases h1 : Fp.sqrt ((a0 + s) * twoInv) with
  | ok _ =>
    rw [h1] at h
    exact Or.inl h
  | error _ =>
    rw [h1] at h
    exact Or.inr h

private theorem two_mul_inverse :
    (Fp.ofNat 2 : ZMod Fp.modulus) * ((Fp.ofNat 2).inverse : ZMod Fp.modulus) = 1 :=
  fp_mul_inverse (by decide)

private theorem sqrt_branch_gen_aux {invFn : Fp → Fp}
    (hinv : ∀ x : Fp, x ≠ 0 → (x : ZMod Fp.modulus) * (invFn x : ZMod Fp.modulus) = 1)
    {a0 a1 s' c0 inv2 : Fp}
    (ha1 : a1 ≠ 0)
    (hs : (s' : ZMod Fp.modulus) * s' = a0 * a0 + a1 * a1)
    (h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * (inv2 : ZMod Fp.modulus) = 1)
    (hc0 : (c0 : ZMod Fp.modulus) * c0 = (a0 + s') * inv2) :
    let w := invFn (Fp.ofNat 2 * c0)
    (⟨c0, a1 * w⟩ : Fp2) * ⟨c0, a1 * w⟩ = ⟨a0, a1⟩ := by
  intro w
  have h2c0_ne : (Fp.ofNat 2 * c0 : Fp) ≠ 0 :=
    c0_ne_zero_zmod ha1 hs h2inv hc0
  have h2c0_inv : ((Fp.ofNat 2 * c0 : Fp) : ZMod Fp.modulus) * (w : ZMod Fp.modulus) = 1 :=
    hinv (Fp.ofNat 2 * c0) h2c0_ne
  exact ext (sqrt_c0_zmod hs h2inv hc0 h2c0_inv) (sqrt_c1_zmod h2c0_inv)

private theorem sqrt_branch_sub_gen_aux {invFn : Fp → Fp}
    (hinv : ∀ x : Fp, x ≠ 0 → (x : ZMod Fp.modulus) * (invFn x : ZMod Fp.modulus) = 1)
    {a0 a1 s' c0 inv2 : Fp}
    (ha1 : a1 ≠ 0)
    (hs : (s' : ZMod Fp.modulus) * s' = a0 * a0 + a1 * a1)
    (h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * (inv2 : ZMod Fp.modulus) = 1)
    (hc0 : (c0 : ZMod Fp.modulus) * c0 = (a0 - s') * inv2) :
    let w := invFn (Fp.ofNat 2 * c0)
    (⟨c0, a1 * w⟩ : Fp2) * ⟨c0, a1 * w⟩ = ⟨a0, a1⟩ := by
  intro w
  have h2c0_ne : (Fp.ofNat 2 * c0 : Fp) ≠ 0 :=
    c0_ne_zero_sub_zmod ha1 hs h2inv hc0
  have h2c0_inv : ((Fp.ofNat 2 * c0 : Fp) : ZMod Fp.modulus) * (w : ZMod Fp.modulus) = 1 :=
    hinv (Fp.ofNat 2 * c0) h2c0_ne
  exact ext (sqrt_c0_sub_zmod hs h2inv hc0 h2c0_inv) (sqrt_c1_zmod h2c0_inv)

-- The body names the library's generated matchers on purpose, as its docstring explains.
set_option linter.auxLemma false in
/-- The square root in `Fp2`, with the inverse function and the inverse of `2` as parameters.

Unfolding the square root directly makes the kernel recurse too deeply.

It tries to evaluate the inverses, which are exponentiations with a 381-bit exponent.

Here they are variables, so the case analysis never evaluates them.

The body copies the library definition with the same generated matchers.

So the library definition is this one applied to the real inverses, by definition.
-/
private def sqrtWith (invFn : Fp → Fp) (twoInvVal : Fp) (a : Fp2) : Except BlsError Fp2 :=
  if a.c1.isZero = true then
    sqrt.match_1 (fun _ => Except BlsError Fp2) a.c0.sqrt (fun s => Except.ok { c0 := s, c1 := Fp.zero }) fun _ =>
      sqrt.match_1 (fun _ => Except BlsError Fp2) (-a.c0).sqrt (fun s => Except.ok { c0 := Fp.zero, c1 := s }) fun _ =>
        Except.error BlsError.notASquare
  else
    have n := a.c0 * a.c0 + a.c1 * a.c1
    sqrt.match_3 (fun _ => Except BlsError Fp2) n.sqrt (fun _ => Except.error BlsError.notASquare) fun s =>
      have twoInv := twoInvVal
      have try1 := ((a.c0 + s) * twoInv).sqrt
      have c0Opt :=
        sqrt.match_1 (fun _ => Except BlsError Fp) try1 (fun _ => try1) fun _ => ((a.c0 - s) * twoInv).sqrt
      sqrt.match_3 (fun _ => Except BlsError Fp2) c0Opt (fun _ => Except.error BlsError.notASquare) fun c0Fp =>
        have c1Fp := a.c1 * invFn (Fp.ofNat 2 * c0Fp)
        Except.ok { c0 := c0Fp, c1 := c1Fp }

private theorem sqrtWith_ok {invFn : Fp → Fp} {twoInv : Fp}
    (hinv : ∀ x : Fp, x ≠ 0 → (x : ZMod Fp.modulus) * (invFn x : ZMod Fp.modulus) = 1)
    (h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * (twoInv : ZMod Fp.modulus) = 1)
    {a c : Fp2} (h : sqrtWith invFn twoInv a = .ok c) : c * c = a := by
  unfold sqrtWith at h
  split at h
  · rename_i hc1z
    have hc1 : a.c1 = 0 := G1.isZero_iff.mp hc1z
    split at h
    · rename_i s hs
      cases h
      have hsq : s * s = a.c0 := Fp.sqrt_ok hs
      refine ext ?_ ?_
      · show s * s - 0 * 0 = a.c0
        rw [Fin.mul_zero, sub_zero, hsq]
      · show s * 0 + 0 * s = a.c1
        rw [Fin.mul_zero, Fin.zero_mul, hc1]
        rfl
    · split at h
      · rename_i s hs
        cases h
        have hsq : (s : ZMod Fp.modulus) * s = -a.c0 := Fp.sqrt_ok hs
        refine ext ?_ ?_
        · exact neg_sq_eq_zero_sub hsq
        · show (0 : Fp) * s + s * 0 = a.c1
          rw [Fin.zero_mul, Fin.mul_zero, hc1]
          rfl
      · cases h
  · rename_i hc1nz
    have hc1 : a.c1 ≠ 0 := fun h0 => hc1nz (G1.isZero_iff.mpr h0)
    dsimp only at h
    split at h
    · cases h
    · rename_i s hs
      have hnsq : (s : ZMod Fp.modulus) * s = a.c0 * a.c0 + a.c1 * a.c1 := Fp.sqrt_ok hs
      split at h
      · cases h
      · rename_i c0Fp hc0Opt
        cases h
        rcases c0Opt_eq_ok hc0Opt with htry1 | htry2
        · exact sqrt_branch_gen_aux hinv hc1 hnsq h2inv (Fp.sqrt_ok htry1)
        · exact sqrt_branch_sub_gen_aux hinv hc1 hnsq h2inv (Fp.sqrt_ok htry2)

/-- Soundness of `Fp2.sqrt`: if `Fp2.sqrt a = .ok c`, then `c * c = a`. -/
theorem sqrt_ok {a c : Fp2} (h : Fp2.sqrt a = .ok c) : c * c = a :=
  sqrtWith_ok (fun _ hx => fp_mul_inverse hx) two_mul_inverse h

/-! ## Sign-bit flip and square-root completeness -/

/-- Negating a nonzero `Fp2` element flips its sign bit (`draft-irtf-cfrg-pairing-friendly-curves-07` Appendix C).

When `c1 != 0`, the sign comes from `c1`, which is negated.

When `c1 = 0`, `c0` is nonzero, and the sign comes from `c0`, which is negated.
-/
theorem signBit_neg {y : Fp2} (hy : y ≠ 0) :
    Fp2.signBit (-y) = !Fp2.signBit y := by
  unfold Fp2.signBit
  -- Negation preserves whether the imaginary part is zero.
  have hc1_zero : (-y).c1.isZero = y.c1.isZero := by
    rw [Bool.eq_iff_iff, G1.isZero_iff, G1.isZero_iff, Fp2.neg_c1, neg_eq_zero]
  rw [hc1_zero]
  by_cases hc1 : y.c1.isZero = true
  -- When c1 = 0, a nonzero element has c0 != 0, so signBit inspects c0.
  · simp only [hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Fp2.neg_c0]
    have hc1_eq : y.c1 = 0 := G1.isZero_iff.mp hc1
    have hc0_ne : y.c0 ≠ 0 := fun hc0_eq => hy (Fp2.ext hc0_eq hc1_eq)
    exact G1.signBit_neg hc0_ne
  -- When c1 != 0, signBit inspects c1 directly.
  · simp only [hc1, Bool.not_false, ↓reduceIte, Fp2.neg_c1]
    have hc1_ne : y.c1 ≠ 0 := fun hc1_eq => hc1 (G1.isZero_iff.mpr hc1_eq)
    exact G1.signBit_neg hc1_ne

private theorem c1_zero_factors_zmod {b0 b1 : ZMod Fp.modulus}
    (h : b0 * b1 + b1 * b0 = 0) : b0 = 0 ∨ b1 = 0 := by
  -- 2 is invertible modulo p, so 2 * b0 * b1 = 0 forces b0 = 0 or b1 = 0.
  have h2 : (2 : ZMod Fp.modulus) * (b0 * b1) = 0 := by linear_combination h
  have h2ne : (2 : ZMod Fp.modulus) ≠ 0 := by decide
  exact mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2ne)

private theorem norm_sq_zmod (b0 b1 : ZMod Fp.modulus) :
    (b0 * b0 + b1 * b1) * (b0 * b0 + b1 * b1) =
      (b0 * b0 - b1 * b1) * (b0 * b0 - b1 * b1) +
      (b0 * b1 + b1 * b0) * (b0 * b1 + b1 * b0) := by
  ring

private theorem sq_pm_zmod {s n : ZMod Fp.modulus} (h : s * s = n * n) :
    s = n ∨ s = -n := by
  -- Factor s^2 - n^2 as (s - n) * (s + n) over the prime field.
  have hfac : (s - n) * (s + n) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

private theorem neg_sub_zero_mul_zmod {a0 b0 b1 : ZMod Fp.modulus}
    (ha0 : a0 = b0 * b0 - b1 * b1) (hb0 : b0 = 0) :
    b1 * b1 = -a0 := by
  subst hb0
  linear_combination ha0

private theorem sub_zero_mul_zmod {a0 b0 b1 : ZMod Fp.modulus}
    (ha0 : a0 = b0 * b0 - b1 * b1) (hb1 : b1 = 0) :
    b0 * b0 = a0 := by
  subst hb1
  linear_combination -ha0

private theorem half_add_norm_zmod {a0 b0 b1 s twoInv : ZMod Fp.modulus}
    (h2 : (2 : ZMod Fp.modulus) * twoInv = 1)
    (ha0 : a0 = b0 * b0 - b1 * b1)
    (hs : s = b0 * b0 + b1 * b1) :
    b0 * b0 = (a0 + s) * twoInv := by
  linear_combination -b0 * b0 * h2 - twoInv * ha0 - twoInv * hs

private theorem half_sub_norm_zmod {a0 b0 b1 s twoInv : ZMod Fp.modulus}
    (h2 : (2 : ZMod Fp.modulus) * twoInv = 1)
    (ha0 : a0 = b0 * b0 - b1 * b1)
    (hs : s = -(b0 * b0 + b1 * b1)) :
    b0 * b0 = (a0 - s) * twoInv := by
  linear_combination -b0 * b0 * h2 - twoInv * ha0 + twoInv * hs

-- `sqrt.match_1` matches the inner fallback branch of `Fp2.sqrt` without unfolding `Fp.inverse`.
set_option linter.auxLemma false in
private theorem sqrtWith_complete {invFn : Fp → Fp} {twoInv : Fp}
    (h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * (twoInv : ZMod Fp.modulus) = 1)
    {a b : Fp2} (hb : b * b = a) :
    ∃ c, sqrtWith invFn twoInv a = .ok c := by
  have ha0 : (a.c0 : ZMod Fp.modulus) = b.c0 * b.c0 - b.c1 * b.c1 := by rw [← hb]; rfl
  have ha1 : (a.c1 : ZMod Fp.modulus) = b.c0 * b.c1 + b.c1 * b.c0 := by rw [← hb]; rfl
  unfold sqrtWith
  split
  · rename_i hc1z
    -- When a.c1 = 0, we have 2 * b0 * b1 = 0, so either b0 = 0 or b1 = 0.
    have hc1 : (a.c1 : ZMod Fp.modulus) = 0 := G1.isZero_iff.mp hc1z
    rw [ha1] at hc1
    rcases c1_zero_factors_zmod hc1 with hb0 | hb1
    -- Purely imaginary root: b1^2 = -a0, so either a0.sqrt or (-a0).sqrt succeeds.
    · have hna0 : (b.c1 : ZMod Fp.modulus) * b.c1 = (-a.c0 : Fp) :=
        neg_sub_zero_mul_zmod ha0 hb0
      have hs2 := Fp.sqrt_complete hna0
      cases hs1 : a.c0.sqrt with
      | ok s => exact ⟨⟨s, Fp.zero⟩, rfl⟩
      | error _ =>
        rw [hs2]
        exact ⟨⟨Fp.zero, _⟩, rfl⟩
    -- Purely real root: b0^2 = a0, so the first Fp.sqrt succeeds directly.
    · have ha0' : (b.c0 : ZMod Fp.modulus) * b.c0 = a.c0 :=
        sub_zero_mul_zmod ha0 hb1
      rw [Fp.sqrt_complete ha0']
      exact ⟨⟨_, Fp.zero⟩, rfl⟩
  · dsimp only
    -- When a.c1 != 0, N(b) = b0^2 + b1^2 is a square root of N(a) = a0^2 + a1^2.
    have hnsq : ((b.c0 * b.c0 + b.c1 * b.c1 : Fp) : ZMod Fp.modulus) *
        (b.c0 * b.c0 + b.c1 * b.c1 : Fp) = a.c0 * a.c0 + a.c1 * a.c1 := by
      rw [ha0, ha1]
      exact norm_sq_zmod b.c0 b.c1
    have hsqrt_n := Fp.sqrt_complete hnsq
    rw [hsqrt_n]
    dsimp only
    -- The norm root s equals +(b0^2 + b1^2) or -(b0^2 + b1^2), so (a0 + s)/2 or (a0 - s)/2 equals b0^2.
    have hs_sq : (Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4) : ZMod Fp.modulus) *
        Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4) =
        ((b.c0 * b.c0 + b.c1 * b.c1 : Fp) : ZMod Fp.modulus) * (b.c0 * b.c0 + b.c1 * b.c1 : Fp) := by
      rw [Fp.sqrt_ok hsqrt_n, ← hnsq]
    rcases sq_pm_zmod hs_sq with hs_pos | hs_neg
    -- Positive norm root: (a0 + s) / 2 = b0^2, so try1 succeeds.
    · have htry1_sq : (b.c0 : ZMod Fp.modulus) * b.c0 =
          (a.c0 + Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)) * twoInv :=
        half_add_norm_zmod h2inv ha0 hs_pos
      rw [Fp.sqrt_complete htry1_sq]
      exact ⟨_, rfl⟩
    -- Negative norm root: (a0 - s) / 2 = b0^2, so the fallback succeeds if try1 fails.
    · have htry2_sq : (b.c0 : ZMod Fp.modulus) * b.c0 =
          (a.c0 - Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)) * twoInv :=
        half_sub_norm_zmod h2inv ha0 hs_neg
      cases htry1 : ((a.c0 + Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)) * twoInv).sqrt with
      | ok s1 => exact ⟨_, rfl⟩
      | error _ =>
        dsimp only [sqrt.match_1]
        rw [Fp.sqrt_complete htry2_sq]
        exact ⟨_, rfl⟩

/-- Completeness of `Fp2.sqrt`: if `b * b = a`, then `Fp2.sqrt a` returns a root. -/
theorem sqrt_complete {a b : Fp2} (hb : b * b = a) :
    ∃ c, Fp2.sqrt a = .ok c :=
  sqrtWith_complete two_mul_inverse hb

end EthLib.Cryptography.Bls.Fp2
