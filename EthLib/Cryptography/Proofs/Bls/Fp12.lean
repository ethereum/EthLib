import EthLib.Cryptography.Bls.Fp12
import EthLib.Cryptography.Proofs.Bls.Fp6

/-!
# Proofs: `Fp12`

`Fp12` is the quadratic extension `Fp6[w] / (w^2 - v)`.

This file proves that it is a field, with the library's own operations.

Every element `a = c0 + c1*w` has a norm `c0^2 - v*c1^2` in `Fp6`.

The norm is zero only at zero, because `v` is not a square in `Fp6`.

Taking norms twice more sends `v` to `2` in `Fp`.

And `2` is not a square in `Fp`, because `p = 3 mod 8`.

It also proves that the library's exponentiation is the field power.
-/

namespace EthLib.Cryptography.Bls.Fp12

/-! ## Extensionality and coordinate projections -/

@[ext]
theorem ext {a b : Fp12} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

instance : Zero Fp12 := ⟨zero⟩
instance : One Fp12 := ⟨one⟩

@[simp] theorem zero_eq_zero : zero = (0 : Fp12) := rfl
@[simp] theorem one_eq_one : one = (1 : Fp12) := rfl

@[simp] theorem zero_c0 : (0 : Fp12).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp12).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp12).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp12).c1 = 0 := rfl

@[simp] theorem add_c0 (a b : Fp12) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp12) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp12) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp12) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp12) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp12) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp12) : (a * b).c0 = a.c0 * b.c0 + (a.c1 * b.c1).mulByV := rfl
@[simp] theorem mul_c1 (a b : Fp12) :
    (a * b).c1 = (a.c0 + a.c1) * (b.c0 + b.c1) - a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem conjugate_c0 (a : Fp12) : a.conjugate.c0 = a.c0 := rfl
@[simp] theorem conjugate_c1 (a : Fp12) : a.conjugate.c1 = -a.c1 := rfl

/-! ## Boolean equality and one check -/

theorem beq_iff_eq {a b : Fp12} : a.beq b = true ↔ a = b := by
  rw [beq, Bool.and_eq_true, Fp6.beq_iff_eq, Fp6.beq_iff_eq]
  exact ⟨fun ⟨h0, h1⟩ => ext h0 h1, fun h => ⟨congrArg c0 h, congrArg c1 h⟩⟩

theorem isOne_iff {a : Fp12} : a.isOne = true ↔ a = 1 := by
  rw [isOne, Bool.and_eq_true, Fp6.beq_iff_eq, Fp6.isZero_iff, Fp6.one_eq_one]
  exact ⟨fun ⟨h0, h1⟩ => ext h0 h1, fun h => ⟨congrArg c0 h, congrArg c1 h⟩⟩

instance : LawfulBEq Fp12 where
  eq_of_beq {a b} h := by
    cases a; cases b
    change (_ && _) = true at h
    rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq] at h
    exact ext h.1 h.2
  rfl {a} := by
    cases a
    change (_ && _) = true
    simp

instance : DecidableEq Fp12 := fun a b =>
  if h : a.beq b then isTrue (beq_iff_eq.mp h)
  else isFalse (fun heq => h (beq_iff_eq.mpr heq))

/-! ## Ring axioms, `AddCommGroup Fp12`, and `CommRing Fp12` -/

protected theorem add_comm (a b : Fp12) : a + b = b + a := by
  apply ext <;> simp <;> ring

protected theorem add_assoc (a b c : Fp12) : a + b + c = a + (b + c) := by
  apply ext <;> simp <;> ring

protected theorem zero_add (a : Fp12) : 0 + a = a := by
  apply ext <;> simp

protected theorem add_zero (a : Fp12) : a + 0 = a := by
  apply ext <;> simp

protected theorem neg_add_cancel (a : Fp12) : -a + a = 0 := by
  apply ext <;> simp

protected theorem sub_eq_add_neg (a b : Fp12) : a - b = a + -b := by
  apply ext <;> simp [_root_.sub_eq_add_neg]

protected theorem mul_comm (a b : Fp12) : a * b = b * a := by
  apply ext <;> simp <;> ring

protected theorem mul_assoc (a b c : Fp12) : a * b * c = a * (b * c) := by
  apply ext <;> simp <;> ring

protected theorem one_mul (a : Fp12) : 1 * a = a := by
  apply ext <;> simp

protected theorem mul_one (a : Fp12) : a * 1 = a := by
  apply ext <;> simp

protected theorem zero_mul (a : Fp12) : 0 * a = 0 := by
  apply ext <;> simp

protected theorem mul_zero (a : Fp12) : a * 0 = 0 := by
  apply ext <;> simp

protected theorem left_distrib (a b c : Fp12) : a * (b + c) = a * b + a * c := by
  apply ext <;> simp <;> ring

protected theorem right_distrib (a b c : Fp12) : (a + b) * c = a * c + b * c := by
  apply ext <;> simp <;> ring

instance : AddCommGroup Fp12 where
  add_assoc := Fp12.add_assoc
  zero_add := Fp12.zero_add
  add_zero := Fp12.add_zero
  neg_add_cancel := Fp12.neg_add_cancel
  add_comm := Fp12.add_comm
  sub_eq_add_neg := Fp12.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : CommRing Fp12 where
  left_distrib := Fp12.left_distrib
  right_distrib := Fp12.right_distrib
  zero_mul := Fp12.zero_mul
  mul_zero := Fp12.mul_zero
  mul_assoc := Fp12.mul_assoc
  one_mul := Fp12.one_mul
  mul_one := Fp12.mul_one
  mul_comm := Fp12.mul_comm

/-! ## Conjugation, norm over `Fp6`, and `Fp12.inverse` soundness -/

@[simp]
theorem conjugate_conjugate (a : Fp12) : a.conjugate.conjugate = a := by
  apply ext <;> simp

theorem conjugate_add (a b : Fp12) : (a + b).conjugate = a.conjugate + b.conjugate := by
  apply ext
  · simp
  · simp; ring

theorem conjugate_sub (a b : Fp12) : (a - b).conjugate = a.conjugate - b.conjugate := by
  apply ext
  · simp
  · simp; ring

theorem conjugate_neg (a : Fp12) : (-a).conjugate = -a.conjugate := by
  apply ext <;> simp

theorem conjugate_mul (a b : Fp12) : (a * b).conjugate = a.conjugate * b.conjugate := by
  apply ext
  · simp
  · simp; ring

/-- The norm `N(c0 + c1*w) = c0^2 - v*c1^2`, an element of `Fp6`.

It equals `a * conjugate a`, and it is the denominator of the library's inverse.
-/
def norm (a : Fp12) : Fp6 := a.c0 * a.c0 - (a.c1 * a.c1).mulByV

theorem mul_conjugate (a : Fp12) : a * a.conjugate = ⟨norm a, 0⟩ := by
  apply ext <;> simp [norm] <;> ring

theorem conjugate_mul_self (a : Fp12) : a.conjugate * a = ⟨norm a, 0⟩ := by
  rw [Fp12.mul_comm, mul_conjugate]

private theorem norm_mul_aux (a0 a1 b0 b1 v : Fp6) :
    (a0 * b0 + a1 * b1 * v) * (a0 * b0 + a1 * b1 * v) -
      ((a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1) *
        ((a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1) * v =
      (a0 * a0 - a1 * a1 * v) * (b0 * b0 - b1 * b1 * v) := by
  ring

theorem norm_mul (a b : Fp12) : norm (a * b) = norm a * norm b := by
  simp only [norm, mul_c0, mul_c1, Fp6.mulByV_eq]
  exact norm_mul_aux a.c0 a.c1 b.c0 b.c1 Fp6.v

@[simp] theorem norm_zero : norm 0 = 0 := by simp [norm]
@[simp] theorem norm_one : norm 1 = 1 := by simp [norm]

/-! ## `v` is not a square, so the norm is zero only at zero -/

open scoped EthLib.Cryptography.Bls.Fp in
set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
private theorem sq_ne_two_zmod (z : ZMod Fp.modulus) : z * z ≠ 2 := by
  -- If `z^2 = 2`, then `2^((p-1)/2) = z^(p-1) = 1`, which the kernel refutes.
  intro h
  have h2 : z ^ 2 = ((2 : Nat) : ZMod Fp.modulus) := by
    have h2' : (2 : ZMod Fp.modulus) = ((2 : Nat) : ZMod Fp.modulus) := rfl
    rw [← h2']
    linear_combination h
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at h
    revert h; decide
  have hfermat : z ^ (Fp.modulus - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hz
  rw [show Fp.modulus - 1 = 2 * ((Fp.modulus - 1) / 2) by decide,
    pow_mul, h2] at hfermat
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 2 2
    (by decide) (by decide) hfermat

open scoped EthLib.Cryptography.Bls.Fp in
private theorem sq_eq_two_mul_sq_zmod {u w nxi : ZMod Fp.modulus}
    (hnxi : nxi = 2) (h : u * u = w * w * nxi) : w = 0 := by
  by_contra hw
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  rw [hnxi] at h
  have hsq : (u * w⁻¹) * (u * w⁻¹) = 2 := by
    linear_combination (w⁻¹ * w⁻¹) * h + 2 * (w * w⁻¹ + 1) * hinv
  exact sq_ne_two_zmod (u * w⁻¹) hsq

private theorem sq_eq_v_mul_sq {x y : Fp6} (h : x * x = y * y * Fp6.v) : y = 0 := by
  -- Two norms, to `Fp2` and then to `Fp`, send `v` to `2`.
  -- So `M(x)^2 = M(y)^2 * 2` in `Fp`, where `M` is the composed norm, and `M(y) = 0`.
  have hnorm : Fp2.norm (Fp6.norm (x * x)) = Fp2.norm (Fp6.norm (y * y * Fp6.v)) :=
    congrArg (fun z => Fp2.norm (Fp6.norm z)) h
  simp only [Fp6.norm_mul, Fp6.norm_v, Fp2.norm_mul] at hnorm
  have hy0 : Fp2.norm (Fp6.norm y) = 0 :=
    sq_eq_two_mul_sq_zmod (u := Fp2.norm (Fp6.norm x)) (w := Fp2.norm (Fp6.norm y))
      (nxi := Fp2.norm Fp2.xi) rfl hnorm
  exact (Fp6.norm_eq_zero_iff y).mp ((Fp2.norm_eq_zero_iff (Fp6.norm y)).mp hy0)

/-- The norm is zero only at zero. -/
theorem norm_eq_zero_iff (a : Fp12) : norm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    simp only [norm, Fp6.mulByV_eq, sub_eq_zero] at h
    have hc1 : a.c1 = 0 := sq_eq_v_mul_sq h
    have hc0_sq : a.c0 * a.c0 = 0 := by
      linear_combination h + a.c1 * Fp6.v * hc1
    have hc0 : a.c0 = 0 := mul_self_eq_zero.mp hc0_sq
    exact ext hc0 hc1
  · rintro rfl
    exact norm_zero

theorem norm_ne_zero_iff (a : Fp12) : norm a ≠ 0 ↔ a ≠ 0 :=
  not_congr (norm_eq_zero_iff a)

private theorem mul_inverse_c0_aux (a0 a1 v invN : Fp6)
    (hnorm : (a0 * a0 - a1 * a1 * v) * invN = 1) :
    a0 * (a0 * invN) + a1 * -(a1 * invN) * v = 1 := by
  linear_combination hnorm

private theorem mul_inverse_c1_aux (a0 a1 invN : Fp6) :
    (a0 + a1) * (a0 * invN + -(a1 * invN)) - a0 * (a0 * invN) - a1 * -(a1 * invN) = 0 := by
  ring

private theorem inverse_eq (a : Fp12) :
    a.inverse = ⟨a.c0 * (norm a).inverse, -(a.c1 * (norm a).inverse)⟩ := rfl

private theorem mul_inverse_aux (a : Fp12) (invN : Fp6) (h : norm a * invN = 1) :
    a * ⟨a.c0 * invN, -(a.c1 * invN)⟩ = 1 := by
  have hnorm : (a.c0 * a.c0 - a.c1 * a.c1 * Fp6.v) * invN = 1 := by
    simpa only [norm, Fp6.mulByV_eq] using h
  refine ext ?_ ?_
  · simp only [mul_c0, Fp6.mulByV_eq, one_c0]
    exact mul_inverse_c0_aux a.c0 a.c1 Fp6.v invN hnorm
  · simp only [mul_c1, one_c1]
    exact mul_inverse_c1_aux a.c0 a.c1 invN

theorem mul_inverse_of_norm_invertible {a : Fp12} (h : norm a * (norm a).inverse = 1) :
    a * a.inverse = 1 := by
  rw [inverse_eq]
  exact mul_inverse_aux a (norm a).inverse h

theorem mul_inverse_of_norm_ne_zero {a : Fp12} (h : Fp6.norm (norm a) ≠ 0) :
    a * a.inverse = 1 :=
  mul_inverse_of_norm_invertible (Fp6.mul_inverse_of_norm_ne_zero h)

theorem inverse_mul_of_norm_ne_zero {a : Fp12} (h : Fp6.norm (norm a) ≠ 0) :
    a.inverse * a = 1 := by
  rw [Fp12.mul_comm, mul_inverse_of_norm_ne_zero h]

theorem mul_inverse_cancel {a : Fp12} (h : a ≠ 0) : a * a.inverse = 1 :=
  mul_inverse_of_norm_invertible (Fp6.mul_inverse_cancel ((norm_ne_zero_iff a).mpr h))

theorem inverse_mul_cancel {a : Fp12} (h : a ≠ 0) : a.inverse * a = 1 := by
  rw [Fp12.mul_comm, mul_inverse_cancel h]

@[simp]
theorem inverse_zero : (0 : Fp12).inverse = 0 := by
  rw [inverse_eq, norm_zero, Fp6.inverse_zero]
  apply ext <;> simp

instance : Field Fp12 where
  inv := inverse
  exists_pair_ne := ⟨0, 1, fun h => by
    have := congrArg (fun x => x.c0.c0.c0) h
    revert this; decide⟩
  mul_inv_cancel := fun _ h => mul_inverse_cancel h
  inv_zero := inverse_zero
  nnqsmul := _
  qsmul := _

/-! ## Exponentiation (`powNat`) -/

theorem powNat_eq_pow (a : Fp12) (e : Nat) : powNat a e = a ^ e := by
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

theorem powNat_zero (a : Fp12) : powNat a 0 = one := by
  rw [powNat_eq_pow, pow_zero, one_eq_one]

theorem powNat_one (a : Fp12) : powNat a 1 = a := by
  rw [powNat_eq_pow, pow_one]

theorem powNat_succ (a : Fp12) (e : Nat) : powNat a (e + 1) = a * powNat a e := by
  rw [powNat_eq_pow, powNat_eq_pow, pow_succ']

end EthLib.Cryptography.Bls.Fp12
