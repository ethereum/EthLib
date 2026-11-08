module

public import EthLib.Cryptography.Proofs.Bls.CofactorAlgebra

/-!
# Proofs: the endomorphism `psi` of the twist satisfies `psi^4 - psi^2 + 1 = 0`

The subgroup check of `G2` tests `psi(Q) = [t] Q`, after Scott.
<https://eprint.iacr.org/2021/1130>

This file proves the fact on `psi` that makes the test imply `[r] Q = 0`.

- `psi` applied twice is `(x, y) ↦ (c x, -y)`, where `c` is a cube root of unity other than `1`.
- So `-psi^2` is `(x, y) ↦ (c x, y)`, and `Q`, `-psi^2(Q)`, `psi^4(Q)` lie on the line `Y = y`.
- They sum to `O`, so `Q - psi^2(Q) + psi^4(Q) = 0` for every point `Q` of the twist.
- If `psi(Q) = [-n] Q`, this gives `[n^4 - n^2 + 1] Q = 0`, and `t^4 - t^2 + 1 = r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve HashToCurve TwistFrobenius

/-- The constant of `psi2` is not `1`. -/
theorem c1Psi2_ne_one : (c1Psi2 : Fp2) ≠ 1 := by
  decide_eq_at_model [map_c1Psi2]

/-- The constant of `psi2` is a root of `1 + X + X^2`, since it is a cube root of unity. -/
theorem one_add_c1Psi2_add_sq : 1 + (c1Psi2 : Fp2) + c1Psi2 ^ 2 = 0 := by
  have h : ((c1Psi2 : Fp2) - 1) * (1 + c1Psi2 + c1Psi2 ^ 2) = 0 := by
    linear_combination c1Psi2_cube
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr c1Psi2_ne_one)

/-- Scaling `(x, y)` to `(x u^2, y u^3)` with `u^6 = 1` keeps a point on the twist. -/
private theorem nonsingular_scale {x y u : Fp2} (h : curve.toAffine.Nonsingular x y)
    (hu : u ^ 6 = 1) : curve.toAffine.Nonsingular (x * u ^ 2) (y * u ^ 3) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  exact ShortWeierstrass.scaled_nonsingular (RingHom.id Fp2) u hu0
    (by rw [RingHom.id_apply, hu, mul_one]) h

/-- `(c x, y)` and `(c x, -y)` are on the twist when `(x, y)` is. -/
theorem nonsingular_c1Psi2 {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.Nonsingular (c1Psi2 * x) y ∧ curve.toAffine.Nonsingular (c1Psi2 * x) (-y) := by
  have hc := c1Psi2_cube
  have hx : x * ((c1Psi2 : Fp2) ^ 2) ^ 2 = c1Psi2 * x := by
    linear_combination x * c1Psi2 * hc
  have hx' : x * (-(c1Psi2 : Fp2) ^ 2) ^ 2 = c1Psi2 * x := by
    linear_combination x * c1Psi2 * hc
  have h12 : (c1Psi2 : Fp2) ^ 12 = 1 := by
    rw [show 12 = 3 * 4 from rfl, pow_mul, hc, one_pow]
  have h1 := nonsingular_scale h (u := (c1Psi2 : Fp2) ^ 2)
    (by rw [show ((c1Psi2 : Fp2) ^ 2) ^ 6 = c1Psi2 ^ 12 by ring]; exact h12)
  have h2 := nonsingular_scale h (u := -(c1Psi2 : Fp2) ^ 2)
    (by rw [show (-(c1Psi2 : Fp2) ^ 2) ^ 6 = c1Psi2 ^ 12 by ring]; exact h12)
  have hy : y * ((c1Psi2 : Fp2) ^ 2) ^ 3 = y := by
    linear_combination y * (c1Psi2 ^ 3 + 1) * hc
  have hy' : y * (-(c1Psi2 : Fp2) ^ 2) ^ 3 = -y := by
    linear_combination -y * (c1Psi2 ^ 3 + 1) * hc
  rw [hx, hy] at h1
  rw [hx', hy'] at h2
  exact ⟨h1, h2⟩

/-- `psi` applied twice is `(x, y) ↦ (c x, -y)`. -/
theorem hom_hom_some {x y : Fp2} (h : curve.toAffine.Nonsingular x y)
    (h' : curve.toAffine.Nonsingular (c1Psi2 * x) (-y)) :
    hom (hom (.some x y h)) = .some (c1Psi2 * x) (-y) h' := by
  simp only [hom_apply, mapPoint]
  apply ShortWeierstrass.some_congr
  · rw [Fp2.conjugate_mul, Fp2.conjugate_conjugate, ← mul_assoc, c1Psi_norm]
  · rw [Fp2.conjugate_mul, Fp2.conjugate_conjugate, ← mul_assoc, c2Psi_norm, neg_one_mul]

/-- `Q - psi^2(Q) + psi^4(Q) = 0`, since `Q`, `-psi^2(Q)` and `psi^4(Q)` lie on one line. -/
theorem add_neg_hom_hom_add (P : curve.toAffine.Point) :
    P + -hom (hom P) + hom (hom (hom (hom P))) = 0 := by
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, _root_.map_zero, _root_.map_zero, _root_.map_zero,
      _root_.map_zero, neg_zero, add_zero, add_zero]
  | some x y h =>
    obtain ⟨h₂, h₂'⟩ := nonsingular_c1Psi2 h
    obtain ⟨-, h₄⟩ := nonsingular_c1Psi2 h₂'
    rw [hom_hom_some h h₂', hom_hom_some h₂' h₄, Affine.Point.neg_some]
    have h₃ : curve.toAffine.Nonsingular ((c1Psi2 : Fp2) ^ 2 * x) y := by
      rw [neg_neg, ← mul_assoc, ← sq] at h₄
      exact h₄
    have hy : curve.toAffine.negY (c1Psi2 * x) (-y) = y := by
      change -(-y) - 0 * (c1Psi2 * x) - 0 = y
      ring
    rw [ShortWeierstrass.some_congr rfl hy _ h₂,
      ShortWeierstrass.some_congr (by ring) (neg_neg y) h₄ h₃]
    exact ShortWeierstrass.some_add_some_add_some one_add_c1Psi2_add_sq c1Psi2_ne_one h h₂ h₃

/-- Scott's criterion for `G2`: if `psi(Q) = [t] Q`, then `[r] Q = 0`.

Here `t = -|t|`, so `psi^2(Q) = [t^2] Q` and `psi^4(Q) = [t^4] Q`. -/
theorem modulus_smul_eq_zero_of_hom {P : curve.toAffine.Point}
    (h : hom P = -(blsX • P)) : Fr.modulus • P = 0 := by
  have h2 : hom (hom P) = (blsX * blsX) • P := by
    rw [h, _root_.map_neg, _root_.map_nsmul, h, neg_nsmul, neg_neg, smul_smul]
  have h4 : hom (hom (hom (hom P))) = ((blsX * blsX) * (blsX * blsX)) • P := by
    rw [h2, _root_.map_nsmul, _root_.map_nsmul, h2, smul_smul]
  have hs := add_neg_hom_hom_add P
  rw [h4, h2] at hs
  have hle : blsX * blsX ≤ blsX * blsX * (blsX * blsX) := Nat.le_mul_of_pos_right _ (by decide)
  rw [Fr.modulus_eq_blsX, show blsX ^ 4 - blsX ^ 2 + 1 =
      (blsX * blsX * (blsX * blsX) - blsX * blsX) + 1 by decide,
    add_nsmul, sub_nsmul P hle, one_nsmul, ← hs]
  abel

end EthLib.Cryptography.Bls.G2
