module

public import EthLib.Cryptography.Bls.HashToCurve
public import EthLib.Cryptography.Proofs.Bls.Fp2

/-!
# Proofs: the square root of a ratio in `Fp2`

Source: RFC 9380, Appendix F.2.1.

For `v ≠ 0`, the flag tells whether `u / v` is a square in `Fp2`.

The root squares to `u / v` when it is, and to `Z u / v` when it is not.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

/-- `x^(2k + 1)`, with `k = (p - 3) / 4`, is `x^((p - 1) / 2)`, and its square is 1 for `x ≠ 0`. -/
private theorem euler_sq {x : ZMod Fp.modulus} (hx : x ≠ 0) :
    (x ^ rootExponent * x ^ rootExponent * x) * (x ^ rootExponent * x ^ rootExponent * x) = 1 := by
  have h := ZMod.pow_card_sub_one_eq_one hx
  rw [show Fp.modulus - 1 = 4 * rootExponent + 2 by decide] at h
  rw [← h]
  ring

/-- On a nonzero square, `x^((p - 1) / 2)` is 1. -/
private theorem euler_of_sq {y : ZMod Fp.modulus} (hy : y ≠ 0) :
    (y * y) ^ rootExponent * (y * y) ^ rootExponent * (y * y) = 1 := by
  have h := ZMod.pow_card_sub_one_eq_one hy
  rw [show Fp.modulus - 1 = 4 * rootExponent + 2 by decide] at h
  rw [← h]
  ring

/-- The constant is a square root of `-N(Z)`, the negated norm of `Z`. -/
theorem sqrtNegNormZ_sq : (sqrtNegNormZ : Fp) * sqrtNegNormZ = -Fp2.norm Z := by
  decide_eq_at_model [sqrtNegNormZ, Z]

/-- The root squares as claimed, and no root of `u / v` exists when the flag is not set. -/
private theorem sqrtRatio_spec {u v : Fp2} (hv : v ≠ 0) :
    ((sqrtRatio u v).2 * (sqrtRatio u v).2 =
      if (sqrtRatio u v).1 then u / v else Z * (u / v)) ∧
    ((sqrtRatio u v).1 = false → ∀ y, y * y ≠ u / v) := by
  simp only [sqrtRatio, Fp.baseField_isZero, Fp.baseField_powNat, Fp.baseField_beq,
    Fp.baseField_one]
  obtain ⟨nu, hnu⟩ : ∃ nu, u.c0 * u.c0 + u.c1 * u.c1 = nu := ⟨_, rfl⟩
  obtain ⟨nv, hnv⟩ : ∃ nv, v.c0 * v.c0 + v.c1 * v.c1 = nv := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α, nu * nv = α := ⟨_, rfl⟩
  simp only [hnu, hnv, hα]
  -- The norms, in `ZMod p`.
  have hNu : Fp.toZMod (Fp2.norm u) = Fp.toZMod nu := by
    rw [← hnu, Fp2.norm]
  have hNv : Fp.toZMod (Fp2.norm v) = Fp.toZMod nv := by
    rw [← hnv, Fp2.norm]
  have hα' : Fp.toZMod α = Fp.toZMod nu * Fp.toZMod nv := by
    rw [← hα, Fp.toZMod_mul]
  have hnv0 : Fp.toZMod nv ≠ 0 := by
    rw [← hNv, ← Fp.toZMod_zero, Ne, Fp.toZMod_inj]
    exact (Fp2.norm_ne_zero_iff v).mpr hv
  by_cases h0 : α.isZero = true
  · -- `α = 0`: then `u = 0`, and the root 0 squares to `u / v = 0`.
    simp only [h0, ↓reduceIte, Bool.true_eq_false, IsEmpty.forall_iff, and_true]
    have hu : u = 0 := by
      rw [← Fp2.norm_eq_zero_iff, ← Fp.toZMod_inj, hNu, Fp.toZMod_zero]
      have h := congrArg Fp.toZMod (Fp.isZero_iff.mp h0)
      rw [hα', Fp.toZMod_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hnv0
    rw [hu, Fp2.zero_eq_zero, zero_div, mul_zero]
  · -- `α ≠ 0`: `e = r^2 α` is 1 or -1, with `r = α^((p - 3) / 4)`.
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    have hα0 : Fp.toZMod α ≠ 0 := fun h =>
      h0 (Fp.isZero_iff.mpr (Fp.toZMod_inj.mp (h.trans Fp.toZMod_zero.symm)))
    obtain ⟨r, hr⟩ : ∃ r, α.powNat rootExponent = r := ⟨_, rfl⟩
    simp only [hr]
    have hR : Fp.toZMod r = Fp.toZMod α ^ rootExponent := by
      rw [← hr, Fp.toZMod_powNat]
    have hEE : Fp.toZMod r * Fp.toZMod r * Fp.toZMod α * (Fp.toZMod r * Fp.toZMod r * Fp.toZMod α)
        = 1 := by
      rw [hR]
      exact euler_sq hα0
    -- `1 / v = conj(v) / N(v)`, and `1 / N(v) = N(u) r^2 e`.
    have hinv : (Fp2.conjugate v).mulFp (nu * (r * r) * (r * r * α)) = v⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      apply Fp2.ext <;> apply Fp.toZMod.injective <;>
        simp only [Fp2.mul_c0, Fp2.mul_c1, Cryptography.Fp2.mulFp_c0, Cryptography.Fp2.mulFp_c1,
          Fp2.conjugate_c0, Fp2.conjugate_c1, Fp2.one_c0, Fp2.one_c1] <;> push_toZMod
      · have hnvZ := congrArg Fp.toZMod hnv
        push_toZMod at hnvZ
        linear_combination Fp.toZMod nu * Fp.toZMod r ^ 4 * Fp.toZMod α * hnvZ -
          Fp.toZMod r ^ 4 * Fp.toZMod α * hα' + hEE
      · ring
    simp only [hinv]
    have hNuv : Fp.toZMod (Fp2.norm (u * v)) = Fp.toZMod α := by
      rw [Fp2.norm_mul, Fp.toZMod_mul, hNu, hNv, hα']
    have hvv : v * v⁻¹ = 1 := mul_inv_cancel₀ hv
    by_cases h3 : (r * r * α).beq 1 = true
    · -- `e = 1`: `r α` is a root of `α = N(u v)`.
      --
      -- So the root of `u v`, over `v`, is a root of `u / v`.
      simp only [h3, ↓reduceIte, Bool.true_eq_false, IsEmpty.forall_iff, and_true]
      have he := congrArg Fp.toZMod (Fp.beq_iff.mp h3)
      push_toZMod at he
      have hw := Fp2.sqrtOfNormRoot_mul_self (a := u * v) (s := r * α) (by
        apply Fp.toZMod.injective
        rw [hNuv]
        push_toZMod
        linear_combination Fp.toZMod α * he)
      rw [div_eq_mul_inv]
      linear_combination v⁻¹ * v⁻¹ * hw + u * v⁻¹ * hvv
    · -- `e = -1`: `sqrt(-N(Z)) r α` is a root of `N(Z) α = N(Z u v)`.
      have he : Fp.toZMod r * Fp.toZMod r * Fp.toZMod α = -1 := by
        have hne : Fp.toZMod r * Fp.toZMod r * Fp.toZMod α - 1 ≠ 0 := by
          intro h
          apply h3
          apply Fp.beq_iff.mpr
          apply Fp.toZMod.injective
          push_toZMod
          linear_combination h
        exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp (by linear_combination hEE :
          (Fp.toZMod r * Fp.toZMod r * Fp.toZMod α - 1) *
            (Fp.toZMod r * Fp.toZMod r * Fp.toZMod α + 1) = 0)).resolve_left hne)
      rw [Bool.not_eq_true] at h3
      simp only [h3, Bool.false_eq_true, ↓reduceIte, forall_const]
      constructor
      · have hS := congrArg Fp.toZMod sqrtNegNormZ_sq
        push_toZMod at hS
        have hw := Fp2.sqrtOfNormRoot_mul_self (a := Z * (u * v)) (s := sqrtNegNormZ * (r * α)) (by
          apply Fp.toZMod.injective
          rw [Fp2.norm_mul]
          push_toZMod
          rw [hNuv]
          linear_combination (Fp.toZMod r * Fp.toZMod α) ^ 2 * hS -
            Fp.toZMod (Fp2.norm Z) * Fp.toZMod α * he)
        rw [div_eq_mul_inv]
        linear_combination v⁻¹ * v⁻¹ * hw + Z * u * v⁻¹ * hvv
      · -- A root `y` of `u / v` makes `α = (N(y) N(v))^2` a square, so `e = 1`.
        intro y hy
        have hu : u = y * y * v := by
          rw [hy, div_mul_cancel₀ u hv]
        have hNy := congrArg (fun x => Fp.toZMod (Fp2.norm x)) hu
        simp only [Fp2.norm_mul, Fp.toZMod_mul, hNu, hNv] at hNy
        have hαT : Fp.toZMod α = (Fp.toZMod (Fp2.norm y) * Fp.toZMod nv) *
            (Fp.toZMod (Fp2.norm y) * Fp.toZMod nv) := by
          rw [hα', hNy]
          ring
        have hT : Fp.toZMod (Fp2.norm y) * Fp.toZMod nv ≠ 0 := by
          intro h
          rw [h, mul_zero] at hαT
          exact hα0 hαT
        have h1 := euler_of_sq hT
        rw [← hαT, ← hR] at h1
        have h2 : (r * r * α).beq 1 = true := by
          apply Fp.beq_iff.mpr
          apply Fp.toZMod.injective
          push_toZMod
          exact h1
        rw [h3] at h2
        exact Bool.false_ne_true h2

/-- For `v ≠ 0`, the flag of the square root of `u / v` is set exactly when `u / v` is a square. -/
theorem sqrtRatio_fst {u v : Fp2} (hv : v ≠ 0) :
    (sqrtRatio u v).1 = true ↔ ∃ y, y * y = u / v := by
  constructor
  · intro h
    have hs := (sqrtRatio_spec (u := u) hv).1
    simp only [h, ↓reduceIte] at hs
    exact ⟨_, hs⟩
  · rintro ⟨y, hy⟩
    by_contra hc
    exact (sqrtRatio_spec hv).2 (Bool.not_eq_true _ ▸ hc) y hy

/-- For `v ≠ 0`, the root squares to `u / v` when the flag is set, and to `Z u / v` otherwise. -/
theorem sqrtRatio_snd {u v : Fp2} (hv : v ≠ 0) :
    (sqrtRatio u v).2 * (sqrtRatio u v).2 =
      if (sqrtRatio u v).1 then u / v else Z * (u / v) :=
  (sqrtRatio_spec hv).1

end EthLib.Cryptography.Bls.HashToCurve
