module

public import EthLib.Cryptography.Secp256k1.Ecdh
public import EthLib.Cryptography.Proofs.Secp256k1.Recovery

/-!
# Proofs: ECDH over secp256k1

Two parties with keys `a` and `b` derive the same secret: `a (b G) = b (a G)`.

The equality holds for every pair of keys, the zero key included, with the same error.

Two nonzero keys always derive a secret.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open Point

/-- The scalars of a multiple of `G` commute: `a (b G) = b (a G)`. -/
theorem mul_mul_generator_comm (a b : Fn) :
    mul a (mul b generator) = mul b (mul a generator) := by
  have hG := isOnCurve_generator
  apply (toPoint_inj (isOnCurve_mul _ (isOnCurve_mul _ hG))
    (isOnCurve_mul _ (isOnCurve_mul _ hG))).mp
  rw [toPoint_mul' _ (isOnCurve_mul _ hG), toPoint_mul' _ hG, toPoint_mul' _ (isOnCurve_mul _ hG),
    toPoint_mul' _ hG, smul_smul, smul_smul, mul_comm]

/-- `0 P = O`, for every point of the curve. -/
theorem mul_zero_left {p : Point} (hp : p.isOnCurve = true) : mul 0 p = .infinity := by
  apply (toPoint_eq_zero (isOnCurve_mul _ hp)).mp
  rw [toPoint_mul' _ hp]
  simp

/-- `k O = O`. -/
private theorem mul_infinity (k : Fn) : mul k .infinity = .infinity := by
  apply (toPoint_eq_zero (isOnCurve_mul _ rfl)).mp
  rw [toPoint_mul' _ rfl]
  simp

/-- A multiple of `G` is `O` exactly for the scalar zero. -/
private theorem mul_generator_eq_infinity (k : Fn) : mul k generator = .infinity ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    exact Ecdsa.mul_generator_ne_infinity hk h
  · rintro rfl
    exact mul_zero_left isOnCurve_generator

/-- The two parties of an exchange derive the same secret, or the same error. -/
theorem ecdh_comm (a b : Fn) : ecdh a (mul b generator) = ecdh b (mul a generator) := by
  have hG := isOnCurve_generator
  unfold ecdh
  simp only [isOnCurve_mul _ hG, Bool.not_true, Bool.false_eq_true, ite_false,
    mul_generator_eq_infinity, mul_mul_generator_comm a b]
  -- With a zero key, both sides reject the point at infinity.
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 0
    · subst hb; rfl
    · simp only [hb, ite_false, ite_true, mul_zero_left hG, mul_infinity]
  · by_cases hb : b = 0
    · subst hb
      simp only [ha, ite_false, ite_true, mul_zero_left (isOnCurve_mul _ hG)]
    · simp only [ha, hb, ite_false]

/-- `k P` is not `O`, for a nonzero `k` and a point `P` of the curve other than `O`. -/
theorem mul_ne_infinity {k : Fn} (hk : k ≠ 0) {p : Point} (hp : p.isOnCurve = true)
    (hinf : p ≠ .infinity) : mul k p ≠ .infinity := by
  intro h
  have h0 := (toPoint_eq_zero (isOnCurve_mul _ hp)).mpr h
  rw [toPoint_mul' _ hp, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hk (Fn.toZMod.injective (by simpa using h0))
  · exact hinf ((toPoint_eq_zero hp).mp h0)

/-- Two nonzero keys always derive a secret. -/
theorem exists_ecdh_eq_ok {a b : Fn} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ secret, ecdh a (mul b generator) = .ok secret := by
  have hG := isOnCurve_generator
  have hP := Ecdsa.mul_generator_ne_infinity hb
  unfold ecdh
  simp only [hP, isOnCurve_mul _ hG, Bool.not_true, Bool.false_eq_true, ite_false]
  cases hm : mul a (mul b generator) with
  | infinity => exact absurd hm (mul_ne_infinity ha (isOnCurve_mul _ hG) hP)
  | affine x y => exact ⟨_, rfl⟩

end EthLib.Cryptography.Secp256k1
