module

public import EthLib.Cryptography.Secp256k1.Ecdh
public import EthLib.Cryptography.Proofs.Secp256k1.Recovery

/-!
# Proofs: ECDH over secp256k1

Two parties with keys `a` and `b` derive the same secret: `a (b G) = b (a G)`.

The equality holds for every pair of keys, the zero key included, with the same error.

Two nonzero keys always derive a secret.

The primitive returns `z` exactly when the key `Q` is a point other than `O` and `d` is nonzero.

Then `z` is the `x` of `d Q`, as 32 big-endian bytes.
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


/-- ECDH is the Diffie-Hellman primitive of SEC 1 v2 §3.3.1, read in the group of the curve.

The private key `d` is a scalar modulo `n`, by its type.

The primitive returns `z` exactly when these hold:

- the public key `Q` lies on the curve and is not `O`;
- `d` is not zero;
- `z` is the `x` of the point `d Q`, as 32 big-endian bytes.

The cofactor is 1, so no subgroup check is needed, and none is made.

The result is the raw shared secret; no key derivation function is applied to it. -/
theorem ecdh_eq_ok_iff {sk : Fn} {pk : Point} {z : Vector UInt8 32} :
    ecdh sk pk = .ok z ↔
      pk ≠ .infinity ∧ pk.isOnCurve = true ∧ sk ≠ 0 ∧
        ∃ x y : Fp, (Point.affine x y).isOnCurve = true ∧
          toPoint (.affine x y) = Fn.toZMod sk • toPoint pk ∧
          z.toList = Base.natToBytes 32 x.val := by
  constructor
  · intro h
    unfold ecdh at h
    by_cases hinf : pk = .infinity
    · simp [hinf] at h
    by_cases hc : pk.isOnCurve = true
    · simp only [hinf, hc, Bool.not_true, Bool.false_eq_true, ite_false] at h
      by_cases hk : sk = 0
      · subst hk
        rw [mul_zero_left hc] at h
        cases h
      refine ⟨hinf, hc, hk, ?_⟩
      cases hm : mul sk pk with
      | infinity => exact absurd hm (mul_ne_infinity hk hc hinf)
      | affine x y =>
        rw [hm] at h
        obtain rfl := Except.ok.inj h
        refine ⟨x, y, hm ▸ isOnCurve_mul _ hc, ?_, rfl⟩
        rw [← hm, toPoint_mul' _ hc]
    · simp [hinf, hc] at h
  · rintro ⟨hinf, hc, hk, x, y, hxy, hpt, hz⟩
    -- The computed point is `(x, y)`, since both have the image `d Q` in the group.
    have hm : mul sk pk = .affine x y :=
      (toPoint_inj (isOnCurve_mul _ hc) hxy).mp ((toPoint_mul' _ hc).trans hpt.symm)
    unfold ecdh
    simp only [hinf, hc, Bool.not_true, Bool.false_eq_true, ite_false, hm]
    congr 1
    apply Vector.toList_inj.mp
    rw [hz]
    rfl

end EthLib.Cryptography.Secp256k1
