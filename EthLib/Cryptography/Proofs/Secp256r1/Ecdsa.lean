module

public import EthLib.Cryptography.Proofs.Secp256r1.Order

/-!
# Proofs: ECDSA verification over secp256r1

A signature from the signing operation of SEC 1 v2 §4.1.3 verifies.

A valid signature has `r` and `s` in `[1, n - 1]`, under a key on the curve other than `O`.

`(r, s)` and `(r, n - s)` are valid together.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

open Point

/-- The point `-P`: the same `x`, and `-y`. -/
private def negPoint : Point → Point
  | infinity => infinity
  | affine x y => affine x (-y)

private theorem isOnCurve_negPoint {p : Point} (h : p.isOnCurve = true) :
    (negPoint p).isOnCurve = true := by
  cases p with
  | infinity => rfl
  | affine x y =>
    show (affine x (-y)).isOnCurve = true
    rw [isOnCurve_affine] at h ⊢
    simp only [Fp.toZMod_neg, neg_mul_neg]
    exact h

private theorem toPoint_negPoint {p : Point} (h : p.isOnCurve = true) :
    toPoint (negPoint p) = -toPoint p := by
  cases p with
  | infinity => exact neg_zero.symm
  | affine x y =>
    show toPoint (affine x (-y)) = _
    rw [toPoint_affine h, toPoint_affine (isOnCurve_negPoint h),
      WeierstrassCurve.Affine.Point.neg_some]
    simp [ShortWeierstrass.curve]

/-- The point the verifier rebuilds, in the group: `u1 G + u2 Q`. -/
private theorem toPoint_rebuilt (u1 u2 : Fn) {q : Point} (hq : q.isOnCurve = true) :
    toPoint (mul u1 generator + mul u2 q)
      = Fn.toZMod u1 • toPoint generator + Fn.toZMod u2 • toPoint q := by
  rw [toPoint_add (isOnCurve_mul _ isOnCurve_generator) (isOnCurve_mul _ hq),
    toPoint_mul' _ isOnCurve_generator, toPoint_mul' _ hq]

/-- A valid signature has `r` and `s` in `[1, n - 1]`. -/
theorem verify_range {q : Point} {e r s : Nat} (h : verify q e r s = true) :
    (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) := by
  unfold verify at h
  split at h
  · split at h
    · exact ⟨by assumption, by assumption⟩
    · cases h
  · cases h

/-- The point at infinity is no public key, and verifies nothing. -/
theorem verify_infinity (e r s : Nat) : verify .infinity e r s = false := by
  unfold verify
  split
  · split
    · simp
    · rfl
  · rfl

/-- A point off the curve is no public key, and verifies nothing. -/
theorem verify_of_not_isOnCurve {q : Point} (hq : q.isOnCurve = false) (e r s : Nat) :
    verify q e r s = false := by
  unfold verify
  split
  · split
    · simp [hq]
    · rfl
  · rfl

/-- Completeness: a signature from the signing operation of SEC 1 v2 §4.1.3 verifies.

The signer has the private key `d` and the nonce `k`, both nonzero.

`R = k G` has coordinate `x`, `r = x mod n`, and `s = k^(-1) (e + r d)`.

Neither `r` nor `s` is zero. -/
theorem verify_sign (d k : Fn) (e : Nat) (hd : d ≠ 0) (hk : k ≠ 0) {x y : Fp}
    (hR : mul k generator = .affine x y) (hr : x.val % Fn.modulus ≠ 0)
    (hs : Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % Fn.modulus) * d) ≠ 0) :
    verify (mul d generator) e (x.val % Fn.modulus)
      (Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % Fn.modulus) * d)).val = true := by
  set sig := Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % Fn.modulus) * d) with hsig
  have hrr : 0 < x.val % Fn.modulus ∧ x.val % Fn.modulus < Fn.modulus :=
    ⟨Nat.pos_of_ne_zero hr, Nat.mod_lt _ (by decide)⟩
  have hss : 0 < sig.val ∧ sig.val < Fn.modulus :=
    ⟨Nat.pos_of_ne_zero (fun h => hs (Fin.ext h)), sig.isLt⟩
  have hG := isOnCurve_generator
  -- The key `d G` is valid: `d != 0` and `G` has order `n`.
  have hQ : mul d generator ≠ .infinity ∧ (mul d generator).isOnCurve = true := by
    refine ⟨fun h => ?_, isOnCurve_mul d hG⟩
    have h0 := congrArg toPoint h
    rw [toPoint_mul' d hG, toPoint_infinity, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact hd (Fn.toZMod.injective (h0.trans (map_zero _).symm))
    · exact toPoint_generator_ne_zero h0
  rw [verify, dite_eq_left hrr, dite_eq_left hss, ite_eq_left hQ]
  dsimp only
  -- The verifier rebuilds `R`: `u1 G + u2 (d G) = s^(-1) (e + r d) G = k G`.
  have hrebuilt : toPoint (mul (Fin.ofNat _ e * Fn.inv ⟨sig.val, hss.2⟩) generator
      + mul ((⟨x.val % Fn.modulus, hrr.2⟩ : Fn) * Fn.inv ⟨sig.val, hss.2⟩) (mul d generator))
      = toPoint (.affine x y) := by
    rw [toPoint_rebuilt _ _ hQ.2, toPoint_mul' d hG, ← hR, toPoint_mul' k hG, smul_smul,
      ← add_smul]
    refine congrArg (· • toPoint generator) ?_
    have hk' : Fn.toZMod k ≠ 0 := fun h => hk (Fn.toZMod.injective (h.trans (map_zero _).symm))
    have hs' : Fn.toZMod sig ≠ 0 := fun h => hs (Fn.toZMod.injective (h.trans (map_zero _).symm))
    have hr' : ((⟨x.val % Fn.modulus, hrr.2⟩ : Fn) : Fn) = Fin.ofNat _ (x.val % Fn.modulus) :=
      Fin.ext (Nat.mod_eq_of_lt hrr.2).symm
    have hsig' : Fn.toZMod sig = (Fn.toZMod k)⁻¹ * (Fn.toZMod (Fin.ofNat _ e)
        + Fn.toZMod (Fin.ofNat _ (x.val % Fn.modulus)) * Fn.toZMod d) := by
      rw [hsig, map_mul, Fn.toZMod_inv, map_add, map_mul]
    rw [Fin.eta sig hss.2, hr', map_mul, map_mul, Fn.toZMod_inv]
    rw [hsig'] at hs' ⊢
    have he : Fn.toZMod (Fin.ofNat _ e)
        + Fn.toZMod (Fin.ofNat _ (x.val % Fn.modulus)) * Fn.toZMod d ≠ 0 :=
      fun h => hs' (by rw [h, mul_zero])
    field_simp
  split
  · rename_i heq
    rw [heq, toPoint_infinity] at hrebuilt
    exact absurd ((toPoint_eq_zero (isOnCurve_mul k hG)).mp (hR ▸ hrebuilt.symm))
      (by rw [hR]; simp)
  · rename_i x' y' heq
    rw [heq] at hrebuilt
    have := (toPoint_inj (heq ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hQ.2))
      (hR ▸ isOnCurve_mul k hG)).mp hrebuilt
    cases this
    simp

/-- `(r, s)` and `(r, n - s)` are valid together: `n - s` rebuilds `-R`, which has the same `x`. -/
theorem verify_neg_s (q : Point) (e r : Nat) {s : Nat} (hs : 0 < s ∧ s < Fn.modulus) :
    verify q e r (Fn.modulus - s) = verify q e r s := by
  have hs' : 0 < Fn.modulus - s ∧ Fn.modulus - s < Fn.modulus := by omega
  by_cases hr : 0 < r ∧ r < Fn.modulus
  · by_cases hq : q ≠ .infinity ∧ q.isOnCurve = true
    · rw [verify, verify, dite_eq_left hr, dite_eq_left hr, dite_eq_left hs, dite_eq_left hs',
        ite_eq_left hq, ite_eq_left hq]
      dsimp only
      -- `n - s` is `-s` mod `n`, so `u1`, `u2` and the rebuilt point change sign.
      have hneg : (⟨Fn.modulus - s, hs'.2⟩ : Fn) = -⟨s, hs.2⟩ :=
        Fin.ext (by simp only [Fin.neg_def]; exact (Nat.mod_eq_of_lt hs'.2).symm)
      rw [hneg]
      have hG := isOnCurve_generator
      generalize hR : mul (Fin.ofNat _ e * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = R
      have hRc : R.isOnCurve = true :=
        hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hq.2)
      have hR' : mul (Fin.ofNat _ e * Fn.inv (-⟨s, hs.2⟩)) generator
          + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv (-⟨s, hs.2⟩)) q = negPoint R := by
        apply (toPoint_inj (isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hq.2))
          (isOnCurve_negPoint hRc)).mp
        rw [toPoint_negPoint hRc, ← hR, toPoint_rebuilt _ _ hq.2, toPoint_rebuilt _ _ hq.2]
        simp only [map_mul, Fn.toZMod_inv, Fn.toZMod_neg, inv_neg, mul_neg, neg_smul, neg_add]
      rw [hR']
      cases R <;> rfl
    · have hq' : q = .infinity ∨ q.isOnCurve = false := by
        by_cases h : q = .infinity
        · exact Or.inl h
        · exact Or.inr (by simpa [h] using hq)
      rcases hq' with rfl | hq'
      · rw [verify_infinity, verify_infinity]
      · rw [verify_of_not_isOnCurve hq', verify_of_not_isOnCurve hq']
  · simp only [verify, dite_eq_right hr]

/-! ## Known answer

Test 1 of `ecdsa_secp256r1_sha256_p1363_test.json` in `C2SP/wycheproof` at `d17cc89`.

It is under the Apache License 2.0.

`e` is the SHA-256 digest of its message `313233343030`, and the signature is valid. -/

/-- The public key of the test, as a point. -/
def wycheproofKey : Point :=
  .affine 0x2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838
    0xc7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e

theorem verify_wycheproof_p1363_1 :
    verify wycheproofKey 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023
      0x2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18
      0x4cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd76 = true := by
  decide +kernel

end EthLib.Cryptography.Secp256r1
