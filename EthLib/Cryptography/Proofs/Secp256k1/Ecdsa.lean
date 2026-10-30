import EthLib.Cryptography.Secp256k1.Ecdsa
import EthLib.Cryptography.Proofs.Secp256k1.Order
import EthLib.Cryptography.Proofs.Hash.Keccak256

/-!
# Proofs: ECDSA verification over secp256k1

- `verify_sign`: a signature made by the signing operation of SEC 1 v2 §4.1.3 verifies.
- `verify_range`: a valid signature has `r` and `s` in `[1, n - 1]`.
- `verify_infinity`, `verify_of_not_isOnCurve`: an invalid public key verifies nothing.
- `verify_neg_s`: `(r, s)` and `(r, n - s)` are valid together, the malleability that EIP-2 removes.
- `isLowS_neg`: exactly one of `s` and `n - s` passes the low-s rule.

So the low-s rule keeps exactly one of the two signatures that every valid signature comes with.
-/

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

open Point

/-- The point the verifier rebuilds, in the group: `u1 G + u2 Q`. -/
private theorem toPoint_rebuilt (u1 u2 : Fn) {q : Point} (hq : q.isOnCurve = true) :
    toPoint (mul u1 generator + mul u2 q) = Fn.toZMod u1 • toPoint generator + Fn.toZMod u2 • toPoint q := by
  rw [toPoint_add (isOnCurve_mul _ isOnCurve_generator) (isOnCurve_mul _ hq), toPoint_mul' _ isOnCurve_generator,
    toPoint_mul' _ hq]

/-- A valid signature has `r` and `s` in `[1, n - 1]`. -/
theorem verify_range {q : Point} {hash : Vector UInt8 32} {r s : Nat} (h : verify q hash r s = true) :
    (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) := by
  unfold verify at h
  split at h
  · split at h
    · exact ⟨by assumption, by assumption⟩
    · cases h
  · cases h

/-- The point at infinity is no public key, and verifies nothing. -/
theorem verify_infinity (hash : Vector UInt8 32) (r s : Nat) : verify .infinity hash r s = false := by
  unfold verify
  split
  · split
    · simp
    · rfl
  · rfl

/-- A point off the curve is no public key, and verifies nothing. -/
theorem verify_of_not_isOnCurve {q : Point} (hq : q.isOnCurve = false) (hash : Vector UInt8 32) (r s : Nat) :
    verify q hash r s = false := by
  unfold verify
  split
  · split
    · simp [hq]
    · rfl
  · rfl

/-- Completeness: a signature made by the signing operation of SEC 1 v2 §4.1.3 verifies.

The signer has the private key `d` and the nonce `k`, both nonzero.

`R = k G` has coordinate `x`, `r = x mod n`, and `s = k^(-1) (e + r d)`, and neither is zero. -/
theorem verify_sign (d k : Fn) (hash : Vector UInt8 32) (hd : d ≠ 0) (hk : k ≠ 0) {x y : Fp}
    (hR : mul k generator = .affine x y) (hr : x.val % Fn.modulus ≠ 0)
    (hs : k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ (x.val % Fn.modulus) * d) ≠ 0) :
    verify (mul d generator) hash (x.val % Fn.modulus)
      (k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ (x.val % Fn.modulus) * d)).val = true := by
  set sig := k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ (x.val % Fn.modulus) * d) with hsig
  have hrr : 0 < x.val % Fn.modulus ∧ x.val % Fn.modulus < Fn.modulus :=
    ⟨Nat.pos_of_ne_zero hr, Nat.mod_lt _ (by decide)⟩
  have hss : 0 < sig.val ∧ sig.val < Fn.modulus := ⟨Nat.pos_of_ne_zero (fun h => hs (Fin.ext h)), sig.isLt⟩
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
  have hrebuilt : toPoint (mul (Fin.ofNat _ (hashToInt hash) * Fn.inv ⟨sig.val, hss.2⟩) generator
      + mul ((⟨x.val % Fn.modulus, hrr.2⟩ : Fn) * Fn.inv ⟨sig.val, hss.2⟩) (mul d generator)) = toPoint (.affine x y) := by
    rw [toPoint_rebuilt _ _ hQ.2, toPoint_mul' d hG, ← hR, toPoint_mul' k hG, smul_smul, ← add_smul]
    refine congrArg (· • toPoint generator) ?_
    have hk' : Fn.toZMod k ≠ 0 := fun h => hk (Fn.toZMod.injective (h.trans (map_zero _).symm))
    have hs' : Fn.toZMod sig ≠ 0 := fun h => hs (Fn.toZMod.injective (h.trans (map_zero _).symm))
    have hr' : ((⟨x.val % Fn.modulus, hrr.2⟩ : Fn) : Fn) = Fin.ofNat _ (x.val % Fn.modulus) :=
      Fin.ext (Nat.mod_eq_of_lt hrr.2).symm
    have hsig' : Fn.toZMod sig = (Fn.toZMod k)⁻¹ * (Fn.toZMod (Fin.ofNat _ (hashToInt hash))
        + Fn.toZMod (Fin.ofNat _ (x.val % Fn.modulus)) * Fn.toZMod d) := by
      rw [hsig, map_mul, Fn.toZMod_inv, map_add, map_mul]
    rw [Fin.eta sig hss.2, hr', map_mul, map_mul, Fn.toZMod_inv]
    rw [hsig'] at hs' ⊢
    have he : Fn.toZMod (Fin.ofNat _ (hashToInt hash)) + Fn.toZMod (Fin.ofNat _ (x.val % Fn.modulus)) * Fn.toZMod d ≠ 0 :=
      fun h => hs' (by rw [h, mul_zero])
    field_simp
  split
  · rename_i heq
    rw [heq, toPoint_infinity] at hrebuilt
    exact absurd ((toPoint_eq_zero (isOnCurve_mul k hG)).mp (hR ▸ hrebuilt.symm)) (by rw [hR]; simp)
  · rename_i x' y' heq
    rw [heq] at hrebuilt
    have := (toPoint_inj (heq ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hQ.2))
      (hR ▸ isOnCurve_mul k hG)).mp hrebuilt
    cases this
    simp

/-- `(r, s)` and `(r, n - s)` are valid together: `n - s` rebuilds `-R`, which has the same `x`. -/
theorem verify_neg_s (q : Point) (hash : Vector UInt8 32) (r : Nat) {s : Nat} (hs : 0 < s ∧ s < Fn.modulus) :
    verify q hash r (Fn.modulus - s) = verify q hash r s := by
  have hs' : 0 < Fn.modulus - s ∧ Fn.modulus - s < Fn.modulus := by omega
  by_cases hr : 0 < r ∧ r < Fn.modulus
  · by_cases hq : q ≠ .infinity ∧ q.isOnCurve = true
    · rw [verify, verify, dite_eq_left hr, dite_eq_left hr, dite_eq_left hs, dite_eq_left hs', ite_eq_left hq,
        ite_eq_left hq]
      dsimp only
      -- `n - s` is `-s` mod `n`, so both `u1` and `u2` change sign, and so does the rebuilt point.
      have hneg : (⟨Fn.modulus - s, hs'.2⟩ : Fn) = -⟨s, hs.2⟩ := Fin.ext (by simp only [Fin.neg_def]; exact (Nat.mod_eq_of_lt hs'.2).symm)
      rw [hneg]
      have hG := isOnCurve_generator
      generalize hR : mul (Fin.ofNat _ (hashToInt hash) * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = R
      have hRc : R.isOnCurve = true := hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hq.2)
      have hR' : mul (Fin.ofNat _ (hashToInt hash) * Fn.inv (-⟨s, hs.2⟩)) generator
          + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv (-⟨s, hs.2⟩)) q = -R := by
        apply (toPoint_inj (isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hq.2)) (isOnCurve_neg hRc)).mp
        rw [toPoint_neg hRc, ← hR, toPoint_rebuilt _ _ hq.2, toPoint_rebuilt _ _ hq.2]
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

/-- Exactly one of `s` and `n - s` passes the low-s rule, since `n` is odd.

It holds for every `s`: `n - s` is `0` when `s >= n`, and `0` is low while `s` is not. -/
theorem isLowS_neg (s : Nat) : isLowS (Fn.modulus - s) = !isLowS s := by
  have hodd : Fn.modulus % 2 = 1 := by decide
  simp only [isLowS]
  by_cases h : s ≤ Fn.modulus / 2
  · simp [h]
    omega
  · simp [h]
    omega

/-! ## Known answer

Test 1 of `ecdsa_secp256k1_sha256_p1363_test.json` in `C2SP/wycheproof` at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`, under the Apache License 2.0.

Its message `313233343030` has the SHA-256 digest below, and the signature is valid.

The kernel runs the whole verification, both scalar multiplications included. -/

/-- The 32 bytes a hex string spells. -/
private def hash32 (hex : String) : Vector UInt8 32 :=
  if h : (Hash.Keccak.hexBytes hex).data.size = 32 then ⟨(Hash.Keccak.hexBytes hex).data, h⟩ else Vector.replicate 32 0

/-- The public key of the test, as a point. -/
private def wycheproofKey : Point :=
  .affine 0xb838ff44e5bc177bf21189d0766082fc9d843226887fc9760371100b7ee20a6f
    0xf0c9d75bfba7b31a6bca1974496eeb56de357071955d83c4b1badaa0b21832e9

theorem verify_wycheproof_p1363_1 :
    verify wycheproofKey (hash32 "bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023")
      0x813ef79ccefa9a56f7ba805f0e478584fe5f0dd5f567bc09b5123ccbc9832365
      0x900e75ad233fcc908509dbff5922647db37c21f4afd3203ae8dc4ae7794b0f87 = true := by
  decide +kernel

end Ecdsa

end EthLib.Cryptography.Secp256k1
