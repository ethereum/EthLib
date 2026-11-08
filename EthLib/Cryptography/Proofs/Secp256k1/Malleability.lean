module

public import EthLib.Cryptography.Proofs.Secp256k1.Recovery

/-!
# Proofs: the malleability of ECDSA over secp256k1

Let `p <= r + n`.

Then `(r, s)` and `(r, s')` both verify only if `s' = s` or `s' = n - s`.

Both are valid together, so the valid signatures with that `r`, key and hash are exactly these two.

So the low-s rule of EIP-2 leaves one valid signature for each `r`.

Below that bound, `R` may also have `x = r + n`, and up to four values of `s` may verify.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

open Point

/-- Two signatures with the same `r` verify only if their `s` agree up to sign mod `n`.

The bound `p <= r + n` makes both rebuilt points have `x = r`, so they are equal or opposite. -/
theorem verify_s_eq_or_neg {q : Point} {hash : Vector UInt8 32} {r s s' : Nat}
    (hv : verify q hash r s = true) (hv' : verify q hash r s' = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) : s' = s ∨ s' = Fn.modulus - s := by
  obtain ⟨hr, hs, -, hqc, x, y, hR, hx⟩ := verify_rebuilt hv
  obtain ⟨hr', hs', -, -, x', y', hR', hx'⟩ := verify_rebuilt hv'
  -- Both rebuilt points have `x = r`.
  obtain rfl : x' = x := Fin.ext ((val_eq_of_mod_eq hx' hp).trans (val_eq_of_mod_eq hx hp).symm)
  have hG := isOnCurve_generator
  have hc : (affine x' y).isOnCurve = true :=
    hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
  have hc' : (affine x' y').isOnCurve = true :=
    hR' ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
  -- Each point is `s^(-1) X` for the same `X = e G + r Q`, and `X != 0`.
  set X := Fn.toZMod (Fin.ofNat _ (hashToInt hash)) • toPoint generator
    + Fn.toZMod ⟨r, hr.2⟩ • toPoint q
  have hP : toPoint (affine x' y) = (Fn.toZMod ⟨s, hs.2⟩)⁻¹ • X := by
    rw [← hR, toPoint_rebuilt _ _ hqc]
    simp only [X, map_mul, Fn.toZMod_inv, smul_add, smul_smul, mul_comm]
  have hP' : toPoint (affine x' y') = (Fn.toZMod ⟨s', hs'.2⟩)⁻¹ • X := by
    rw [← hR', toPoint_rebuilt _ _ hqc]
    simp only [X, map_mul, Fn.toZMod_inv, smul_add, smul_smul, mul_comm]
  have hX : X ≠ 0 := fun h0 => by
    rw [h0, smul_zero, toPoint_eq_zero hc] at hP
    cases hP
  -- The two `y` agree up to sign.
  rcases Fp.eq_or_eq_neg_of_mul_self (((isOnCurve_affine _ _).mp hc').trans
    ((isOnCurve_affine _ _).mp hc).symm) with h | h
  · -- The same point: `s'^(-1) X = s^(-1) X`, so `s' = s`.
    obtain rfl : y' = y := Fp.toZMod.injective h
    have h0 : ((Fn.toZMod ⟨s', hs'.2⟩)⁻¹ - (Fn.toZMod ⟨s, hs.2⟩)⁻¹) • X = 0 := by
      rw [sub_smul, ← hP, ← hP', sub_self]
    have heq := inv_injective (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hX))
    exact Or.inl (congrArg Fin.val (Fn.toZMod.injective heq))
  · -- Opposite points: `s'^(-1) X = -(s^(-1) X)`, so `s' = -s`.
    have hy : y' = -y := Fp.toZMod.injective (h.trans (Fp.toZMod_neg y).symm)
    subst hy
    have hneg : toPoint (affine x' (-y)) = -toPoint (affine x' y) := by
      rw [show (affine x' (-y)) = -(affine x' y) from rfl, toPoint_neg hc]
    have h0 : ((Fn.toZMod ⟨s', hs'.2⟩)⁻¹ + (Fn.toZMod ⟨s, hs.2⟩)⁻¹) • X = 0 := by
      rw [add_smul, ← hP, ← hP', hneg, neg_add_cancel]
    have heq : Fn.toZMod ⟨s', hs'.2⟩ = -Fn.toZMod ⟨s, hs.2⟩ := by
      rw [← inv_inj, inv_neg]
      exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h0).resolve_right hX)
    have hv := congrArg Fin.val (Fn.toZMod.injective (heq.trans (Fn.toZMod_neg _).symm))
    simp only [Fin.neg_def] at hv
    exact Or.inr (hv.trans (Nat.mod_eq_of_lt (by omega)))

/-- Two low-s signatures with the same `r` that verify are equal, when `p <= r + n`. -/
theorem verify_lowS_unique {q : Point} {hash : Vector UInt8 32} {r s s' : Nat}
    (hv : verify q hash r s = true) (hv' : verify q hash r s' = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) (hlow : isLowS s = true) (hlow' : isLowS s' = true) :
    s' = s := by
  rcases verify_s_eq_or_neg hv hv' hp with h | h
  · exact h
  · -- `n - s` fails the low-s rule when `s` passes it.
    rw [h, isLowS_neg, hlow] at hlow'
    cases hlow'

/-- Let `(r, s)` be a valid signature under a key and a hash, with `p <= r + n`.

Then `(r, s')` is valid under the same key and hash exactly when `s'` is `s` or `n - s`. -/
theorem verify_iff_of_verify {q : Point} {hash : Vector UInt8 32} {r s s' : Nat}
    (hv : verify q hash r s = true) (hp : Fp.modulus ≤ r + Fn.modulus) :
    verify q hash r s' = true ↔ s' = s ∨ s' = Fn.modulus - s := by
  refine ⟨fun hv' => verify_s_eq_or_neg hv hv' hp, ?_⟩
  rintro (rfl | rfl)
  · exact hv
  · obtain ⟨-, hs⟩ := verify_range hv
    rw [verify_neg_s q hash r hs, hv]

/-- Let `(r, s)` be a valid low-s signature under a key and a hash, with `p <= r + n`.

Then `(r, s')` is a valid low-s signature under the same key and hash exactly when `s' = s`. -/
theorem verify_and_isLowS_iff {q : Point} {hash : Vector UInt8 32} {r s s' : Nat}
    (hv : verify q hash r s = true) (hlow : isLowS s = true) (hp : Fp.modulus ≤ r + Fn.modulus) :
    verify q hash r s' = true ∧ isLowS s' = true ↔ s' = s := by
  refine ⟨fun ⟨hv', hlow'⟩ => verify_lowS_unique hv hv' hp hlow hlow', ?_⟩
  rintro rfl
  exact ⟨hv, hlow⟩

end Ecdsa

end EthLib.Cryptography.Secp256k1
