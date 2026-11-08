module

public import EthLib.Base.Proofs.Nat
public import EthLib.Cryptography.Proofs.Secp256r1.Order

/-!
# Proofs: ECDSA verification over secp256r1

A signature from the signing operation of SEC 1 v2 §4.1.3 verifies.

A valid signature has `r` and `s` in `[1, n - 1]`, under a key on the curve other than `O`.

`(r, s)` and `(r, n - s)` are valid together.

When `p <= r + n`, they are the only valid signatures with that `r`, key and message.

The verifier rebuilds the point `R = (e / s) G + (r / s) Q`, and checks that `x_R mod n = r`.

Below that bound, `R` may also have `x = r + n`, and up to four values of `s` may verify.

Verification is exactly the range checks, the key checks and that check of `R`, in the group.
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

/-- A key that verifies is never `(0, 0)`, since that point is off the curve. -/
theorem verify_affine_ne_zero {qx qy : Fp} {e r s : Nat}
    (h : verify (.affine qx qy) e r s = true) : ¬(qx.val = 0 ∧ qy.val = 0) := by
  rintro ⟨hx, hy⟩
  rw [show qx = 0 from Fin.ext hx, show qy = 0 from Fin.ext hy,
    verify_of_not_isOnCurve isOnCurve_affine_zero_zero] at h
  cases h

/-- Completeness: a signature from the signing operation of SEC 1 v2 §4.1.3 verifies.

The signer has a nonzero private key `d` and the nonce `k`.

`R = k G` has coordinate `x`, `r = x mod n`, and `s = k^(-1) (e + r d)`.

Neither `r` nor `s` is zero. -/
theorem verify_sign (d k : Fn) (e : Nat) (hd : d ≠ 0) {x y : Fp}
    (hR : mul k generator = .affine x y) (hr : x.val % Fn.modulus ≠ 0)
    (hs : Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % Fn.modulus) * d) ≠ 0) :
    verify (mul d generator) e (x.val % Fn.modulus)
      (Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % Fn.modulus) * d)).val = true := by
  set sig := Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % Fn.modulus) * d) with hsig
  -- A zero nonce would make `s` zero.
  have hk : k ≠ 0 := by
    rintro rfl
    apply hs
    apply Fn.toZMod.injective
    rw [hsig, map_mul, Fn.toZMod_inv, map_zero, inv_zero, zero_mul]
  have hrr : 0 < x.val % Fn.modulus ∧ x.val % Fn.modulus < Fn.modulus :=
    ⟨Nat.pos_of_ne_zero hr, Nat.mod_lt _ (by decide)⟩
  have hss : 0 < sig.val ∧ sig.val < Fn.modulus :=
    ⟨Nat.pos_of_ne_zero (fun h => hs (Fin.ext h)), sig.isLt⟩
  have hG := isOnCurve_generator
  -- The key `d G` is valid: `d != 0` and `G` has order `n`.
  have hQ : mul d generator ≠ .infinity ∧ (mul d generator).isOnCurve = true :=
    ⟨mul_generator_ne_infinity hd, isOnCurve_mul d hG⟩
  rw [verify, dite_eq_left hrr, dite_eq_left hss, ite_eq_left hQ]
  dsimp only
  rw [mulAdd_eq _ _ isOnCurve_generator hQ.2]
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
      rw [mulAdd_eq _ _ isOnCurve_generator hq.2, mulAdd_eq _ _ isOnCurve_generator hq.2]
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

/-- A valid signature has `r` and `s` in `[1, n - 1]`, under a key on the curve other than `O`.

Its rebuilt point `R` is affine, with `x_R mod n = r`. -/
theorem verify_rebuilt {q : Point} {e r s : Nat} (hv : verify q e r s = true) :
    ∃ (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus),
      q ≠ .infinity ∧ q.isOnCurve = true ∧
      ∃ x y : Fp, mul (Fin.ofNat _ e * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = .affine x y ∧ x.val % Fn.modulus = r := by
  obtain ⟨hr, hs⟩ := verify_range hv
  have hq : q ≠ .infinity ∧ q.isOnCurve = true := by
    by_cases hi : q = .infinity
    · subst hi; rw [verify_infinity] at hv; cases hv
    · cases hc : q.isOnCurve
      · rw [verify_of_not_isOnCurve hc] at hv; cases hv
      · exact ⟨hi, rfl⟩
  refine ⟨hr, hs, hq.1, hq.2, ?_⟩
  rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left hq] at hv
  dsimp only at hv
  rw [mulAdd_eq _ _ isOnCurve_generator hq.2] at hv
  split at hv
  · cases hv
  · rename_i x y hR
    exact ⟨x, y, hR, by simpa using hv⟩

/-- Two signatures with the same `r`, key and message verify only if their `s` agree up to sign.

The bound `p <= r + n` makes both rebuilt points have `x = r`, so they are equal or opposite. -/
theorem verify_s_eq_or_neg {q : Point} {e r s s' : Nat}
    (hv : verify q e r s = true) (hv' : verify q e r s' = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) : s' = s ∨ s' = Fn.modulus - s := by
  obtain ⟨hr, hs, -, hqc, x, y, hR, hx⟩ := verify_rebuilt hv
  obtain ⟨hr', hs', -, -, x', y', hR', hx'⟩ := verify_rebuilt hv'
  -- Both rebuilt points have `x = r`.
  obtain rfl : x' = x := Fin.ext ((Base.eq_of_mod_eq_of_lt hx' x'.isLt hp).trans
    (Base.eq_of_mod_eq_of_lt hx x.isLt hp).symm)
  have hG := isOnCurve_generator
  have hc : (affine x' y).isOnCurve = true :=
    hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
  have hc' : (affine x' y').isOnCurve = true :=
    hR' ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
  -- Each point is `s^(-1) X` for the same `X = e G + r Q`, and `X != 0`.
  set X := Fn.toZMod (Fin.ofNat _ e) • toPoint generator + Fn.toZMod ⟨r, hr.2⟩ • toPoint q
  have hP : toPoint (affine x' y) = (Fn.toZMod ⟨s, hs.2⟩)⁻¹ • X := by
    rw [← hR, toPoint_rebuilt _ _ hqc]
    simp only [X, map_mul, Fn.toZMod_inv, smul_add, smul_smul, mul_comm]
  have hP' : toPoint (affine x' y') = (Fn.toZMod ⟨s', hs'.2⟩)⁻¹ • X := by
    rw [← hR', toPoint_rebuilt _ _ hqc]
    simp only [X, map_mul, Fn.toZMod_inv, smul_add, smul_smul, mul_comm]
  have hX : X ≠ 0 := fun h0 => by
    rw [h0, smul_zero, toPoint_eq_zero hc] at hP
    cases hP
  -- The two `y` square to the same value, so they agree up to sign.
  have hsq : Fp.toZMod y' * Fp.toZMod y' = Fp.toZMod y * Fp.toZMod y :=
    ((isOnCurve_affine _ _).mp hc').trans ((isOnCurve_affine _ _).mp hc).symm
  rcases mul_self_eq_mul_self_iff.mp hsq with h | h
  · -- The same point: `s'^(-1) X = s^(-1) X`, so `s' = s`.
    obtain rfl : y' = y := Fp.toZMod.injective h
    have h0 : ((Fn.toZMod ⟨s', hs'.2⟩)⁻¹ - (Fn.toZMod ⟨s, hs.2⟩)⁻¹) • X = 0 := by
      rw [sub_smul, ← hP, ← hP', sub_self]
    have heq := inv_injective (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hX))
    exact Or.inl (congrArg Fin.val (Fn.toZMod.injective heq))
  · -- Opposite points: `s'^(-1) X = -(s^(-1) X)`, so `s' = -s`.
    have hy : y' = -y :=
      Fp.toZMod.injective (h.trans (Fp.toZMod_neg y).symm)
    subst hy
    have hneg : toPoint (affine x' (-y)) = -toPoint (affine x' y) :=
      toPoint_negPoint (p := affine x' y) hc
    have h0 : ((Fn.toZMod ⟨s', hs'.2⟩)⁻¹ + (Fn.toZMod ⟨s, hs.2⟩)⁻¹) • X = 0 := by
      rw [add_smul, ← hP, ← hP', hneg, neg_add_cancel]
    have heq : Fn.toZMod ⟨s', hs'.2⟩ = -Fn.toZMod ⟨s, hs.2⟩ := by
      rw [← inv_inj, inv_neg]
      exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h0).resolve_right hX)
    have hv := congrArg Fin.val (Fn.toZMod.injective (heq.trans (Fn.toZMod_neg _).symm))
    simp only [Fin.neg_def] at hv
    exact Or.inr (hv.trans (Nat.mod_eq_of_lt (by omega)))

/-- Let `(r, s)` be a valid signature under a key and a message, with `p <= r + n`.

Then `(r, s')` is valid under the same key and message exactly when `s'` is `s` or `n - s`. -/
theorem verify_iff_s_eq_or_neg {q : Point} {e r s s' : Nat} (hv : verify q e r s = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) :
    verify q e r s' = true ↔ s' = s ∨ s' = Fn.modulus - s := by
  refine ⟨fun hv' => verify_s_eq_or_neg hv hv' hp, ?_⟩
  rintro (rfl | rfl)
  · exact hv
  · obtain ⟨-, hs, -⟩ := verify_rebuilt hv
    rw [verify_neg_s q e r hs, hv]

/-- A scalar read from a natural number is that number in `ZMod n`. -/
private theorem toZMod_ofNat (e : Nat) : Fn.toZMod (Fin.ofNat _ e) = (e : ZMod Fn.modulus) := by
  apply ZMod.val_injective
  simp [Fn.toZMod, ZMod.val_natCast]
  rfl

/-- The scalars `e / s` and `r / s` that the verifier computes, in `ZMod n`. -/
private theorem toZMod_scalars (e r s : Nat) (hr : r < Fn.modulus) (hs : s < Fn.modulus) :
    Fn.toZMod (Fin.ofNat _ e * Fn.inv ⟨s, hs⟩) = (e : ZMod Fn.modulus) / s ∧
      Fn.toZMod ((⟨r, hr⟩ : Fn) * Fn.inv ⟨s, hs⟩) = (r : ZMod Fn.modulus) / s := by
  have hs' : (⟨s, hs⟩ : Fn) = Fin.ofNat _ s := Fin.ext (Nat.mod_eq_of_lt hs).symm
  have hr' : (⟨r, hr⟩ : Fn) = Fin.ofNat _ r := Fin.ext (Nat.mod_eq_of_lt hr).symm
  rw [map_mul, map_mul, Fn.toZMod_inv, hs', hr', toZMod_ofNat, toZMod_ofNat,
    toZMod_ofNat, div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨rfl, rfl⟩

/-- Verification is the verifying operation of SEC 1 v2 §4.1.4, read in the group of the curve.

A signature `(r, s)` is valid exactly when these hold:

- `r` and `s` lie in `[1, n - 1]`;
- the key `Q` lies on the curve and is not `O`;
- `R = (e / s) G + (r / s) Q` is a point `(x, y)` other than `O`, with `x mod n = r`.

The scalars `e / s` and `r / s` are taken modulo `n`, and `e` is any natural number. -/
theorem verify_eq_true_iff {q : Point} {e r s : Nat} :
    verify q e r s = true ↔
      (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) ∧ q ≠ .infinity ∧
        q.isOnCurve = true ∧
        ∃ x y : Fp, (affine x y).isOnCurve = true ∧
          toPoint (affine x y) = ((e : ZMod Fn.modulus) / s) • toPoint generator
            + ((r : ZMod Fn.modulus) / s) • toPoint q ∧
          x.val % Fn.modulus = r := by
  have hG := isOnCurve_generator
  constructor
  · intro hv
    obtain ⟨hr, hs, hqi, hqc, x, y, hR, hx⟩ := verify_rebuilt hv
    obtain ⟨h1, h2⟩ := toZMod_scalars e r s hr.2 hs.2
    have hc : (affine x y).isOnCurve = true :=
      hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
    refine ⟨hr, hs, hqi, hqc, x, y, hc, ?_, hx⟩
    rw [← hR, toPoint_rebuilt _ _ hqc, h1, h2]
  · rintro ⟨hr, hs, hqi, hqc, x, y, hc, hR, hx⟩
    obtain ⟨h1, h2⟩ := toZMod_scalars e r s hr.2 hs.2
    rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left ⟨hqi, hqc⟩]
    dsimp only
    rw [mulAdd_eq _ _ isOnCurve_generator hqc]
    -- The point that the verifier rebuilds is `(x, y)`, since both have one image in the group.
    have heq : mul (Fin.ofNat _ e * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = affine x y := by
      apply (toPoint_inj (isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)) hc).mp
      rw [toPoint_rebuilt _ _ hqc, h1, h2, hR]
    rw [heq]
    simp [hx]

end EthLib.Cryptography.Secp256r1
