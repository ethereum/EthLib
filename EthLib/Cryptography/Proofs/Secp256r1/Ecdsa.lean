module

public import EthLib.Cryptography.Proofs.Ecdsa.Curve
public import EthLib.Cryptography.Proofs.Secp256r1.Order

/-!
# Proofs: ECDSA verification over secp256r1

A signature from the signing operation of SEC 1 v2 §4.1.3 verifies.

A valid signature has `r` and `s` in `[1, n - 1]`, under a key on the curve other than `O`.

`(r, s)` and `(r, n - s)` are valid together.

When `p <= r + n`, they are the only valid signatures with that `r`, key and message.

The verifier rebuilds the point `R = (e / s) G + (r / s) Q`, and checks that `x_R mod n = r`.

Verification is exactly the range checks, the key checks and that check of `R`, in the group.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

open Point

/-- P-256 satisfies the laws from which the facts of ECDSA follow.

Each fact below is then that of every curve that satisfies these laws. -/
theorem laws : domain.Laws toPoint Fn.toZMod where
  isOnCurve_generator := isOnCurve_generator
  toPoint_generator_ne_zero := toPoint_generator_ne_zero
  isOnCurve_mul k _ hP := isOnCurve_mul k hP
  toPoint_mul k _ hP := toPoint_mul' k hP
  mulAdd_eq k l _ _ hP hQ := mulAdd_eq k l hP hQ
  isOnCurve_add := isOnCurve_add
  toPoint_add := toPoint_add
  isOnCurve_neg := ShortWeierstrass.Point.isOnCurve_neg embedding
  toPoint_neg := ShortWeierstrass.Point.toPoint_neg embedding
  toPoint_inj := toPoint_inj
  toPoint_infinity := rfl
  y_eq_or_eq_neg {x y y'} hc hc' := by
    -- The two `y` square to the same value, so they agree up to sign.
    rcases mul_self_eq_mul_self_iff.mp (((isOnCurve_affine _ _).mp hc').trans
      ((isOnCurve_affine _ _).mp hc).symm) with h | h
    · exact Or.inl (Fp.toZMod.injective h)
    · exact Or.inr (Fp.toZMod.injective (h.trans (Fp.toZMod_neg y).symm))
  toZMod_inv := Fn.toZMod_inv

/-- A valid signature has `r` and `s` in `[1, n - 1]`. -/
theorem verify_range {q : Point} {e r s : Nat} (h : verify q e r s = true) :
    (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) :=
  domain.verify_range h

/-- The point at infinity is no public key, and verifies nothing. -/
theorem verify_infinity (e r s : Nat) : verify .infinity e r s = false :=
  domain.verify_infinity e r s

/-- A point off the curve is no public key, and verifies nothing. -/
theorem verify_of_not_isOnCurve {q : Point} (hq : q.isOnCurve = false) (e r s : Nat) :
    verify q e r s = false :=
  domain.verify_of_not_isOnCurve hq e r s

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
      (Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % Fn.modulus) * d)).val = true :=
  laws.verify_sign d k e hd hR hr hs

/-- `(r, s)` and `(r, n - s)` are valid together: `n - s` rebuilds `-R`, which has the same `x`. -/
theorem verify_neg_s (q : Point) (e r : Nat) {s : Nat} (hs : 0 < s ∧ s < Fn.modulus) :
    verify q e r (Fn.modulus - s) = verify q e r s :=
  laws.verify_neg_s q e r hs

/-- A valid signature has `r` and `s` in `[1, n - 1]`, under a key on the curve other than `O`.

Its rebuilt point `R` is affine, with `x_R mod n = r`. -/
theorem verify_rebuilt {q : Point} {e r s : Nat} (hv : verify q e r s = true) :
    ∃ (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus),
      q ≠ .infinity ∧ q.isOnCurve = true ∧
      ∃ x y : Fp, mul (Fin.ofNat _ e * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = .affine x y ∧ x.val % Fn.modulus = r :=
  laws.verify_rebuilt hv

/-- Two signatures with the same `r`, key and message verify only if their `s` agree up to sign.

The bound `p <= r + n` makes both rebuilt points have `x = r`, so they are equal or opposite. -/
theorem verify_s_eq_or_neg {q : Point} {e r s s' : Nat}
    (hv : verify q e r s = true) (hv' : verify q e r s' = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) : s' = s ∨ s' = Fn.modulus - s :=
  laws.verify_s_eq_or_neg hv hv' hp

/-- Let `(r, s)` be a valid signature under a key and a message, with `p <= r + n`.

Then `(r, s')` is valid under the same key and message exactly when `s'` is `s` or `n - s`.

Below that bound, the rebuilt point `R` may also have `x = r + n`.

Then up to four values of `s` may verify. -/
theorem verify_iff_s_eq_or_neg {q : Point} {e r s s' : Nat} (hv : verify q e r s = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) :
    verify q e r s' = true ↔ s' = s ∨ s' = Fn.modulus - s :=
  laws.verify_iff_s_eq_or_neg hv hp

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
          x.val % Fn.modulus = r :=
  laws.verify_eq_true_iff

end EthLib.Cryptography.Secp256r1
