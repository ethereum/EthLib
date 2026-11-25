module

public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Proofs.Ecdsa.Curve
public import EthLib.Cryptography.Proofs.Secp256k1.MulAdd
public import EthLib.Cryptography.Proofs.Secp256k1.Order

/-!
# Proofs: ECDSA verification over secp256k1

Completeness, the range of a valid signature, and the malleability that the low-s rule removes.

Sources: SEC 1 v2 §4.1.3, and EIP-2 for the low-s rule.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

open Point

/-- secp256k1 satisfies the laws from which the facts of ECDSA follow.

Each fact below is then that of every curve that satisfies these laws. -/
theorem laws : domain.Laws toPoint Fn.toZMod where
  isOnCurve_generator := isOnCurve_generator
  toPoint_generator_ne_zero := toPoint_generator_ne_zero
  isOnCurve_mul k _ hP := isOnCurve_mul k hP
  toPoint_mul k _ hP := toPoint_mul' k hP
  mulAdd_eq k l _ _ hP hQ := mulAdd_eq k l hP hQ
  isOnCurve_add := isOnCurve_add
  toPoint_add := toPoint_add
  isOnCurve_neg := isOnCurve_neg
  toPoint_neg := toPoint_neg
  toPoint_inj := toPoint_inj
  toPoint_infinity := rfl
  y_eq_or_eq_neg {x y y'} hc hc' := by
    -- The two `y` square to the same value, so they agree up to sign.
    rcases Fp.eq_or_eq_neg_of_mul_self (((isOnCurve_affine _ _).mp hc').trans
      ((isOnCurve_affine _ _).mp hc).symm) with h | h
    · exact Or.inl (Fp.toZMod.injective h)
    · exact Or.inr (Fp.toZMod.injective (h.trans (Fp.toZMod_neg y).symm))
  toZMod_inv := Fn.toZMod_inv

/-- The point the verifier rebuilds, in the group: `u1 G + u2 Q`. -/
theorem toPoint_rebuilt (u1 u2 : Fn) {q : Point} (hq : q.isOnCurve = true) :
    toPoint (mul u1 generator + mul u2 q)
      = Fn.toZMod u1 • toPoint generator + Fn.toZMod u2 • toPoint q :=
  laws.toPoint_rebuilt u1 u2 hq

/-- A valid signature has `r` and `s` in `[1, n - 1]`. -/
theorem verify_range {q : Point} {hash : Vector UInt8 32} {r s : Nat} (h : verify q hash r s = true) :
    (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) :=
  domain.verify_range h

/-- The point at infinity is no public key, and verifies nothing. -/
theorem verify_infinity (hash : Vector UInt8 32) (r s : Nat) : verify .infinity hash r s = false :=
  domain.verify_infinity _ r s

/-- A point off the curve is no public key, and verifies nothing. -/
theorem verify_of_not_isOnCurve {q : Point} (hq : q.isOnCurve = false) (hash : Vector UInt8 32) (r s : Nat) :
    verify q hash r s = false :=
  domain.verify_of_not_isOnCurve hq _ r s

/-- A product `k^(-1) a` that is not zero has a nonzero `k`, since the inverse of zero is zero. -/
theorem ne_zero_of_inv_mul_ne_zero {k a : Fn} (h : k.inv * a ≠ 0) : k ≠ 0 :=
  laws.ne_zero_of_inv_mul_ne_zero h

/-- Completeness: a signature made by the signing operation of SEC 1 v2 §4.1.3 verifies.

The signer has a nonzero private key `d` and the nonce `k`.

`R = k G` has coordinate `x`, `r = x mod n`, and `s = k^(-1) (e + r d)`.

Neither `r` nor `s` is zero. -/
theorem verify_sign (d k : Fn) (hash : Vector UInt8 32) (hd : d ≠ 0) {x y : Fp}
    (hR : mul k generator = .affine x y) (hr : x.val % Fn.modulus ≠ 0)
    (hs : k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ (x.val % Fn.modulus) * d) ≠ 0) :
    verify (mul d generator) hash (x.val % Fn.modulus)
      (k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ (x.val % Fn.modulus) * d)).val = true :=
  laws.verify_sign d k _ hd hR hr hs

/-- `(r, s)` and `(r, n - s)` are valid together: `n - s` rebuilds `-R`, which has the same `x`. -/
theorem verify_neg_s (q : Point) (hash : Vector UInt8 32) (r : Nat) {s : Nat} (hs : 0 < s ∧ s < Fn.modulus) :
    verify q hash r (Fn.modulus - s) = verify q hash r s :=
  laws.verify_neg_s q _ r hs

/-- Exactly one of `s` and `n - s` passes the low-s rule, since `n` is odd.

It holds for every `s`: `n - s` is `0` when `s >= n`, and `0` is low while `s` is not.

So the low-s rule keeps exactly one of the two signatures that every valid signature comes with. -/
theorem isLowS_neg (s : Nat) : isLowS (Fn.modulus - s) = !isLowS s := by
  have hodd : Fn.modulus % 2 = 1 := by decide
  simp only [isLowS]
  by_cases h : s ≤ Fn.modulus / 2
  · simp [h]
    omega
  · simp [h]
    omega

/-! ## Forgeries -/

/-- An existential forgery of hash-then-sign ECDSA under the key `q`, against the messages `signed`.

The message is not among them, and ECDSA accepts the pair `(r, s)` on its hash.

This is the winning condition of the chosen-message game, with the hash inside the scheme.

ECDSA on raw digests is forgeable from the public key alone, so it is no target. -/
def IsForgery (hash : ByteArray → Vector UInt8 32) (q : Point) (signed : List ByteArray)
    (f : ByteArray × Nat × Nat) : Prop :=
  f.1 ∉ signed ∧ verify q (hash f.1) f.2.1 f.2.2 = true

end Ecdsa

end EthLib.Cryptography.Secp256k1
