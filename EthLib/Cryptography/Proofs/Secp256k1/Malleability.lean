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
    (hp : Fp.modulus ≤ r + Fn.modulus) : s' = s ∨ s' = Fn.modulus - s :=
  laws.verify_s_eq_or_neg hv hv' hp

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
theorem verify_iff_s_eq_or_neg {q : Point} {hash : Vector UInt8 32} {r s s' : Nat}
    (hv : verify q hash r s = true) (hp : Fp.modulus ≤ r + Fn.modulus) :
    verify q hash r s' = true ↔ s' = s ∨ s' = Fn.modulus - s :=
  laws.verify_iff_s_eq_or_neg hv hp

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
