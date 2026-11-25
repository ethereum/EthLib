module

public import EthLib.Cryptography.Secp256r1.Sign
public import EthLib.Cryptography.Proofs.Secp256r1.Ecdsa

/-!
# Proofs: ECDSA signing over secp256r1

A signature from signing is the signing operation of SEC 1 v2 §4.1.3 for some nonzero nonce.

It verifies under the signer's public key, for the hash that it signs.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

namespace Ecdsa

open Point Rfc6979

/-- What a successful run of the signing loop returns: SEC 1 v2 §4.1.3 for some nonce `k`. -/
theorem signWith_spec {d e r s : Fn} :
    ∀ {fuel : Nat} {state : NonceState}, signWith d e fuel state = some (r, s) →
      ∃ k : Fn, ∃ x y : Fp, k ≠ 0 ∧ mul k generator = .affine x y ∧
        r = Fin.ofNat _ x.val ∧ r ≠ 0 ∧ s = k.inv * (e + r * d) ∧ s ≠ 0 := by
  intro fuel state h
  -- The loop is that of every curve, which keeps the point `R` that this one drops.
  obtain ⟨⟨r', s', x, y⟩, hw, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨k, hk, hR, hr, hr0, hs, hs0⟩ := domain.signWith_spec hw
  exact ⟨k, x, y, hk, hR, hr, hr0, hs, hs0⟩

/-- A signature from signing verifies under the public key `d G`, for the hash read mod `n`. -/
theorem verify_sign_of_sign {d r s : Fn} {hash : Vector UInt8 32}
    (signed : sign d hash = some (r, s)) :
    verify (mul d generator) (Base.ByteOrder.ofBE hash.toList) r.val s.val = true := by
  unfold sign at signed
  split at signed
  · cases signed
  rename_i hd
  obtain ⟨k, x, y, -, hR, rfl, hr0, rfl, hs0⟩ := signWith_spec signed
  have hrv : (Fin.ofNat Fn.modulus x.val : Fn).val = x.val % Fn.modulus := Fin.val_ofNat _ _
  have hmod : (Fin.ofNat Fn.modulus (x.val % Fn.modulus) : Fn) = Fin.ofNat _ x.val :=
    Fin.ext (by simp)
  -- The loop's signature is the one of SEC 1 v2 §4.1.3, whose verification is proved.
  have hv := verify_sign d k (Base.ByteOrder.ofBE hash.toList) hd hR
    (by rw [← hrv]; exact fun h0 => hr0 (Fin.ext h0)) (by rw [hmod]; exact hs0)
  rw [hmod, ← hrv] at hv
  exact hv

end Ecdsa

end EthLib.Cryptography.Secp256r1
