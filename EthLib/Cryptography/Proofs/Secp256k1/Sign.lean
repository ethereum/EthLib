module

public import EthLib.Cryptography.Secp256k1.Sign
public import EthLib.Cryptography.Proofs.Secp256k1.Recovery

/-!
# Proofs: ECDSA signing over secp256k1

A signature from signing verifies under the signer's key.

Recovery from it returns that key, and its `s` passes the low-s rule.

Each fact follows from the matching fact about the signing operation of SEC 1 v2 §4.1.3.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

open Point

/-- What a successful run of the signing loop returns: SEC 1 v2 §4.1.3 for some nonce `k`. -/
theorem signWith_spec {d e r s : Fn} {odd : Bool} :
    ∀ {fuel : Nat} {state : NonceState}, signWith d e fuel state = .ok (r, s, odd) →
      ∃ k : Fn, ∃ x y : Fp, k ≠ 0 ∧ mul k generator = .affine x y ∧ x.val < Fn.modulus ∧
        r = Fin.ofNat _ x.val ∧ r ≠ 0 ∧ s = k.inv * (e + r * d) ∧ s ≠ 0 ∧
        odd = decide (y.val % 2 = 1) := by
  intro fuel
  induction fuel with
  | zero => intro state h; cases h
  | succ fuel ih =>
    intro state h
    unfold signWith at h
    dsimp only at h
    split at h
    · rename_i ht
      split at h
      · exact ih h
      · rename_i x y hR
        split at h
        · exact ih h
        · rename_i hrs
          split at h
          · cases h
          · rename_i hx
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨⟨_, ht.2⟩, x, y, fun h0 => ?_, hR, by omega, rfl, fun h => hrs (Or.inl h), rfl,
              fun h => hrs (Or.inr h), rfl⟩
            have := congrArg Fin.val h0
            simp at this
            omega
    · exact ih h

/-- The value of `-s`, for `s ≠ 0`. -/
private theorem val_neg {s : Fn} (hs : s ≠ 0) : (-s).val = Fn.modulus - s.val := by
  have h0 : s.val ≠ 0 := fun h => hs (Fin.ext h)
  simp only [Fin.neg_def]
  exact Nat.mod_eq_of_lt (by omega)

/-- What signing returns: the loop's signature, with `s` replaced by `n - s` when it is high. -/
private theorem sign_spec {sk : Fn} {hash : Vector UInt8 32} {r s : Fn} {odd : Bool}
    (h : sign sk hash = .ok (r, s, odd)) :
    sk ≠ 0 ∧ ∃ s0 odd0, signWith sk (Fin.ofNat _ (hashToInt hash)) MAX_NONCES (nonceSeed sk hash)
        = .ok (r, s0, odd0) ∧
      ((isLowS s0.val = true ∧ s = s0 ∧ odd = odd0) ∨
        (isLowS s0.val = false ∧ s = -s0 ∧ odd = !odd0)) := by
  unfold sign at h
  by_cases hsk : sk = 0
  · simp [hsk] at h
  refine ⟨hsk, ?_⟩
  simp only [hsk, ite_false] at h
  generalize hw : signWith sk _ MAX_NONCES (nonceSeed sk hash) = w at h
  match w, h with
  | .ok (r0, s0, odd0), h =>
    simp only [bind, Except.bind] at h
    by_cases low : isLowS s0.val = true
    · simp only [low, ite_true, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨s0, odd0, rfl, Or.inl ⟨low, rfl, rfl⟩⟩
    · simp only [low] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨s0, odd0, rfl, Or.inr ⟨by simpa using low, rfl, rfl⟩⟩

/-- `x mod n`, read in `Fn`, is `x` read in `Fn`. -/
private theorem ofNat_mod (x : Nat) :
    (Fin.ofNat Fn.modulus (x % Fn.modulus) : Fn) = Fin.ofNat _ x :=
  Fin.ext (by simp)

/-- A signature from signing verifies under the signer's public key `sk G`. -/
theorem verify_sign_rfc6979 {sk : Fn} {hash : Vector UInt8 32} {r s : Fn} {odd : Bool}
    (h : sign sk hash = .ok (r, s, odd)) : verify (mul sk generator) hash r.val s.val = true := by
  obtain ⟨hsk, s0, odd0, hw, hs⟩ := sign_spec h
  obtain ⟨k, x, y, hk, hR, hx, rfl, hr0, hs1, hs0, -⟩ := signWith_spec hw
  have hrv : (Fin.ofNat Fn.modulus x.val : Fn).val = x.val % Fn.modulus := Fin.val_ofNat _ _
  -- The loop's signature is the one of SEC 1 v2 §4.1.3, whose verification is proved.
  have hv := verify_sign sk k hash hsk hk hR
    (by rw [← hrv]; exact fun h0 => hr0 (Fin.ext h0)) (by rw [ofNat_mod, ← hs1]; exact hs0)
  rw [ofNat_mod, ← hrv, ← hs1] at hv
  rcases hs with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
  · exact hv
  · -- `(r, n - s)` verifies with `(r, s)`.
    rw [val_neg hs0,
      verify_neg_s _ _ _ ⟨Nat.pos_of_ne_zero (fun h0 => hs0 (Fin.ext h0)), Fin.isLt _⟩]
    exact hv

/-- Recovery from a signature from signing, with its recovery bit, returns the signer's key. -/
theorem recover_sign_rfc6979 {sk : Fn} {hash : Vector UInt8 32} {r s : Fn} {odd : Bool}
    (h : sign sk hash = .ok (r, s, odd)) :
    recover hash r.val s.val (if odd then 1 else 0) = .ok (mul sk generator) := by
  obtain ⟨hsk, s0, odd0, hw, hs⟩ := sign_spec h
  obtain ⟨k, x, y, -, hR, hx, rfl, hr0, hs1, hs0, hodd⟩ := signWith_spec hw
  have hrv : (Fin.ofNat Fn.modulus x.val : Fn).val = x.val := by
    rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hx
  have hx0 : x.val ≠ 0 := fun h0 => hr0 (Fin.ext (hrv.trans h0))
  -- The loop's signature is the one of SEC 1 v2 §4.1.3, whose recovery is proved.
  have hrec := recover_sign sk k hash hsk hR hx hx0 (by rw [← hs1]; exact hs0)
  have hid : parityId y = if decide (y.val % 2 = 1) then 1 else 0 := by
    unfold parityId; by_cases hy : y.val % 2 = 1 <;> simp [hy]
  rw [hid, ← hs1, ← hodd] at hrec
  rw [← hrv] at hrec
  rcases hs with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · exact hrec
  · -- `n - s` with the other id names the same key.
    rw [val_neg hs0]
    have hflip := recover_neg_s hrec
    cases odd0 <;> exact hflip

/-- A signature from signing passes the low-s rule of EIP-2. -/
theorem isLowS_sign {sk : Fn} {hash : Vector UInt8 32} {r s : Fn} {odd : Bool}
    (h : sign sk hash = .ok (r, s, odd)) : isLowS s.val = true := by
  obtain ⟨-, s0, odd0, hw, hs⟩ := sign_spec h
  obtain ⟨-, -, -, -, -, -, -, -, -, hs0, -⟩ := signWith_spec hw
  rcases hs with ⟨low, rfl, -⟩ | ⟨high, rfl, -⟩
  · exact low
  · rw [val_neg hs0, isLowS_neg, high]
    rfl

end Ecdsa

end EthLib.Cryptography.Secp256k1
