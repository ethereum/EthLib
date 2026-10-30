import EthLib.Cryptography.Xmss.Sign
import EthLib.Cryptography.Proofs.Xmss.Ots
import EthLib.Cryptography.Proofs.Xmss.Serialization

/-!
# Proofs: `Xmss.Sign`

What a successful signature holds, and how signing can fail.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {pp : PublicParam} {s : Seed} {layer : Layer} {e : Nat} {msg : ByteArray}
  {sig : LayerSignature}

/-- A layer's signature is a one-time signature from the seed, with the key's honest path. -/
theorem signLayer_eq_ok (h : signLayer pp s layer e msg = .ok sig) :
    otsSign pp s layer (UInt32.ofNat e) msg = some (sig.randomizer, sig.chainValues) ∧
      sig.path = path pp s layer e := by
  -- Name the one-time signature, so the match reduces without evaluating it.
  cases hots : otsSign pp s layer (UInt32.ofNat e) msg with
  | none => simp [signLayer, hots] at h
  | some found =>
    simp only [signLayer, hots, Option.elim_some] at h
    -- The accepting branch packs the one-time signature with the path.
    obtain rfl := (Except.ok.inj h).symm
    exact ⟨rfl, rfl⟩

/-- A layer fails only when no randomizer trial gives a codeword. -/
theorem signLayer_error {err : XmssError} (h : signLayer pp s layer e msg = .error err) :
    otsSign pp s layer (UInt32.ofNat e) msg = none ∧ err = .noAdmissibleEncoding layer e := by
  cases hots : otsSign pp s layer (UInt32.ofNat e) msg with
  | none =>
    simp only [signLayer, hots, Option.elim_none] at h
    exact ⟨rfl, (Except.error.inj h).symm⟩
  | some found => simp [signLayer, hots] at h

/-- A signature holds one honest signature per layer.

- The bottom key `idx` signs the message.
- The top key `b` signs the root that the bottom key's leaf and path lead to. -/
theorem sign_eq_ok {sk : SecretKey} {idx : LeafIndex} {m : Message} {σ : Signature}
    (h : sign sk idx m = .ok σ) :
    σ.leafIndex = idx ∧
      signLayer sk.publicParam sk.schemeSeed .bottom idx.toNat (packBytes m) = .ok σ.bottom ∧
      signLayer sk.publicParam sk.schemeSeed .top (bottomTree idx)
        (packBytes (fold sk.publicParam .bottom idx.toNat
          (otsPublicLeaf sk.publicParam sk.schemeSeed .bottom idx) σ.bottom.path))
        = .ok σ.top := by
  simp only [sign, bind, Except.bind, pure, Except.pure] at h
  -- Each layer is either an error, which propagates, or a value the next step uses.
  split at h
  · exact absurd h (by simp)
  · rename_i bottom hbottom
    split at h
    · exact absurd h (by simp)
    · rename_i top htop
      obtain rfl := (Except.ok.inj h).symm
      exact ⟨rfl, hbottom, htop⟩

/-- An encoded signature carries the leaf index it was signed at.

So a verifier that reads the index from the bytes learns which one-time key signed. -/
theorem signatureIndex_sign {sk : SecretKey} {idx : LeafIndex} {m : Message} {σ : Signature}
    (h : sign sk idx m = .ok σ) :
    signatureIndex (encodeSignature σ) = .ok idx := by
  rw [signatureIndex_encodeSignature, (sign_eq_ok h).1]

/-- Signing fails only when one layer's one-time key finds no codeword. -/
theorem sign_error {sk : SecretKey} {idx : LeafIndex} {m : Message} {err : XmssError}
    (h : sign sk idx m = .error err) :
    ∃ layer key, err = .noAdmissibleEncoding layer key := by
  simp only [sign, bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i e' hbottom
    obtain rfl := Except.error.inj h
    exact ⟨_, _, (signLayer_error hbottom).2⟩
  · split at h
    · rename_i e' htop
      obtain rfl := Except.error.inj h
      exact ⟨_, _, (signLayer_error htop).2⟩
    · exact absurd h (by simp)

end EthLib.Cryptography.Xmss
