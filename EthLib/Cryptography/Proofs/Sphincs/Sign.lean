import EthLib.Cryptography.Sphincs.Sign
import EthLib.Cryptography.Proofs.Sphincs.Ots

/-!
# Proofs: `Sphincs.Sign`

What a successful signature is made of, and why signing can fail.

- A signature carries the message's randomizer, the FORS openings at its digest, and three honest layer signatures.
- Signing fails only when a one-time key finds no codeword in `2^32` counters.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {pp : PublicParam} {seed : Seed} {layer : Layer} {idx : Nat} {msg : ByteArray}

/-- A layer signature is the one-time signature of the layer's key, with that key's path. -/
theorem signLayer_eq_ok {sig : LayerSignature layer} (h : signLayer pp seed layer idx msg = .ok sig) :
    otsSign pp seed (OtsKey.ofIndex layer idx) msg = some (sig.counter, sig.chainValues) ∧
      sig.path = path pp seed layer (OtsKey.ofIndex layer idx).tree (OtsKey.ofIndex layer idx).leaf := by
  cases hots : otsSign pp seed (OtsKey.ofIndex layer idx) msg with
  -- No codeword: the result is an error, not a signature.
  | none =>
    simp only [signLayer, hots, Option.elim_none] at h
    cases h
  -- A codeword: the signature packs the one-time signature with the path.
  | some ots =>
    simp only [signLayer, hots, Option.elim_some, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- A layer fails only when its key finds no codeword, and then says which layer it was. -/
theorem signLayer_error {e : SphincsError} (h : signLayer pp seed layer idx msg = .error e) :
    e = .noAdmissibleEncoding layer ∧ otsSign pp seed (OtsKey.ofIndex layer idx) msg = none := by
  cases hots : otsSign pp seed (OtsKey.ofIndex layer idx) msg with
  -- No codeword: the error names the layer.
  | none =>
    simp only [signLayer, hots, Option.elim_none, Except.error.injEq] at h
    exact ⟨h.symm, rfl⟩
  -- A codeword: the result is a signature, not an error.
  | some ots =>
    simp only [signLayer, hots, Option.elim_some] at h
    cases h

/-- A signature is made of the message's randomizer, the FORS openings its digest picks, and three layers.

Each layer's key signs what the layer below gives. -/
theorem sign_eq_ok {sk : SecretKey} {m : Message} {σ : Signature} (h : sign sk m = .ok σ) :
    let d := messageDigest sk.publicParam m σ.randomizer
    σ.randomizer = randomizer sk.publicParam sk.seed m ∧
      σ.fors = forsSign sk.publicParam sk.seed (digestIndex d) (digestLeaves d) ∧
      signLayer sk.publicParam sk.seed .bottom (digestIndex d)
          (layerMessage sk.publicParam sk.seed .bottom (digestIndex d)) = .ok σ.bottom ∧
      signLayer sk.publicParam sk.seed .middle (digestIndex d)
          (layerMessage sk.publicParam sk.seed .middle (digestIndex d)) = .ok σ.middle ∧
      signLayer sk.publicParam sk.seed .top (digestIndex d)
          (layerMessage sk.publicParam sk.seed .top (digestIndex d)) = .ok σ.top := by
  -- Peel the three layers off the signer, one bind at a time.
  simp only [sign, bind, Except.bind] at h
  split at h
  · cases h
  rename_i bottom hbottom
  split at h
  · cases h
  rename_i middle hmiddle
  split at h
  · cases h
  rename_i top htop
  -- What is left is the signature itself.
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, hbottom, hmiddle, htop⟩

/-- Signing fails only when a one-time key finds no codeword, and the error names that key's layer. -/
theorem sign_error {sk : SecretKey} {m : Message} {e : SphincsError} (h : sign sk m = .error e) :
    ∃ layer, e = .noAdmissibleEncoding layer := by
  simp only [sign, bind, Except.bind] at h
  -- Each layer either fails, with its own error, or passes to the next.
  split at h
  · rename_i e' he
    cases h
    exact ⟨.bottom, (signLayer_error he).1⟩
  split at h
  · rename_i e' he
    cases h
    exact ⟨.middle, (signLayer_error he).1⟩
  split at h
  · rename_i e' he
    cases h
    exact ⟨.top, (signLayer_error he).1⟩
  -- With every layer passing, the result is a signature, not an error.
  · cases h

end EthLib.Cryptography.Sphincs
