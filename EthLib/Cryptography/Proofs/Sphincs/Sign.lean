module

public import EthLib.Cryptography.Sphincs.Sign
public import EthLib.Cryptography.Proofs.Sphincs.Ots

/-!
# Proofs: leanSPHINCS signing

What a successful signature is made of, and why signing can fail.

- The signer signs under the public key that key generation gives `SK.seed`.
- A signature carries the randomizer `R = PRF_msg(SK.prf, PK.seed, M')`.
- It carries the FORS openings at its digest, and three honest layer signatures.
- Signing fails only when a one-time key finds no codeword in `2^32` counters.

Each theorem holds for every hash function `f`, run in the identity monad.

`sign` is the case `f = hash`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {f : ByteArray → Vector UInt8 32}

section Layers

variable {pkSeed : PkSeed} {prf : Prf Id} {layer : Layer} {idx : Nat} {msg : Digest}

/-! ## The signer as a value

`rw` unfolds the signer, not `simp`, as for the one-time signer. -/

/-- What a layer's signature computes: the one-time signature with the key's path, or the error. -/
theorem signLayer_run :
    (signLayer (pureHash f) pkSeed prf layer idx msg).run
      = match (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
        | none => .error (.noAdmissibleEncoding layer)
        | some (counter, chainValues) =>
          .ok { counter, chainValues, path := (path (pureHash f) pkSeed prf layer
            (OtsKey.ofIndex layer idx).tree (OtsKey.ofIndex layer idx).leaf).run } := by
  rw [signLayer, Id.run_bind]
  cases (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
  | none => rfl
  | some found => rfl

/-- What each layer's key signs: the FORS public key, or the root of the tree below. -/
theorem layerMessage_run :
    (layerMessage (pureHash f) pkSeed prf layer idx).run = match layer with
      | .bottom => (forsKey (pureHash f) pkSeed prf idx).run
      | .middle => (treeRoot (pureHash f) pkSeed prf .bottom
          (OtsKey.ofIndex .bottom idx).tree).run
      | .top => (treeRoot (pureHash f) pkSeed prf .middle
          (OtsKey.ofIndex .middle idx).tree).run := by
  cases layer <;> rfl

/-- What signing from a source of secrets, a public key and `R` computes, in `Except`.

Each layer signs what the layer below gives, at the index the digest names. -/
theorem signDerived_run {pk : PublicKey} {rho : Randomizer} {m : Message} :
    (signDerived (pureHash f) prf pk rho m).run
      = let d := (hMsg (pureHash f) rho pk.pkSeed pk.root m).run
        (signLayer (pureHash f) pk.pkSeed prf .bottom (digestIndex d)
            (layerMessage (pureHash f) pk.pkSeed prf .bottom (digestIndex d)).run).run.bind
          fun bottom => (signLayer (pureHash f) pk.pkSeed prf .middle (digestIndex d)
            (layerMessage (pureHash f) pk.pkSeed prf .middle (digestIndex d)).run).run.bind
          fun middle => (signLayer (pureHash f) pk.pkSeed prf .top (digestIndex d)
            (layerMessage (pureHash f) pk.pkSeed prf .top (digestIndex d)).run).run.bind
          fun top => .ok ⟨rho,
            (forsSign (pureHash f) pk.pkSeed prf (digestIndex d) (digestLeaves d)).run,
            bottom, middle, top⟩ := by
  rw [signDerived]
  simp only [Id.run_bind]
  -- Each layer is either an error, which ends signing, or a value the next layer uses.
  cases (signLayer (pureHash f) pk.pkSeed prf .bottom
      (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)
      (layerMessage (pureHash f) pk.pkSeed prf .bottom
        (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)).run).run with
  | error err => rfl
  | ok bottom =>
    -- No signer is unfolded here, so `simp` may reduce the matches on `.ok`.
    simp only [Id.run_bind, Id.run_pure, Except.bind]
    cases (signLayer (pureHash f) pk.pkSeed prf .middle
        (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)
        (layerMessage (pureHash f) pk.pkSeed prf .middle
          (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)).run).run with
    | error err => rfl
    | ok middle =>
      simp only [Id.run_bind, Id.run_pure]
      cases (signLayer (pureHash f) pk.pkSeed prf .top
          (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)
          (layerMessage (pureHash f) pk.pkSeed prf .top
            (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)).run).run with
      | error err => rfl
      | ok top => rfl

/-! ## Layers -/

/-- A layer signature is the one-time signature of the layer's key, with that key's path. -/
theorem signLayer_eq_ok {sig : LayerSignature layer}
    (h : (signLayer (pureHash f) pkSeed prf layer idx msg).run = .ok sig) :
    (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run
        = some (sig.counter, sig.chainValues) ∧
      sig.path = (path (pureHash f) pkSeed prf layer (OtsKey.ofIndex layer idx).tree
        (OtsKey.ofIndex layer idx).leaf).run := by
  rw [signLayer_run] at h
  -- Name the one-time signature, so the match reduces without evaluating it.
  cases hots : (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
  -- No codeword: the result is an error, not a signature.
  | none =>
    rw [hots] at h
    cases h
  -- A codeword: the signature packs the one-time signature with the path.
  | some ots =>
    obtain ⟨counter, chainValues⟩ := ots
    rw [hots] at h
    cases h
    exact ⟨rfl, rfl⟩

/-- A layer fails only when its key finds no codeword, and then says which layer it was. -/
theorem signLayer_error {e : SphincsError}
    (h : (signLayer (pureHash f) pkSeed prf layer idx msg).run = .error e) :
    e = .noAdmissibleEncoding layer ∧
      (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run = none := by
  rw [signLayer_run] at h
  cases hots : (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
  -- No codeword: the error names the layer.
  | none =>
    rw [hots] at h
    cases h
    exact ⟨rfl, rfl⟩
  -- A codeword: the result is a signature, not an error.
  | some ots =>
    obtain ⟨counter, chainValues⟩ := ots
    rw [hots] at h
    cases h

end Layers

/-! ## Signatures -/

/-- What signing computes: the signature under the public key that key generation gives.

- The secrets are `PRF(PK.seed, SK.seed, ADRS)`.
- The randomizer is `PRF_msg(SK.prf, PK.seed, M')`, with `SK.prf` expanded from `SK.seed`.
- The signer rebuilds `PK.root` as key generation computes it. -/
theorem signWith_run {sk : SecretKey} {m : Message} :
    (signWith (pureHash f) sk m).run
      = let pk := (keyGenWith (pureHash f) sk.seed).run.2
        (signDerived (pureHash f) (prf (pureHash f) pk.pkSeed sk.seed) pk
          (prfMsg (pureHash f) (expandKey (pureHash f) sk.seed).run.skPrf pk.pkSeed m).run
          m).run :=
  rfl

/-- A signature holds the randomizer, the FORS openings its digest picks, and three layers.

- `pk` is the public key that key generation gives `SK.seed`.
- Every secret is `PRF(PK.seed, SK.seed, ADRS)`.
- Each layer's key signs what the layer below gives. -/
theorem sign_eq_ok {sk : SecretKey} {pk : PublicKey} {m : Message} {σ : Signature}
    (hpk : (keyGenWith (pureHash f) sk.seed).run.2 = pk)
    (h : (signWith (pureHash f) sk m).run = .ok σ) :
    let secrets := prf (pureHash f) pk.pkSeed sk.seed
    let d := (hMsg (pureHash f) σ.randomizer pk.pkSeed pk.root m).run
    σ.randomizer
        = (prfMsg (pureHash f) (expandKey (pureHash f) sk.seed).run.skPrf pk.pkSeed m).run ∧
      σ.fors = (forsSign (pureHash f) pk.pkSeed secrets (digestIndex d) (digestLeaves d)).run ∧
      (signLayer (pureHash f) pk.pkSeed secrets .bottom (digestIndex d)
          (layerMessage (pureHash f) pk.pkSeed secrets .bottom (digestIndex d)).run).run
        = .ok σ.bottom ∧
      (signLayer (pureHash f) pk.pkSeed secrets .middle (digestIndex d)
          (layerMessage (pureHash f) pk.pkSeed secrets .middle (digestIndex d)).run).run
        = .ok σ.middle ∧
      (signLayer (pureHash f) pk.pkSeed secrets .top (digestIndex d)
          (layerMessage (pureHash f) pk.pkSeed secrets .top (digestIndex d)).run).run
        = .ok σ.top := by
  subst hpk
  rw [signWith_run, signDerived_run] at h
  -- Peel the three layers off the signer, one bind at a time.
  simp only [Except.bind] at h
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
  cases h
  exact ⟨rfl, rfl, hbottom, hmiddle, htop⟩

/-- Signing fails only when a one-time key finds no codeword.

The error names the layer of that key. -/
theorem sign_error {sk : SecretKey} {m : Message} {e : SphincsError}
    (h : (signWith (pureHash f) sk m).run = .error e) :
    ∃ layer, e = .noAdmissibleEncoding layer := by
  rw [signWith_run, signDerived_run] at h
  simp only [Except.bind] at h
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
