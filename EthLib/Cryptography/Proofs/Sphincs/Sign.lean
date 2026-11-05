module

public import EthLib.Cryptography.Sphincs.Sign
public import EthLib.Cryptography.Proofs.Sphincs.Ots

/-!
# Proofs: leanSPHINCS signing

What a successful signature is made of, and why signing can fail.

- A signature carries the message's randomizer and the FORS openings at its digest.
- It also carries three honest layer signatures.
- Signing fails only when a one-time key finds no codeword in `2^32` counters.

Each theorem holds for every hash function `f`, run in the identity monad.

`sign` is the case `f = hash`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {prf : SeedPrf Id} {layer : Layer}
  {idx : Nat} {msg : ByteArray}

/-! ## The signer as a value

`rw` unfolds the signer, not `simp`, as for the one-time signer. -/

/-- What a layer's signature computes: the one-time signature with the key's path, or the error. -/
theorem signLayer_run :
    (signLayer (pureHash f) pp prf layer idx msg).run
      = match (otsSign (pureHash f) pp prf (OtsKey.ofIndex layer idx) msg).run with
        | none => .error (.noAdmissibleEncoding layer)
        | some (counter, chainValues) =>
          .ok { counter, chainValues, path := (path (pureHash f) pp prf layer
            (OtsKey.ofIndex layer idx).tree (OtsKey.ofIndex layer idx).leaf).run } := by
  rw [signLayer, Id.run_bind]
  cases (otsSign (pureHash f) pp prf (OtsKey.ofIndex layer idx) msg).run with
  | none => rfl
  | some found => rfl

/-- What each layer's key signs: the FORS key, or the root of the tree below. -/
theorem layerMessage_run :
    (layerMessage (pureHash f) pp prf layer idx).run = match layer with
      | .bottom => forsKeyBytes (forsKey (pureHash f) pp prf idx).run
      | .middle => packBytes (treeRoot (pureHash f) pp prf .bottom
          (OtsKey.ofIndex .bottom idx).tree).run
      | .top => packBytes (treeRoot (pureHash f) pp prf .middle
          (OtsKey.ofIndex .middle idx).tree).run := by
  cases layer <;> rfl

/-- What signing from the derivations of a seed computes, one layer after the other, in `Except`.

Each layer signs what the layer below gives, at the index the digest names. -/
theorem signDerived_run {m : Message} :
    (signDerived (pureHash f) prf pp m).run
      = let rho := (randomizer pp prf m).run
        let d := (messageDigest (pureHash f) pp m rho).run
        (signLayer (pureHash f) pp prf .bottom (digestIndex d)
            (layerMessage (pureHash f) pp prf .bottom (digestIndex d)).run).run.bind
          fun bottom => (signLayer (pureHash f) pp prf .middle (digestIndex d)
            (layerMessage (pureHash f) pp prf .middle (digestIndex d)).run).run.bind
          fun middle => (signLayer (pureHash f) pp prf .top (digestIndex d)
            (layerMessage (pureHash f) pp prf .top (digestIndex d)).run).run.bind
          fun top => .ok ⟨rho,
            (forsSign (pureHash f) pp prf (digestIndex d) (digestLeaves d)).run,
            bottom, middle, top⟩ := by
  rw [signDerived]
  simp only [Id.run_bind]
  -- Each layer is either an error, which ends signing, or a value the next layer uses.
  cases (signLayer (pureHash f) pp prf .bottom
      (digestIndex (messageDigest (pureHash f) pp m (randomizer pp prf m).run).run)
      (layerMessage (pureHash f) pp prf .bottom (digestIndex (messageDigest (pureHash f) pp m
        (randomizer pp prf m).run).run)).run).run with
  | error err => rfl
  | ok bottom =>
    -- No signer is unfolded here, so `simp` may reduce the matches on `.ok`.
    simp only [Id.run_bind, Id.run_pure, Except.bind]
    cases (signLayer (pureHash f) pp prf .middle
        (digestIndex (messageDigest (pureHash f) pp m (randomizer pp prf m).run).run)
        (layerMessage (pureHash f) pp prf .middle (digestIndex (messageDigest (pureHash f) pp m
          (randomizer pp prf m).run).run)).run).run with
    | error err => rfl
    | ok middle =>
      simp only [Id.run_bind, Id.run_pure]
      cases (signLayer (pureHash f) pp prf .top
          (digestIndex (messageDigest (pureHash f) pp m
            (randomizer pp prf m).run).run)
          (layerMessage (pureHash f) pp prf .top (digestIndex (messageDigest (pureHash f) pp m
            (randomizer pp prf m).run).run)).run).run with
      | error err => rfl
      | ok top => rfl

/-! ## Layers -/

/-- A layer signature is the one-time signature of the layer's key, with that key's path. -/
theorem signLayer_eq_ok {sig : LayerSignature layer}
    (h : (signLayer (pureHash f) pp prf layer idx msg).run = .ok sig) :
    (otsSign (pureHash f) pp prf (OtsKey.ofIndex layer idx) msg).run
        = some (sig.counter, sig.chainValues) ∧
      sig.path = (path (pureHash f) pp prf layer (OtsKey.ofIndex layer idx).tree
        (OtsKey.ofIndex layer idx).leaf).run := by
  rw [signLayer_run] at h
  -- Name the one-time signature, so the match reduces without evaluating it.
  cases hots : (otsSign (pureHash f) pp prf (OtsKey.ofIndex layer idx) msg).run with
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
    (h : (signLayer (pureHash f) pp prf layer idx msg).run = .error e) :
    e = .noAdmissibleEncoding layer ∧
      (otsSign (pureHash f) pp prf (OtsKey.ofIndex layer idx) msg).run = none := by
  rw [signLayer_run] at h
  cases hots : (otsSign (pureHash f) pp prf (OtsKey.ofIndex layer idx) msg).run with
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

/-! ## Signatures -/

/-- A signature holds the randomizer, the FORS openings its digest picks, and three layers.

- `s` and `pp` are the scheme seed and the public parameter, from the secret key's seed.
- Every secret is a derivation from `s`.
- Each layer's key signs what the layer below gives. -/
theorem sign_eq_ok {s : Seed} {sk : SecretKey} {m : Message} {σ : Signature}
    (hs : (schemeSeed (pureHash f) sk.seed).run = s)
    (hpp : (publicParamOf (seedPrf (pureHash f) s)).run = pp)
    (h : (signWith (pureHash f) sk m).run = .ok σ) :
    let prf := seedPrf (pureHash f) s
    let d := (messageDigest (pureHash f) pp m σ.randomizer).run
    σ.randomizer = (randomizer pp prf m).run ∧
      σ.fors = (forsSign (pureHash f) pp prf (digestIndex d) (digestLeaves d)).run ∧
      (signLayer (pureHash f) pp prf .bottom (digestIndex d)
          (layerMessage (pureHash f) pp prf .bottom (digestIndex d)).run).run = .ok σ.bottom ∧
      (signLayer (pureHash f) pp prf .middle (digestIndex d)
          (layerMessage (pureHash f) pp prf .middle (digestIndex d)).run).run = .ok σ.middle ∧
      (signLayer (pureHash f) pp prf .top (digestIndex d)
          (layerMessage (pureHash f) pp prf .top (digestIndex d)).run).run = .ok σ.top := by
  subst hs hpp
  rw [signWith, Id.run_bind, Id.run_bind, signDerived_run] at h
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
  rw [signWith, Id.run_bind, Id.run_bind, signDerived_run] at h
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
