module

public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Proofs.Xmss.KeyGen
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Serialization

/-!
# Proofs: leanXMSS signing

What a successful signature holds, and how signing can fail.

Each theorem holds for every hash function `f`, run in the identity monad.

`sign` is the case `f = hash`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {s : Seed} {prf : SeedPrf Id}
  {layer : Layer} {e : Nat}
  {msg : ByteArray} {sig : LayerSignature}

/-! ## The signer as a value

`rw` unfolds the signer, not `simp`, as for the one-time signer. -/

/-- What a layer's signature computes: the one-time signature with the key's path, or the error. -/
theorem signLayer_run :
    (signLayer (pureHash f) pp prf layer e msg).run
      = match (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
        | none => .error (.noAdmissibleEncoding layer e)
        | some (randomizer, chainValues) =>
          .ok { randomizer, chainValues, path := (path (pureHash f) pp prf layer e).run } := by
  rw [signLayer, Id.run_bind]
  cases (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
  | none => rfl
  | some found => rfl

/-- What signing computes, one layer after the other, as a computation in `Except`.

- `s` and `pp` are the scheme seed and the public parameter, from the secret key's seed.
- Both layers derive their secrets from `s`.
- The top layer signs the root of bottom tree `b`, which signing builds. -/
theorem signWith_run {sk : SecretKey} {idx : LeafIndex} {m : Message}
    (hs : (schemeSeed (pureHash f) sk.seed).run = s)
    (hpp : (publicParamOf (seedPrf (pureHash f) s)).run = pp) :
    (signWith (pureHash f) sk idx m).run
      = (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
          (packBytes m)).run.bind fun bottom =>
          (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
            (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
              (bottomTree idx)).run)).run.bind fun top =>
            .ok { leafIndex := idx, bottom, top } := by
  subst hs hpp
  rw [signWith, Id.run_bind, Id.run_bind, signDerived, Id.run_bind]
  cases (signLayer (pureHash f)
      (publicParamOf (seedPrf (pureHash f) (schemeSeed (pureHash f) sk.seed).run)).run
      (seedPrf (pureHash f) (schemeSeed (pureHash f) sk.seed).run) .bottom idx.toNat
      (packBytes m)).run with
  | error err => rfl
  | ok bottom =>
    -- No signer is unfolded here, so `simp` may reduce the matches on `.ok`.
    simp only [Id.run_bind, Id.run_pure, Except.bind]
    cases (signLayer (pureHash f)
        (publicParamOf (seedPrf (pureHash f) (schemeSeed (pureHash f) sk.seed).run)).run
        (seedPrf (pureHash f) (schemeSeed (pureHash f) sk.seed).run) .top (bottomTree idx)
        (packBytes (node (pureHash f)
          (publicParamOf (seedPrf (pureHash f) (schemeSeed (pureHash f) sk.seed).run)).run
          (seedPrf (pureHash f) (schemeSeed (pureHash f) sk.seed).run) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run with
    | error err => rfl
    | ok top => rfl

/-! ## Layers -/

/-- A layer's signature is a one-time signature, with the key's honest path. -/
theorem signLayer_eq_ok (h : (signLayer (pureHash f) pp prf layer e msg).run = .ok sig) :
    (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run
        = some (sig.randomizer, sig.chainValues) ∧
      sig.path = (path (pureHash f) pp prf layer e).run := by
  rw [signLayer_run] at h
  -- Name the one-time signature, so the match reduces without evaluating it.
  cases hots : (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
  | none =>
    rw [hots] at h
    cases h
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [hots] at h
    -- The accepting branch packs the one-time signature with the path.
    cases h
    exact ⟨rfl, rfl⟩

/-- A layer fails only when no randomizer trial gives a codeword. -/
theorem signLayer_error {err : XmssError}
    (h : (signLayer (pureHash f) pp prf layer e msg).run = .error err) :
    (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run = none ∧
      err = .noAdmissibleEncoding layer e := by
  rw [signLayer_run] at h
  cases hots : (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
  | none =>
    rw [hots] at h
    cases h
    exact ⟨rfl, rfl⟩
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [hots] at h
    cases h

/-! ## Signatures -/

/-- A signature holds one honest signature per layer.

- The bottom key `idx` signs the message.
- The top key `b` signs the root of bottom tree `b`. -/
theorem sign_eq_ok {sk : SecretKey} {idx : LeafIndex} {m : Message} {σ : Signature}
    (hs : (schemeSeed (pureHash f) sk.seed).run = s)
    (hpp : (publicParamOf (seedPrf (pureHash f) s)).run = pp)
    (h : (signWith (pureHash f) sk idx m).run = .ok σ) :
    σ.leafIndex = idx ∧
      (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
        (packBytes m)).run = .ok σ.bottom ∧
      (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
        (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run = .ok σ.top := by
  rw [signWith_run hs hpp] at h
  -- Each layer is either an error, which propagates, or a value the next step uses.
  cases hbottom : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
      (packBytes m)).run with
  | error err =>
    rw [hbottom] at h
    cases h
  | ok bottom =>
    rw [hbottom, Except.bind] at h
    cases htop : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
        (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run with
    | error err =>
      rw [htop] at h
      cases h
    | ok top =>
      rw [htop] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩

/-- An encoded signature carries the leaf index it was signed at.

So a verifier that reads the index from the bytes learns which one-time key signed. -/
theorem signatureIndex_sign {sk : SecretKey} {idx : LeafIndex} {m : Message} {σ : Signature}
    (h : sign sk idx m = .ok σ) :
    signatureIndex (encodeSignature σ) = .ok idx := by
  rw [signatureIndex_encodeSignature, (sign_eq_ok rfl rfl h).1]

/-- Signing fails only when one layer's one-time key finds no codeword. -/
theorem sign_error {sk : SecretKey} {idx : LeafIndex} {m : Message} {err : XmssError}
    (h : (signWith (pureHash f) sk idx m).run = .error err) :
    ∃ layer key, err = .noAdmissibleEncoding layer key := by
  -- Name the scheme seed and the parameter, so the layers stay short.
  obtain ⟨s, hs⟩ : ∃ s, (schemeSeed (pureHash f) sk.seed).run = s := ⟨_, rfl⟩
  obtain ⟨pp, hpp⟩ : ∃ pp, (publicParamOf (seedPrf (pureHash f) s)).run = pp := ⟨_, rfl⟩
  rw [signWith_run hs hpp] at h
  -- The error comes from one of the two layers.
  cases hbottom : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
      (packBytes m)).run with
  | error e' =>
    rw [hbottom] at h
    cases h
    exact ⟨_, _, (signLayer_error hbottom).2⟩
  | ok bottom =>
    rw [hbottom, Except.bind] at h
    cases htop : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
        (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run with
    | error e' =>
      rw [htop] at h
      cases h
      exact ⟨_, _, (signLayer_error htop).2⟩
    | ok top =>
      rw [htop] at h
      cases h

end EthLib.Cryptography.Xmss
