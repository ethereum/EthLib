module

public import EthLib.Cryptography.Proofs.Xmss.Reference
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RegisteredDigest

/-!
# The two message trials selected by a successful signature

The leanXMSS draft in "The scheme", paragraph "Signing", signs the bottom tree's root at the top.

The same tree gives the bottom authentication path, so recording the root needs no further hash.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning

open Constants HashSig OracleSpec OracleComp CachedCodeword

/-- Keep the signed root from the one tree built by the reference signer. -/
@[expose] def signWithRoot {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
    (prf : SeedPrf m) (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    m (Except XmssError (Signature × Digest)) := do
  let some (rho, chains) ← otsSign H pp prf .bottom (UInt32.ofNat idx.toNat) (packBytes msg)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let tree ← build H pp prf .bottom LAYER_HEIGHT (bottomTree idx)
  let bottom : LayerSignature := ⟨rho, chains, tree.path LAYER_HEIGHT idx.toNat⟩
  -- Keep the value passed to the top signer only when both layers succeed.
  let reply ← signLayer H pp prf .top (bottomTree idx) (packBytes tree.value)
  return reply.map fun top => (⟨idx, bottom, top⟩, tree.value)

/-- Dropping the retained root recovers the exact signing computation, including failed calls. -/
theorem signWithRoot_project {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : ByteArray → m (Vector UInt8 32)) (prf : SeedPrf m) (pp : PublicParam)
    (idx : LeafIndex) (msg : Message) :
    Except.map Prod.fst <$> signWithRoot H prf pp idx msg = signDerived H prf pp idx msg := by
  simp only [signWithRoot, signDerived, map_bind]
  congr 1
  funext o
  rcases o with _ | ⟨rho, chains⟩
  · simp [Except.map]
  · simp only [map_bind]
    congr 1
    funext tree
    congr 1
    funext reply
    cases reply <;> simp [Except.map]

/-- Register both physical trial addresses after a successful reply. -/
@[expose] def notify (pp : PublicParam) (msg : Message)
    (out : Except XmssError (Signature × Digest)) :
    OracleComp WatchQueries (Except XmssError Signature) :=
  match out with
  | .error err => pure (.error err)
  | .ok (sig, root) => do
    let i := sig.leafIndex
    let _ ← query (spec := WatchQueries) (.inr
      (trialInput pp .bottom (UInt32.ofNat i.toNat) (packBytes msg) sig.bottom.randomizer))
    let _ ← query (spec := WatchQueries) (.inr
      (trialInput pp .top (UInt32.ofNat (bottomTree i)) (packBytes root) sig.top.randomizer))
    return .ok sig

/-- Erase a registration before counting the signer's original oracle operations. -/
abbrev forget : QueryImpl WatchQueries (OracleComp OracleWorld) := randomOracle.Targets.forget

/-- Erasing both notices preserves the exact reply, even when either search fails. -/
theorem forget_notify (pp : PublicParam) (msg : Message)
    (out : Except XmssError (Signature × Digest)) :
    simulateQ forget (notify pp msg out) = pure (out.map Prod.fst) := by
  rcases out with err | ⟨sig, root⟩ <;> simp [notify, forget, randomOracle.Targets.forget, Except.map]

/-- Extend the actual signing run with notices for its two successful trials. -/
@[expose] def signingTargets (H : ByteArray → OracleComp OracleWorld (Vector UInt8 32))
    (prf : SeedPrf (OracleComp OracleWorld)) (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    OracleComp WatchQueries (Except XmssError Signature) := do
  let out ← simulateQ (fun t => query (spec := WatchQueries) (.inl t)) (signWithRoot H prf pp idx msg)
  notify pp msg out

/-- Every interpreter, including the original hash meter, sees the exact original signer. -/
theorem forget_signingTargets (H : ByteArray → OracleComp OracleWorld (Vector UInt8 32))
    (prf : SeedPrf (OracleComp OracleWorld)) (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    simulateQ forget (signingTargets H prf pp idx msg) = signDerived H prf pp idx msg := by
  unfold signingTargets
  rw [simulateQ_bind, ← QueryImpl.simulateQ_compose]
  have same : QueryImpl.compose forget
      (fun t => query (spec := WatchQueries) (.inl t) :
        QueryImpl OracleWorld (OracleComp WatchQueries)) =
      QueryImpl.id' OracleWorld := by
    funext t
    simp [QueryImpl.compose, forget, randomOracle.Targets.forget]
  rw [same, simulateQ_id' (signWithRoot H prf pp idx msg)]
  simp_rw [forget_notify]
  exact (map_eq_pure_bind _ _).symm.trans (signWithRoot_project H prf pp idx msg)

/-- Erasing both watches gives the native signer and its entire ordinary cache. -/
theorem signingTargets_run (H : ByteArray → OracleComp OracleWorld (Vector UInt8 32))
    (prf : SeedPrf (OracleComp OracleWorld)) (pp : PublicParam) (idx : LeafIndex)
    (msg : Message) (s : WatchState) :
    (fun z => (z.1, z.2.cache)) <$>
        (simulateQ (randomOracle.Targets.impl (record pp) (messageKey pp) low)
          (signingTargets H prf pp idx msg)).run s =
      (simulateQ HashSpec.romImpl (signDerived H prf pp idx msg)).run s.cache := by
  rw [randomOracle.Targets.forget_run]
  exact congrArg (fun c => (simulateQ HashSpec.romImpl c).run s.cache)
    (forget_signingTargets H prf pp idx msg)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning
