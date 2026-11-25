module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Signer
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Deterministic.TranscriptReduction
public import
  EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Deterministic.KeyedErasure
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Adversary

/-!
# EthLib's game as the model's

After key generation, EthLib's game is the model's game.

The adversary is translated as in `XmssSecurity/Adversary.lean`.

So the two games win equally often, and the model's makes at most the hash calls of EthLib's.
-/

@[expose] public section

open OracleComp OracleSpec
open EthLib.Cryptography
open EthLib.Cryptography.Xmss.Unforgeability (queryH ofParam ofSeed ofDigest ofLeafIndex ofMessage
  ofSignature ofPublicKey toLeafIndex toMessage toSignature toModelAdversary toModelForgery
  toModelRequest adversaryImpl ofEntry)

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

/- A concrete height would let Lean unfold a whole tree, so the height stays opaque. -/
attribute [local irreducible] EthLib.Cryptography.Xmss.Constants.LAYER_HEIGHT

/-! ## Erasures and liftings -/

/-- Lifting a map of a hash computation maps its lift. -/
theorem liftM_hash_map {α β : Type} (f : α → β) (c : OracleComp HashSpec α) :
    (liftM (f <$> c) : OracleComp OracleWorld β) = f <$> (liftM c : OracleComp OracleWorld α) := by
  rw [map_eq_bind_pure_comp, liftM_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_def, liftM_pure]

/-- The random oracle runs a lifted hash computation as the hash oracle runs it. -/
theorem lift_hash_romImpl {α : Type} (c : OracleComp HashSpec α) :
    simulateQ romImpl (liftM c : OracleComp OracleWorld α) = simulateQ randomOracle c :=
  QueryImpl.simulateQ_add_liftM_right _ _ c

/-! ## EthLib's game after key generation -/

/-- EthLib's oracles: coins and hashes pass through, and a request signs with the kept key. -/
noncomputable abbrev keyedOracles : QueryImpl (OracleWorld + Xmss.Unforgeability.SigningSpec)
    (StateT Xmss.SecretKey
      (WriterT (QueryLog Xmss.Unforgeability.SigningSpec) (OracleComp OracleWorld))) :=
  QueryImpl.ofLift OracleWorld (StateT Xmss.SecretKey
      (WriterT (QueryLog Xmss.Unforgeability.SigningSpec) (OracleComp OracleWorld))) +
    SufCma.signingOracle Xmss.Unforgeability.scheme

/-- The game after key generation: the adversary's run with its key forgotten, then the check. -/
theorem gameAfterKeys_eq (adversary : Xmss.Unforgeability.Adversary) (pk : Xmss.PublicKey)
    (sk : Xmss.SecretKey) :
    SufCma.gameAfterKeys Xmss.Unforgeability.scheme adversary pk sk =
      (forgetState <$> ((simulateQ keyedOracles (adversary.main pk)).run sk).run) >>=
        SufCma.checkForgery Xmss.Unforgeability.scheme pk := by
  rw [bind_map_left]
  rfl

/-- The model's game after key generation: the translated run, then EthLib's check.

The forgery wins in one game exactly when its translation wins in the other. -/
theorem gameRest_eq (adversary : Xmss.Unforgeability.Adversary) (d : Derivations)
    (result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec) :
    Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary) (modelPublicKey d result)
        (modelSecretKey d result) =
      (translateLog ofEntry <$> (simulateQ ((forwardOracles + signingOracle (tableScheme d.rnd)
          (modelSecretKey d result)) ∘ₛ adversaryImpl)
          (adversary.main (ofPublicKey (modelPublicKey d result)))).run) >>=
        SufCma.checkForgery Xmss.Unforgeability.scheme (ofPublicKey (modelPublicKey d result)) := by
  unfold Seeded.gameRest toModelAdversary
  simp only [simulateQ_map, WriterT.run_map', ← QueryImpl.simulateQ_compose]
  -- `erw`: the `<$>` is the free monad's functor.
  erw [bind_map_left]
  refine Eq.trans ?_ (bind_map_left _ _ _).symm
  refine bind_congr fun p => ?_
  -- The verifier is the model's, on the translated forgery.
  have hverify :
      (Xmss.verifyWith queryH (ofPublicKey (modelPublicKey d result)) p.1.message p.1.signature :
        OracleComp HashSpec Bool)
      = Concrete.verify (modelPublicKey d result) (toLeafIndex p.1.signature.leafIndex)
        (toMessage p.1.message) (toSignature p.1.signature) := by
    rw [← Xmss.Unforgeability.verifyWith_queryH, Xmss.Unforgeability.ofMessage_toMessage,
      Xmss.Unforgeability.ofSignature_toSignature]
  -- So is the winning condition.
  have hwin : decide (Xmss.Unforgeability.Valid (p.2.map ofEntry) ∧
        ¬SufCma.Returned Xmss.Unforgeability.scheme (p.2.map ofEntry) p.1)
      = decide (SigningTranscript.Valid p.2 ∧
          ¬SigningTranscript.Contains p.2 (toModelForgery p.1)) :=
    decide_eq_decide.mpr (and_congr (Xmss.Unforgeability.valid_map _)
      (not_congr (Xmss.Unforgeability.returned_map _ _)))
  simp only [tableScheme, Concrete.scheme, SufCma.checkForgery,
    Xmss.Unforgeability.scheme, translateLog]
  rw [hverify]
  exact (bind_congr fun verified => congrArg (fun b => pure (b && verified)) hwin).symm

/-- A coin or hash query of EthLib's game passes through, and leaves the key as it is. -/
theorem run_keyedOracles_inl (t : OracleWorld.Domain) (sk : Xmss.SecretKey) :
    ((keyedOracles (.inl t)).run sk).run =
      (fun u => ((u, sk), ([] : QueryLog Xmss.Unforgeability.SigningSpec))) <$>
        (liftM (OracleWorld.query t) : OracleComp OracleWorld _) := by
  simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
  rfl

/-- A request of EthLib's game signs with the kept key, and logs the signature or its absence. -/
theorem run_keyedOracles_inr (request : Xmss.Unforgeability.SignRequest) (sk : Xmss.SecretKey) :
    ((keyedOracles (.inr request)).run sk).run =
      (fun r => ((r.1.toOption, r.2), [⟨request, r.1.toOption⟩])) <$>
        (liftM (Xmss.signWith Xmss.Unforgeability.H sk request.leafIndex
          request.message) : OracleComp OracleWorld _) := by
  simp only [QueryImpl.add_apply_inr, SufCma.signingOracle, Xmss.Unforgeability.scheme,
    StateT.run_mk, WriterT.run_mk, Functor.map_map]

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec} {sk : Xmss.SecretKey}

/-- Each query of EthLib's game, with a key the cache knows, erases to the model's.

The key is forgotten, and the model's log is translated. -/
theorem erases_oracles (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    (input : (OracleWorld + Xmss.Unforgeability.SigningSpec).Domain) :
    Erases (worldKnown cache) (forgetState <$> ((keyedOracles input).run sk).run)
      (translateLog ofEntry <$>
        (((forwardOracles + signingOracle (tableScheme d.rnd) (modelSecretKey d result)) ∘ₛ
          adversaryImpl) input).run) := by
  cases input with
  | inl input =>
      have hleft : forgetState <$> ((keyedOracles (.inl input)).run sk).run =
          (fun a => (a, ([] : QueryLog Xmss.Unforgeability.SigningSpec))) <$>
            (liftM (OracleWorld.query input) : OracleComp OracleWorld _) := by
        rw [run_keyedOracles_inl, Functor.map_map]
        rfl
      rw [hleft]
      simp only [QueryImpl.add_apply_inl, QueryImpl.apply_compose, adversaryImpl,
        simulateQ_spec_query, forwardOracles]
      show Erases _ ((fun a => (a, ([] : QueryLog Xmss.Unforgeability.SigningSpec))) <$>
          (liftM (OracleWorld.query input) : OracleComp OracleWorld _))
        (translateLog ofEntry <$> ((fun a => (a, ([] : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query input) : OracleComp OracleWorld _)))
      rw [Functor.map_map]
      exact .refl _ _
  | inr request =>
      have hleft : forgetState <$> ((keyedOracles (.inr request)).run sk).run =
          (liftM ((fun r => r.1.toOption) <$>
            Xmss.signWith (queryH (m := OracleComp HashSpec)) sk request.leafIndex
              request.message) : OracleComp OracleWorld _) >>= fun u =>
            pure (u, [(⟨request, u⟩ :
              (_ : Xmss.Unforgeability.SignRequest) × Option Xmss.Signature)]) := by
        rw [liftM_hash_map, bind_map_left, run_keyedOracles_inr, Functor.map_map,
          map_eq_bind_pure_comp]
        rfl
      rw [hleft]
      simp only [QueryImpl.add_apply_inr, QueryImpl.apply_compose, adversaryImpl, simulateQ_map,
        simulateQ_spec_query, WriterT.run_map', signingOracle,
        QueryImpl.run_withLogging_apply, tableScheme]
      -- The request is the translation of its model request.
      have hidx : ofLeafIndex (toModelRequest request).leafIndex = request.leafIndex := by
        simp [toModelRequest]
      have hmsg : ofMessage (toModelRequest request).message = request.message := by
        simp [toModelRequest]
      have key := (h.erases_signWith hk (toModelRequest request).leafIndex
        (toModelRequest request).message).lift_hash.bind
        (fun u => (pure (u, [(⟨request, u⟩ :
          (_ : Xmss.Unforgeability.SignRequest) × Option Xmss.Signature)]) :
          OracleComp OracleWorld _))
        (fun u => (pure (u, [(⟨request, u⟩ :
          (_ : Xmss.Unforgeability.SignRequest) × Option Xmss.Signature)]) :
          OracleComp OracleWorld _)) fun u => .pure _
      rw [hidx, hmsg] at key
      refine (congrArg₂ (Erases (worldKnown cache)) rfl ?_).mpr key
      -- `erw`: the oracle's `<$>` is the free monad's functor, the lemmas' the monad's.
      erw [liftM_hash_map, bind_map_left, map_bind]
      refine Eq.trans (map_bind _ _ _) (bind_congr fun a => ?_)
      erw [map_pure]
      simp [ofEntry, toModelRequest, translateLog]

/-- Each query of EthLib's game, with a key the cache knows, returns a key the cache knows. -/
theorem keyResolves_oracles (h : Prepared seed d result cache)
    (input : (OracleWorld + Xmss.Unforgeability.SigningSpec).Domain) (sk : Xmss.SecretKey)
    (c : QueryCache HashSpec) (hk : KeyResolves seed d cache sk) (hc : cache ≤ c) :
    ∀ x ∈ support ((simulateQ romImpl ((keyedOracles input).run sk).run).run c),
      KeyResolves seed d cache x.1.1.2 := by
  intro x hx
  cases input with
  | inl t =>
    rw [run_keyedOracles_inl, simulateQ_map, StateT.run_map, support_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hk
  | inr request =>
    rw [run_keyedOracles_inr, simulateQ_map, StateT.run_map, support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [lift_hash_romImpl] at hy
    exact h.keyResolves_signWith hk (hc.trans (cache_le_of_run _ _ _ hy)) _ _
      (resolves_of_run _ _ _ hy)

/-- **After key generation, EthLib's game wins as the model's, in distribution.**

The key must be one the cache knows, such as the key of key generation. -/
theorem evalDist_rest (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    (adversary : Xmss.Unforgeability.Adversary) :
    (simulateQ romImpl (SufCma.gameAfterKeys Xmss.Unforgeability.scheme adversary
      (ofPublicKey (modelPublicKey d result)) sk)).run'
        cache =ᵈ
      (simulateQ romImpl (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
        (modelPublicKey d result) (modelSecretKey d result))).run' cache := by
  -- EthLib's signer keeps its key across requests, and the model's game uses the table signer.
  rw [gameAfterKeys_eq, gameRest_eq]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_map_left]
  -- The prepared cache knows the key of key generation.
  --
  -- Signing keeps it a key the cache knows.
  --
  -- Under that cache, each request of EthLib's game erases to the model's.
  have hrun := evalDist_simulateQ_state cache (fun sk => KeyResolves seed d cache sk)
    keyedOracles _ ofEntry (fun q _ hs => h.erases_oracles hs q)
    (fun q sk c hs hc => h.keyResolves_oracles q sk c hs hc)
    (adversary.main (ofPublicKey (modelPublicKey d result))) sk cache hk le_rfl
  -- The transcripts correspond entry by entry.
  have hbind := hrun.bind_left fun z =>
    Prod.fst <$> (simulateQ romImpl (SufCma.checkForgery Xmss.Unforgeability.scheme
      (ofPublicKey (modelPublicKey d result)) z.1)).run
      z.2
  simp only [bind_map_left] at hbind
  exact hbind

/-- **After key generation, the model's game makes at most the hash calls of EthLib's.**

The key must be one the cache knows, such as the key of key generation. -/
theorem hashQueryBound_rest (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    (adversary : Xmss.Unforgeability.Adversary) (q : Nat)
    (hbound : HashQueryBound (SufCma.gameAfterKeys Xmss.Unforgeability.scheme adversary
      (ofPublicKey (modelPublicKey d result)) sk)
      cache q) :
    HashQueryBound (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
      (modelPublicKey d result) (modelSecretKey d result)) cache q := by
  rw [gameAfterKeys_eq] at hbound
  rw [gameRest_eq]
  refine hashQueryBound_bind_of_costWorld_le _ cache q (fun y hy => ?_) hbound
  rw [simulateQ_map, StateT.run_map, support_map] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  obtain ⟨x, hx, h1, h2, h3⟩ := costWorld_le_simulateQ_state cache
    (fun sk => KeyResolves seed d cache sk) keyedOracles _ ofEntry
    (fun q _ hs => h.erases_oracles hs q) (fun q sk c hs hc => h.keyResolves_oracles q sk c hs hc)
    (adversary.main (ofPublicKey (modelPublicKey d result))) sk cache hk le_rfl 0 y hy
  refine ⟨(forgetState x.1, x.2), ?_, h1, h2, h3⟩
  rw [simulateQ_map, StateT.run_map, support_map]
  exact ⟨x, hx, rfl⟩

end Prepared

end XmssSecurity.Bridge
