import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Statement
import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity

/-!
# Proofs: EthLib's game is the security proof's game

An adversary of EthLib's game becomes an adversary of the proof's game.

It speaks bytes and the proof speaks bit vectors.

So its requests, answers and forgery are translated.

The two games then differ in one place.

EthLib's signer gets the seed `S_0` and re-derives `S` and `P` with two hash calls.

The proof's signer keeps `S` and `P`.

Key generation made those two calls first, so the random oracle has their answers cached.

So the two extra calls return what the proof's signer holds, change nothing, and only cost budget.

```text
    EthLib :  S_0, hash S, hash P, tree, adversary, verify
                                         signer: 2 cached calls, then sign
    proof  :  S_0, hash S, hash P, tree, adversary, verify
                                         signer: sign
```

Hence both games win with the same probability, and the proof's game spends at most EthLib's budget.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-! ## From bytes to bit vectors

Values from the adversary go to the proof through their integers. -/

/-- A leaf index as the proof writes it. -/
def toLeafIndex (idx : LeafIndex) : LeanXmss.LeafIndex :=
  ⟨idx.toNat, by
    simpa [LeanXmss.lifetime, LeanXmss.numLayers, LeanXmss.layerHeight] using idx.toNat_lt⟩

/-- A message as the proof writes it. -/
def toMessage (msg : Message) : LeanXmss.Message :=
  BitVec.ofNat _ (fromLittleEndian msg)

/-- A digest as the proof writes it. -/
def toDigest (d : Digest) : LeanXmss.Digest :=
  BitVec.ofNat _ (fromLittleEndian d)

/-- One layer's signature as the proof writes it. -/
def toLayerSig (s : LayerSignature) : LeanXmss.LayerSignature where
  randomness := BitVec.ofNat _ (fromLittleEndian s.randomizer)
  chainValues i := toDigest s.chainValues[i.val]
  path l := toDigest s.path[l.val]

/-- A signature as the proof writes it. -/
def toSignature (σ : Signature) : LeanXmss.Signature where
  leafIndex := toLeafIndex σ.leafIndex
  layers l := if l = LeanXmss.bottomLayer then toLayerSig σ.bottom else toLayerSig σ.top

@[simp] theorem ofLeafIndex_toLeafIndex (idx : LeafIndex) :
    ofLeafIndex (toLeafIndex idx) = idx := by
  apply UInt32.toNat.inj
  simp [toLeafIndex]

@[simp] theorem toLeafIndex_ofLeafIndex (idx : LeanXmss.LeafIndex) :
    toLeafIndex (ofLeafIndex idx) = idx := by
  apply Fin.ext
  simp [toLeafIndex]

@[simp] theorem ofMessage_toMessage (msg : Message) : ofMessage (toMessage msg) = msg :=
  ofBV_ofNat_fromLittleEndian msg (by simp [MESSAGE_LEN])

@[simp] theorem toMessage_ofMessage (msg : LeanXmss.Message) : toMessage (ofMessage msg) = msg :=
  ofBV_inj (n := MESSAGE_LEN) (by simp [MESSAGE_LEN]) (ofMessage_toMessage _)

@[simp] theorem ofDigest_toDigest (d : Digest) : ofDigest (toDigest d) = d :=
  ofBV_ofNat_fromLittleEndian d (by simp [DIGEST_LEN, LeanXmss.digestBits])

@[simp] theorem toDigest_ofDigest (d : LeanXmss.Digest) : toDigest (ofDigest d) = d :=
  ofBV_inj (n := DIGEST_LEN) (by simp [DIGEST_LEN, LeanXmss.digestBits]) (ofDigest_toDigest _)

theorem ofLayerSig_toLayerSig (s : LayerSignature) : ofLayerSig (toLayerSig s) = s := by
  obtain ⟨rho, y, pi⟩ := s
  simp only [ofLayerSig, toLayerSig, LayerSignature.mk.injEq]
  refine ⟨ofBV_ofNat_fromLittleEndian rho (by simp [RANDOMIZER_LEN, LeanXmss.digestBits]), ?_, ?_⟩
  · exact Vector.ext fun i hi => by simp [ofChains, chainOf]
  · exact Vector.ext fun i hi => by simp [ofPath]

theorem toLayerSig_ofLayerSig (s : LeanXmss.LayerSignature) : toLayerSig (ofLayerSig s) = s := by
  obtain ⟨rho, y, pi⟩ := s
  simp only [ofLayerSig, toLayerSig, LeanXmss.LayerSignature.mk.injEq]
  refine ⟨ofBV_inj (n := RANDOMIZER_LEN) (by simp [RANDOMIZER_LEN, LeanXmss.digestBits])
    (ofBV_ofNat_fromLittleEndian _ (by simp [RANDOMIZER_LEN, LeanXmss.digestBits])), ?_, ?_⟩
  · funext i
    simp [ofChains, chainOf]
  · funext l
    simp [ofPath]

@[simp] theorem ofSignature_toSignature (σ : Signature) : ofSignature (toSignature σ) = σ := by
  obtain ⟨idx, bottom, top⟩ := σ
  simp [ofSignature, toSignature, ofLayerSig_toLayerSig, LeanXmss.bottomLayer, LeanXmss.topLayer]

@[simp] theorem toSignature_ofSignature (σ : LeanXmss.Signature) :
    toSignature (ofSignature σ) = σ := by
  obtain ⟨idx, layers⟩ := σ
  simp only [toSignature, ofSignature, toLeafIndex_ofLeafIndex, toLayerSig_ofLayerSig,
    LeanXmss.Signature.mk.injEq, true_and]
  funext l
  -- A layer is the bottom or the top one.
  match l with
  | ⟨0, _⟩ => simp [LeanXmss.bottomLayer]
  | ⟨1, _⟩ => simp [LeanXmss.bottomLayer, LeanXmss.topLayer]

theorem ofLeafIndex_injective : Function.Injective ofLeafIndex := fun a b h => by
  rw [← toLeafIndex_ofLeafIndex a, h, toLeafIndex_ofLeafIndex]

theorem ofSignature_eq_iff (σ : LeanXmss.Signature) (τ : Signature) :
    ofSignature σ = τ ↔ σ = toSignature τ :=
  ⟨fun h => by rw [← h, toSignature_ofSignature], fun h => by rw [h, ofSignature_toSignature]⟩

theorem ofMessage_eq_iff (x : LeanXmss.Message) (msg : Message) :
    ofMessage x = msg ↔ x = toMessage msg :=
  ⟨fun h => by rw [← h, toMessage_ofMessage], fun h => by rw [h, ofMessage_toMessage]⟩

/-! ## The adversary -/

/-- A request as the proof writes it. -/
def toModelRequest (request : SignRequest) : LeanXmss.SignRequest :=
  ⟨toLeafIndex request.leafIndex, toMessage request.message⟩

/-- A forgery as the proof writes it. -/
def toModelForgery (forgery : Forgery) : LeanXmss.Forgery :=
  ⟨toMessage forgery.message, toSignature forgery.signature⟩

/-- The adversary's oracles, answered by the proof's.

Hash queries and coins pass through.

Each request is translated, and so is each signature it returns. -/
def adversaryImpl :
    QueryImpl (LeanXmss.OracleWorld + SigningSpec)
      (OracleComp (LeanXmss.OracleWorld + LeanXmss.SigningSpec))
  | .inl input => liftM ((LeanXmss.OracleWorld + LeanXmss.SigningSpec).query (.inl input))
  | .inr request => Option.map ofSignature <$>
      liftM ((LeanXmss.OracleWorld + LeanXmss.SigningSpec).query (.inr (toModelRequest request)))

/-- EthLib's adversary as one of the proof's game. -/
noncomputable def toModelAdversary (adversary : Adversary) : LeanXmss.Security.Adversary where
  main pk := toModelForgery <$> simulateQ adversaryImpl (adversary.main (ofPublicKey pk))

/-- A transcript entry of the proof's game as EthLib's. -/
def ofEntry (entry : (_ : LeanXmss.SignRequest) × Option LeanXmss.Signature) :
    (_ : SignRequest) × Option Signature :=
  ⟨⟨ofLeafIndex entry.1.leafIndex, ofMessage entry.1.message⟩, entry.2.map ofSignature⟩

/-- The translated transcript repeats a leaf index exactly when the proof's does. -/
theorem valid_map (log : QueryLog LeanXmss.SigningSpec) :
    Valid (log.map ofEntry) ↔ LeanXmss.SigningTranscript.Valid log := by
  -- The translated leaf indices are the proof's, each through `ofLeafIndex`, which is injective.
  have hmap : (log.map ofEntry).map (fun entry => entry.1.leafIndex)
      = (log.map fun entry => entry.1.leafIndex).map ofLeafIndex := by
    simp only [List.map_map]
    rfl
  rw [Valid, hmap, List.nodup_map_iff ofLeafIndex_injective]

/-- The translated transcript holds the forgery exactly when the proof's holds its translation. -/
theorem contains_map (log : QueryLog LeanXmss.SigningSpec) (forgery : Forgery) :
    Contains (log.map ofEntry) forgery ↔
      LeanXmss.SigningTranscript.Contains log (toModelForgery forgery) := by
  simp only [Contains, LeanXmss.SigningTranscript.Contains, List.mem_map, toModelForgery]
  constructor
  · rintro ⟨_, ⟨entry, hentry, rfl⟩, hmessage, hsignature⟩
    obtain ⟨request, answer⟩ := entry
    cases answer with
    | none => simp [ofEntry] at hsignature
    | some signature =>
      simp only [ofEntry, Option.map_some, Option.some.injEq] at hmessage hsignature
      exact ⟨⟨request, some signature⟩, hentry, (ofMessage_eq_iff _ _).mp hmessage,
        congrArg some ((ofSignature_eq_iff _ _).mp hsignature)⟩
  · rintro ⟨entry, hentry, hmessage, hsignature⟩
    refine ⟨ofEntry entry, ⟨entry, hentry, rfl⟩, ?_, ?_⟩
    · simp only [ofEntry, hmessage, ofMessage_toMessage]
    · simp only [ofEntry, hsignature, Option.map_some, ofSignature_toSignature]

/-! ## EthLib's game after key generation -/

open XmssSecurity XmssSecurity.Bridge XmssSecurity.Seeded

/-- EthLib's game once the keys exist: the adversary with its oracles, then the verification. -/
noncomputable def ethRest (adversary : Adversary) (sk : SecretKey) (pk : PublicKey) :
    OracleComp LeanXmss.OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift LeanXmss.OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp LeanXmss.OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return decide (Valid log ∧ ¬Contains log forgery) && verified

/-- The game's `H` is `queryH`, at the hash oracle. -/
theorem H_eq_queryH : H = queryH (m := OracleComp LeanXmss.HashSpec) :=
  rfl

/-- Lifting a hash computation into the game's oracles commutes with mapping its result. -/
theorem liftM_map_hash {α β : Type} (f : α → β) (c : OracleComp LeanXmss.HashSpec α) :
    (liftM (f <$> c) : OracleComp LeanXmss.OracleWorld β)
      = f <$> (liftM c : OracleComp LeanXmss.OracleWorld α) := by
  rw [map_eq_bind_pure_comp, liftM_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_def, liftM_pure]

/-- EthLib's game samples the proof's seed and runs the proof's key generation. -/
theorem gameCore_eq_keygen (adversary : Adversary) :
    gameCore adversary
      = (liftM LeanXmss.sampleMasterSeed : OracleComp LeanXmss.OracleWorld _) >>= fun S0 =>
          (liftM (LeanXmss.Seeded.keygenFromSeed S0) : OracleComp LeanXmss.OracleWorld _)
            >>= fun keys => ethRest adversary ⟨ofSeed S0⟩ (ofPublicKey keys.1) := by
  unfold gameCore sampleSeed
  rw [liftM_map, bind_map_left]
  refine bind_congr fun S0 => ?_
  rw [H_eq_queryH, keyGenWith_queryH,
    liftM_map_hash, bind_map_left]
  rfl

/-! ## The two calls the signer repeats -/

/-- The input of `S = H("leanXMSS" | S_0)`. -/
abbrev seedInput (S0 : LeanXmss.MasterSeed) : LeanXmss.HashInput := LeanXmss.seedHashInput S0

/-- The input of `P = Th(0^128, A_param, S)`. -/
abbrev paramInput (S : LeanXmss.MasterSeed) : LeanXmss.HashInput :=
  LeanXmss.keygenHashInput 0 .parameter S

/-- The oracle's answers to the two calls of key generation that the signer repeats. -/
def knownKeys (S0 S : LeanXmss.MasterSeed) (Pf : LeanXmss.HashOutput) :
    QueryCache LeanXmss.HashSpec :=
  ((∅ : QueryCache LeanXmss.HashSpec).cacheQuery (seedInput S0) S).cacheQuery (paramInput S) Pf

theorem knownKeys_seedInput (S0 S : LeanXmss.MasterSeed) (Pf : LeanXmss.HashOutput) :
    knownKeys S0 S Pf (seedInput S0) = some S := by
  rw [knownKeys,
    QueryCache.cacheQuery_of_ne _ _ (LeanXmss.seedHashInput_ne_keygen S0 0 .parameter S),
    QueryCache.cacheQuery_self]

theorem knownKeys_paramInput (S0 S : LeanXmss.MasterSeed) (Pf : LeanXmss.HashOutput) :
    knownKeys S0 S Pf (paramInput S) = some Pf := by
  rw [knownKeys, QueryCache.cacheQuery_self]

/-- EthLib's signer erases to the proof's.

The cache answers its two calls for `S` and `P`. -/
theorem erases_signWith (S0 S : LeanXmss.MasterSeed) (Pf : LeanXmss.HashOutput) (idx : LeafIndex)
    (msg : Message) :
    Erases (knownKeys S0 S Pf) (Except.toOption <$> signWith H ⟨ofSeed S0⟩ idx msg)
      (Option.map ofSignature <$>
        LeanXmss.Seeded.sign ⟨S, LeanXmss.truncateHash Pf⟩ (toLeafIndex idx) (toMessage msg)) := by
  rw [← ofLeafIndex_toLeafIndex idx, ← ofMessage_toMessage msg, H_eq_queryH,
    signWith_queryH, toLeafIndex_ofLeafIndex, toMessage_ofMessage]
  -- The seed hash is cached: skip it.
  refine Erases.skip (seedInput S0) S (knownKeys_seedInput S0 S Pf) _ _ ?_
  -- The parameter's hash is cached: skip it.
  -- `P` is the first 16 bytes of the hash of the parameter's input.
  rw [LeanXmss.Concrete.th, bind_assoc]
  simp only [pure_bind]
  refine Erases.skip (paramInput S) Pf (knownKeys_paramInput S0 S Pf) _ _ ?_
  exact Erases.refl _ _

/-! ## The adversary's run -/

-- The proof's lemmas type a hash value `BitVec hashOutputBits`, and its statement `BitVec 256`.
-- As in the proof's own bridge, definitional checks may unfold the width to match them.
set_option backward.isDefEq.respectTransparency false in
/-- Each oracle of EthLib's adversary erases to the proof's.

Its answer and its log entry are translated. -/
theorem erases_oracles (S0 S : LeanXmss.MasterSeed) (Pf : LeanXmss.HashOutput)
    (input : (LeanXmss.OracleWorld + SigningSpec).Domain) :
    Erases (worldKnown (knownKeys S0 S Pf))
      ((QueryImpl.ofLift LeanXmss.OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp LeanXmss.OracleWorld)) +
          signingOracle ⟨ofSeed S0⟩) input).run
      ((fun p => (p.1, p.2.map ofEntry)) <$>
        (((QueryImpl.ofLift LeanXmss.OracleWorld
          (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp LeanXmss.OracleWorld)) +
            LeanXmss.Security.signingOracle ⟨S, LeanXmss.truncateHash Pf⟩) ∘ₛ adversaryImpl)
          input).run) := by
  cases input with
  | inl input =>
    simp only [QueryImpl.add_apply_inl, QueryImpl.apply_compose, adversaryImpl,
      simulateQ_spec_query, QueryImpl.ofLift_apply]
    show Erases _ ((fun a => (a, ([] : QueryLog SigningSpec))) <$>
        (liftM (LeanXmss.OracleWorld.query input) : OracleComp LeanXmss.OracleWorld _))
      ((fun p => (p.1, p.2.map ofEntry)) <$>
        ((fun a => (a, ([] : QueryLog LeanXmss.SigningSpec))) <$>
        (liftM (LeanXmss.OracleWorld.query input) : OracleComp LeanXmss.OracleWorld _)))
    rw [Functor.map_map]
    exact .refl _ _
  | inr request =>
    simp only [QueryImpl.add_apply_inr, QueryImpl.apply_compose, adversaryImpl, simulateQ_map,
      simulateQ_spec_query, WriterT.run_map', LeanXmss.Security.signingOracle, signingOracle,
      QueryImpl.run_withLogging_apply]
    have key := (erases_signWith S0 S Pf request.leafIndex request.message).lift_hash.bind
      (fun u => (pure (u, [(⟨request, u⟩ : (_ : SignRequest) × Option Signature)]) :
        OracleComp LeanXmss.OracleWorld _))
      (fun u => (pure (u, [(⟨request, u⟩ : (_ : SignRequest) × Option Signature)]) :
        OracleComp LeanXmss.OracleWorld _)) fun u => .pure _
    -- Both sides are `key`'s, up to the monad laws and the round trips of the translation.
    refine (congrArg₂ (Erases (worldKnown (knownKeys S0 S Pf))) ?_ ?_).mpr key
    -- `erw`: the oracle's `<$>` is the free monad's functor, the lemmas' the monad's; they agree.
    · erw [liftM_map_hash, bind_map_left]
    · erw [liftM_map_hash, bind_map_left, map_bind]
      refine Eq.trans (map_bind _ _ _) (bind_congr fun a => ?_)
      erw [map_pure]
      simp [ofEntry, toModelRequest]

/-- EthLib's game after key generation erases to the proof's. -/
theorem erases_rest (adversary : Adversary) (S0 S : LeanXmss.MasterSeed) (Pf : LeanXmss.HashOutput)
    (root : LeanXmss.Digest) :
    Erases (worldKnown (knownKeys S0 S Pf))
      (ethRest adversary ⟨ofSeed S0⟩ (ofPublicKey ⟨root, LeanXmss.truncateHash Pf⟩))
      (realRest (toModelAdversary adversary) ⟨root, LeanXmss.truncateHash Pf⟩
        ⟨S, LeanXmss.truncateHash Pf⟩) := by
  unfold ethRest realRest toModelAdversary
  simp only [simulateQ_map, WriterT.run_map', ← QueryImpl.simulateQ_compose]
  have hsim := Erases.simulateQ_writer_map (worldKnown (knownKeys S0 S Pf)) _ _ ofEntry
    (erases_oracles S0 S Pf) (adversary.main (ofPublicKey ⟨root, LeanXmss.truncateHash Pf⟩))
  refine Erases.trans (hsim.bind _ _ fun _ => Erases.refl _ _) (Erases.of_eq ?_)
  -- `erw`, as in `erases_oracles`: the `<$>` is the free monad's functor.
  erw [bind_map_left]
  refine Eq.trans ?_ (bind_map_left _ _ _).symm
  refine bind_congr fun p => ?_
  -- The verifier is the proof's, on the translated forgery.
  have hverify :
      (verifyWith H (ofPublicKey ⟨root, LeanXmss.truncateHash Pf⟩) p.1.message p.1.signature :
        OracleComp LeanXmss.HashSpec Bool)
      = LeanXmss.Concrete.verify ⟨root, LeanXmss.truncateHash Pf⟩
        (toMessage p.1.message) (toSignature p.1.signature) := by
    rw [H_eq_queryH, ← verifyWith_queryH, ofMessage_toMessage, ofSignature_toSignature]
  -- So is the winning condition.
  have hwin : decide (Valid (p.2.map ofEntry) ∧ ¬Contains (p.2.map ofEntry) p.1)
      = decide (LeanXmss.SigningTranscript.Valid p.2 ∧
          ¬LeanXmss.SigningTranscript.Contains p.2 (toModelForgery p.1)) :=
    decide_eq_decide.mpr (and_congr (valid_map _) (not_congr (contains_map _ _)))
  simp only [hverify]
  exact bind_congr fun verified => congrArg (fun b => pure (b && verified)) hwin

/-! ## The whole game

Both games sample `S_0`, query the seed hash and the parameter's hash, then go on.

After those two queries the cache holds both answers.

That is all the signer's extra calls need.

The argument is made once, for any game of that shape.

So it never unfolds the games themselves. -/

/-- After a hash query the cache holds its answer, and every entry it held before. -/
theorem romImpl_run_hash (x : HashInput) (c : QueryCache HashSpec)
    (r : HashOutput × QueryCache HashSpec) (hr : r ∈ support ((romImpl (.inr x)).run c)) :
    r.2 x = some r.1 ∧ c ≤ r.2 := by
  refine ⟨?_, romImpl_query_cache_le (.inr x) c r hr⟩
  change r ∈ support ((randomOracle (spec := HashSpec) x).run c) at hr
  cases hc : c x with
  | some v =>
    rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hr
    subst hr
    exact hc
  | none =>
    rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
    obtain ⟨u, -, rfl⟩ := hr
    exact QueryCache.cacheQuery_self _ _ _

section Prefix

variable {α : Type} (first : ProbComp α) (x1 : α → HashInput) (x2 : α → HashOutput → HashInput)

/-- A game that samples, makes two hash queries, then goes on with `rest`. -/
noncomputable def prefixGame (rest : α → HashOutput → HashOutput → OracleComp OracleWorld Bool) :
    OracleComp OracleWorld Bool :=
  (liftM first : OracleComp OracleWorld α) >>= fun a =>
    liftM (OracleWorld.query (.inr (x1 a))) >>= fun S =>
      liftM (OracleWorld.query (.inr (x2 a S))) >>= fun Pf => rest a S Pf

variable {restE restM : α → HashOutput → HashOutput → OracleComp OracleWorld Bool}
  {known : α → HashOutput → HashOutput → QueryCache HashSpec}

/-- Two such games win equally often, when the rests erase once the two answers are cached. -/
theorem evalDist_prefixGame
    (hknown : ∀ a S Pf (c1 c2 : QueryCache HashSpec), c1 (x1 a) = some S → c1 ≤ c2 →
      c2 (x2 a S) = some Pf → known a S Pf ≤ c2)
    (herases : ∀ a S Pf, Erases (worldKnown (known a S Pf)) (restE a S Pf) (restM a S Pf)) :
    (simulateQ romImpl (prefixGame first x1 x2 restE)).run' ∅ =ᵈ
      (simulateQ romImpl (prefixGame first x1 x2 restM)).run' ∅ := by
  unfold prefixGame
  rw [run'_lift_sample_bind, run'_lift_sample_bind]
  apply EvalDistEq.bind_right
  intro a
  rw [run'_query_bind, run'_query_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun r1 hr1 => ?_
  rw [run'_query_bind, run'_query_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun r2 hr2 => ?_
  obtain ⟨h1, -⟩ := romImpl_run_hash _ _ r1 hr1
  obtain ⟨h2, h12⟩ := romImpl_run_hash _ _ r2 hr2
  rw [StateT.run'_eq, StateT.run'_eq]
  exact ((herases a r1.1 r2.1).evalDist_run r2.2 (hknown a r1.1 r2.1 r1.2 r2.2 h1 h12 h2)).map _

/-- A budget after sampling, on every sample, is a budget before it. -/
theorem hashQueryBound_sample_bind_of {β : Type} (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (q : Nat)
    (h : ∀ value ∈ support first, HashQueryBound (next value) cache q) :
    HashQueryBound ((liftM first : OracleComp OracleWorld α) >>= next) cache q := by
  intro result hresult
  rw [countHashQueries_bind, countHashQueries_lift_prob, bind_map_left, run'_lift_sample_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨value, hvalue, hrun⟩ := hresult
  simp only [zero_add, Prod.mk.eta, bind_pure] at hrun
  exact h value hvalue result hrun

/-- The second game spends at most the first's budget: its rest makes no more calls. -/
theorem hashQueryBound_prefixGame
    (hknown : ∀ a S Pf (c1 c2 : QueryCache HashSpec), c1 (x1 a) = some S → c1 ≤ c2 →
      c2 (x2 a S) = some Pf → known a S Pf ≤ c2)
    (herases : ∀ a S Pf, Erases (worldKnown (known a S Pf)) (restE a S Pf) (restM a S Pf))
    (q : Nat) (h : HashQueryBound (prefixGame first x1 x2 restE) ∅ q) :
    HashQueryBound (prefixGame first x1 x2 restM) ∅ q := by
  unfold prefixGame at h ⊢
  refine hashQueryBound_sample_bind_of first _ _ _ fun a ha => ?_
  have h0 := hashQueryBound_of_sampling_bind first _ ∅ q h a ha
  obtain ⟨r1, hr1⟩ := probComp_support_nonempty ((romImpl (.inr (x1 a))).run ∅)
  refine hashQueryBound_query_bind_of _ _ _ _ (hashQueryBound_query_bind _ _ _ _ h0 r1 hr1).1
    fun r1 hr1 => ?_
  have h1 := (hashQueryBound_query_bind _ _ _ _ h0 r1 hr1).2
  obtain ⟨r2, hr2⟩ := probComp_support_nonempty ((romImpl (.inr (x2 a r1.1))).run r1.2)
  refine hashQueryBound_query_bind_of _ _ _ _ (hashQueryBound_query_bind _ _ _ _ h1 r2 hr2).1
    fun r2 hr2 => ?_
  have h2 := (hashQueryBound_query_bind _ _ _ _ h1 r2 hr2).2
  obtain ⟨hc1, -⟩ := romImpl_run_hash _ _ r1 hr1
  obtain ⟨hc2, hc12⟩ := romImpl_run_hash _ _ r2 hr2
  exact (herases a r1.1 r2.1).hashQueryBound r2.2 (hknown a r1.1 r2.1 r1.2 r2.2 hc1 hc12 hc2) _ h2

end Prefix

/-- A cache that answered both queries holds the two entries the signer repeats. -/
theorem knownKeys_le (S0 S : LeanXmss.MasterSeed) (Pf : LeanXmss.HashOutput)
    (c1 c2 : QueryCache HashSpec) (h1 : c1 (seedInput S0) = some S) (h12 : c1 ≤ c2)
    (h2 : c2 (paramInput S) = some Pf) : knownKeys S0 S Pf ≤ c2 := by
  intro t u ht
  by_cases hb : t = paramInput S
  · subst hb
    rw [knownKeys_paramInput] at ht
    cases ht
    exact h2
  · by_cases ha : t = seedInput S0
    · subst ha
      rw [knownKeys_seedInput] at ht
      cases ht
      exact h12 h1
    · simp [knownKeys, QueryCache.cacheQuery_of_ne _ _ hb, QueryCache.cacheQuery_of_ne _ _ ha] at ht

/-- The proof's key generation in the game.

It queries the seed hash and the parameter's hash, then builds the top tree. -/
theorem liftM_keygenFromSeed_bind {β : Type} (S0 : LeanXmss.MasterSeed)
    (k : LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey → OracleComp LeanXmss.OracleWorld β) :
    (liftM (LeanXmss.Seeded.keygenFromSeed S0) : OracleComp LeanXmss.OracleWorld _) >>= k
      = liftM (LeanXmss.OracleWorld.query (.inr (seedInput S0))) >>= fun S =>
          liftM (LeanXmss.OracleWorld.query (.inr (paramInput S))) >>= fun Pf =>
            (liftM (LeanXmss.Seeded.treeNode (m := OracleComp LeanXmss.HashSpec)
              (LeanXmss.truncateHash Pf) LeanXmss.topLayer S LeanXmss.layerHeight 0) :
              OracleComp LeanXmss.OracleWorld _) >>= fun root =>
              k (⟨root, LeanXmss.truncateHash Pf⟩, ⟨S, LeanXmss.truncateHash Pf⟩) := by
  unfold LeanXmss.Seeded.keygenFromSeed
  simp only [LeanXmss.Concrete.taggedSeed, LeanXmss.Concrete.th, liftM_bind, bind_assoc, liftM_pure,
    pure_bind]
  rfl

/-- EthLib's game after the two queries of key generation. -/
noncomputable def ethAfter (adversary : Adversary) (S0 S : LeanXmss.MasterSeed)
    (Pf : LeanXmss.HashOutput) : OracleComp LeanXmss.OracleWorld Bool :=
  (liftM (LeanXmss.Seeded.treeNode (m := OracleComp LeanXmss.HashSpec) (LeanXmss.truncateHash Pf)
    LeanXmss.topLayer S LeanXmss.layerHeight 0) : OracleComp LeanXmss.OracleWorld _) >>= fun root =>
      ethRest adversary ⟨ofSeed S0⟩ (ofPublicKey ⟨root, LeanXmss.truncateHash Pf⟩)

/-- The proof's game after the two queries of key generation. -/
noncomputable def modelAfter (adversary : Adversary) (S : LeanXmss.MasterSeed)
    (Pf : LeanXmss.HashOutput) : OracleComp LeanXmss.OracleWorld Bool :=
  (liftM (LeanXmss.Seeded.treeNode (m := OracleComp LeanXmss.HashSpec) (LeanXmss.truncateHash Pf)
    LeanXmss.topLayer S LeanXmss.layerHeight 0) : OracleComp LeanXmss.OracleWorld _) >>= fun root =>
      realRest (toModelAdversary adversary) ⟨root, LeanXmss.truncateHash Pf⟩
        ⟨S, LeanXmss.truncateHash Pf⟩

/-- EthLib's game, as a game of that shape. -/
theorem gameCore_eq_prefixGame (adversary : Adversary) :
    (gameCore adversary : OracleComp OracleWorld Bool)
      = prefixGame LeanXmss.sampleMasterSeed seedInput (fun _ S => paramInput S)
          (fun S0 S Pf => ethAfter adversary S0 S Pf) := by
  rw [gameCore_eq_keygen]
  refine bind_congr fun S0 => ?_
  rw [liftM_keygenFromSeed_bind]
  rfl

/-- The proof's game, as a game of that shape. -/
theorem modelGameCore_eq_prefixGame (adversary : Adversary) :
    (LeanXmss.Security.gameCore (toModelAdversary adversary) : OracleComp OracleWorld Bool)
      = prefixGame LeanXmss.sampleMasterSeed seedInput (fun _ S => paramInput S)
          (fun _ S Pf => modelAfter adversary S Pf) := by
  rw [gameCore_eq]
  refine bind_congr fun S0 => ?_
  rw [liftM_keygenFromSeed_bind]
  rfl

theorem erases_after (adversary : Adversary) (S0 S : LeanXmss.MasterSeed)
    (Pf : LeanXmss.HashOutput) :
    Erases (worldKnown (knownKeys S0 S Pf)) (ethAfter adversary S0 S Pf)
      (modelAfter adversary S Pf) :=
  (Erases.refl _ _).bind _ _ fun root => erases_rest adversary S0 S Pf root

/-! ## The theorem -/

-- The hash width again, as for `erases_oracles`.
set_option backward.isDefEq.respectTransparency false in
theorem forgeAdvantage_eq (adversary : Adversary) :
    forgeAdvantage adversary = LeanXmss.Security.forgeAdvantage (toModelAdversary adversary) := by
  have hEth : forgeAdvantage adversary =
      Pr{let x ← (simulateQ romImpl (gameCore adversary : OracleComp OracleWorld Bool)).run' ∅}[
        x = true] := by
    unfold forgeAdvantage experiment
    rw [← probOutput_countHashQueries, simulateQ_countHashQueries]
    rfl
  have hModel : LeanXmss.Security.forgeAdvantage (toModelAdversary adversary) =
      Pr{let x ← (simulateQ romImpl (LeanXmss.Security.gameCore (toModelAdversary adversary) :
        OracleComp OracleWorld Bool)).run' ∅}[x = true] := by
    unfold LeanXmss.Security.forgeAdvantage LeanXmss.Security.experiment
    rw [← probOutput_countHashQueries, simulateQ_countHashQueries]
    rfl
  rw [hEth, hModel, gameCore_eq_prefixGame, modelGameCore_eq_prefixGame]
  exact (evalDist_prefixGame _ _ _
    (fun S0 S Pf c1 c2 h1 h12 h2 => knownKeys_le S0 S Pf c1 c2 h1 h12 h2)
    fun S0 S Pf => erases_after adversary S0 S Pf).prEvent_eq _

-- The hash width again, as for `erases_oracles`.
set_option backward.isDefEq.respectTransparency false in
theorem hasHashQueryBound_toModelAdversary (adversary : Adversary) (q : Nat)
    (h : HasHashQueryBound adversary q) :
    LeanXmss.Security.HasHashQueryBound (toModelAdversary adversary) q := by
  have hEth : HashQueryBound (gameCore adversary : OracleComp OracleWorld Bool) ∅ q := by
    simp only [HashQueryBound, simulateQ_countHashQueries]
    exact h
  rw [gameCore_eq_prefixGame] at hEth
  have hModel := hashQueryBound_prefixGame _ _ _
    (fun S0 S Pf c1 c2 h1 h12 h2 => knownKeys_le S0 S Pf c1 c2 h1 h12 h2)
    (fun S0 S Pf => erases_after adversary S0 S Pf) q hEth
  have hGame : HashQueryBound (LeanXmss.Security.gameCore (toModelAdversary adversary) :
      OracleComp OracleWorld Bool) ∅ q := by
    rw [modelGameCore_eq_prefixGame]
    exact hModel
  simp only [HashQueryBound, simulateQ_countHashQueries] at hGame
  exact hGame

/-- leanXMSS as EthLib computes it has 127 bits of classical security in the random oracle model.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It forges with probability at most `q / 2^127`. -/
theorem unforgeable : HasClassicalSecurityBits 127 := fun q hq adversary hbound =>
  (forgeAdvantage_eq adversary).trans_le
    (XmssSecurity.leanXmss_has_127_bits_of_classical_security q hq _
      (hasHashQueryBound_toModelAdversary adversary q hbound))

end EthLib.Cryptography.Xmss.Unforgeability
