import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Security

/-!
# Proofs: EthLib's game wins as often as the real game

EthLib's signer gets the seed `S_0` and re-derives `S` and `P` with two hash calls.

The real game of the security proof (`XmssSecurity.Bridge.realGame`) runs EthLib's algorithms too.

Its signer, `signDerived`, keeps `S` and `P` instead.

Key generation made those two calls first, so the random oracle has their answers cached.

So the two extra calls return what the real game's signer holds.

They change nothing, and only cost budget.

```text
    EthLib :  S_0, hash S, hash P, tree, adversary, verify
                                         signer: 2 cached calls, then sign
    real   :  S_0, hash S, hash P, tree, adversary, verify
                                         signer: sign
```

Hence both games win with the same probability, and the real game spends at most EthLib's budget.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open XmssSecurity (HashSpec OracleWorld HashInput HashOutput MasterSeed seedHashInput
  truncateHash romImpl HashQueryBound hashQueryBound_of_sampling_bind hashQueryBound_query_bind
  simulateQ_countHashQueries countHashQueries_bind countHashQueries_lift_prob romImpl_query_cache_le
  probComp_support_nonempty)
open XmssSecurity.Bridge (paramInput derivedSigningOracle realRest realGame realAfterSeed
  realKeygen)
open XmssSecurity.Seeded (Erases worldKnown run'_lift_sample_bind run'_query_bind
  hashQueryBound_query_bind_of)

/-! ## The two calls the signer repeats -/

/-- The game's `H` is `queryH`, at the hash oracle. -/
theorem H_eq_queryH : H = queryH (m := OracleComp HashSpec) :=
  rfl

/-- `S = H("leanXMSS" | S_0)`, one query of the seed hash's input. -/
theorem schemeSeed_queryH (S0 : MasterSeed) :
    (schemeSeed queryH (ofSeed S0) : OracleComp HashSpec Seed)
      = liftM (HashSpec.query (seedHashInput S0)) >>= fun y => pure (ofSeed y) := by
  have hinput : (ByteArray.mk SEED_TAG.toArray ++ packBytes (ofSeed S0)).data.toList
      = seedHashInput S0 := by
    simp only [toList_data_append, toList_data_packBytes, toList_ofSeed]
    rfl
  unfold schemeSeed queryH
  rw [hinput, map_eq_bind_pure_comp]
  rfl

/-- `P = Th(0^128, A_param, S)`, one query of the parameter's input. -/
theorem publicParamOf_queryH (S : MasterSeed) :
    (publicParamOf queryH (ofSeed S) : OracleComp HashSpec PublicParam)
      = liftM (HashSpec.query (paramInput S)) >>= fun y => pure (ofParam (truncateHash y)) := by
  -- The all-zero parameter is the bytes of the zero bit vector.
  have hzero : Vector.replicate PUBLIC_PARAM_LEN (0 : UInt8)
      = ofParam (0 : XmssSecurity.PublicParameter) := by
    rw [ofParam, ofBV_eq_littleEndian]
    apply Vector.ext
    intro i hi
    simp [littleEndian]
  have hinput : (thInput (ofParam (0 : XmssSecurity.PublicParameter)) addrParam
      (packBytes (ofSeed S))).data.toList = paramInput S := by
    rw [XmssSecurity.Bridge.paramInput_eq]
    simp only [thInput, toList_data_append, toList_data_packBytes, toList_ofParam, toList_ofSeed,
      toList_addrParam]
    rfl
  unfold publicParamOf th queryH
  rw [hzero, hinput]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun y => ?_
  rw [halfOf_zero_ofOutput]
  rfl

/-- The oracle's answers to the two calls of key generation that the signer repeats. -/
def knownKeys (S0 : MasterSeed) (S Pf : HashOutput) : QueryCache HashSpec :=
  ((∅ : QueryCache HashSpec).cacheQuery (seedHashInput S0) S).cacheQuery (paramInput S) Pf

/-- The seed hash's input, 40 bytes, is not the parameter's, 64 bytes. -/
theorem seedHashInput_ne_paramInput (S0 : MasterSeed) (S : HashOutput) :
    seedHashInput S0 ≠ paramInput S := by
  intro h
  have := congrArg List.length h
  have hS : (XmssSecurity.bytesLE 32 S).length = 32 := XmssSecurity.length_bytesLE 32 S
  simp [seedHashInput, XmssSecurity.Bridge.paramInput, XmssSecurity.keygenHashInput,
    XmssSecurity.fieldBytes, XmssSecurity.length_bytesLE, hS] at this

theorem knownKeys_seedInput (S0 : MasterSeed) (S Pf : HashOutput) :
    knownKeys S0 S Pf (seedHashInput S0) = some S := by
  rw [knownKeys, QueryCache.cacheQuery_of_ne _ _ (seedHashInput_ne_paramInput S0 S),
    QueryCache.cacheQuery_self]

theorem knownKeys_paramInput (S0 : MasterSeed) (S Pf : HashOutput) :
    knownKeys S0 S Pf (paramInput S) = some Pf := by
  rw [knownKeys, QueryCache.cacheQuery_self]

-- `S` is a hash value, `BitVec hashOutputBits`, and a seed is `BitVec 256`.
-- As in the vendored proof, definitional checks may unfold the width to match them.
set_option backward.isDefEq.respectTransparency false in
/-- EthLib's signer erases to the real game's: the cache answers its calls for `S` and `P`. -/
theorem erases_signWith (S0 : MasterSeed) (S Pf : HashOutput) (idx : LeafIndex) (msg : Message) :
    Erases (knownKeys S0 S Pf) (Except.toOption <$> signWith queryH ⟨ofSeed S0⟩ idx msg)
      (Except.toOption <$> signDerived queryH (ofSeed S) (ofParam (truncateHash Pf)) idx msg) := by
  unfold signWith
  rw [schemeSeed_queryH]
  simp only [bind_assoc, pure_bind, map_bind]
  -- The seed hash is cached: skip it.
  refine Erases.skip (seedHashInput S0) S (knownKeys_seedInput S0 S Pf) _ _ ?_
  -- The parameter's hash is cached: skip it.
  rw [publicParamOf_queryH]
  simp only [bind_assoc, pure_bind]
  refine Erases.skip (paramInput S) Pf (knownKeys_paramInput S0 S Pf) _ _ ?_
  exact Erases.refl _ _

/-! ## The adversary's run -/

/-- EthLib's game once the keys exist: the adversary with its oracles, then the verification. -/
noncomputable def ethRest (adversary : Adversary) (sk : SecretKey) (pk : PublicKey) :
    OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return decide (Valid log ∧ ¬Contains log forgery) && verified

/-- Each oracle of EthLib's adversary erases to the real game's. -/
theorem erases_oracles (S0 : MasterSeed) (S Pf : HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) :
    Erases (worldKnown (knownKeys S0 S Pf))
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        signingOracle ⟨ofSeed S0⟩) input).run
      ((fun p => (p.1, p.2.map id)) <$>
        ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          derivedSigningOracle (ofSeed S) (ofParam (truncateHash Pf))) input).run) := by
  -- The logs are the same, so the translation is the identity.
  simp only [List.map_id, Prod.mk.eta, id_map']
  cases input with
  | inl input =>
    simp only [QueryImpl.add_apply_inl]
    exact .refl _ _
  | inr request =>
    simp only [QueryImpl.add_apply_inr, signingOracle, derivedSigningOracle,
      QueryImpl.run_withLogging_apply]
    exact (erases_signWith S0 S Pf request.leafIndex request.message).lift_hash.bind _ _
      fun _ => .pure _

/-- EthLib's game after key generation erases to the real game's. -/
theorem erases_rest (adversary : Adversary) (S0 : MasterSeed) (S Pf : HashOutput)
    (root : Digest) :
    Erases (worldKnown (knownKeys S0 S Pf))
      (ethRest adversary ⟨ofSeed S0⟩ ⟨root, ofParam (truncateHash Pf)⟩)
      (realRest adversary ⟨root, ofParam (truncateHash Pf)⟩ S) := by
  unfold ethRest realRest
  have hsim := XmssSecurity.Bridge.Erases.simulateQ_writer_map (worldKnown (knownKeys S0 S Pf))
    _ _ id (erases_oracles S0 S Pf) (adversary.main ⟨root, ofParam (truncateHash Pf)⟩)
  simp only [List.map_id, Prod.mk.eta, id_map'] at hsim
  exact hsim.bind _ _ fun _ => .refl _ _

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
  rw [countHashQueries_bind, countHashQueries_lift_prob,
    bind_map_left, run'_lift_sample_bind, mem_support_bind_iff] at hresult
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
theorem knownKeys_le (S0 : MasterSeed) (S Pf : HashOutput) (c1 c2 : QueryCache HashSpec)
    (h1 : c1 (seedHashInput S0) = some S) (h12 : c1 ≤ c2) (h2 : c2 (paramInput S) = some Pf) :
    knownKeys S0 S Pf ≤ c2 := by
  intro t u ht
  by_cases hb : t = paramInput S
  · subst hb
    rw [knownKeys_paramInput] at ht
    cases ht
    exact h2
  · by_cases ha : t = seedHashInput S0
    · subst ha
      rw [knownKeys_seedInput] at ht
      cases ht
      exact h12 h1
    · simp [knownKeys, QueryCache.cacheQuery_of_ne _ _ hb, QueryCache.cacheQuery_of_ne _ _ ha] at ht

/-- The top tree's root, from `S` and the parameter. -/
noncomputable def topRoot (S Pf : HashOutput) : OracleComp OracleWorld Digest :=
  liftM (node (queryH (m := OracleComp HashSpec)) (ofParam (truncateHash Pf)) (ofSeed S) .top
    LAYER_HEIGHT (Nat.le_refl _) 0)

-- `S` is a hash value, `BitVec hashOutputBits`, and a seed is `BitVec 256`.
-- As in the vendored proof, definitional checks may unfold the width to match them.
set_option backward.isDefEq.respectTransparency false in
/-- EthLib's key generation in the game: the seed hash, the parameter's hash, then the top tree. -/
theorem liftM_keyGenWith_bind {β : Type} (S0 : MasterSeed)
    (k : SecretKey × PublicKey → OracleComp OracleWorld β) :
    (liftM (keyGenWith H (ofSeed S0)) : OracleComp OracleWorld _) >>= k
      = liftM (OracleWorld.query (.inr (seedHashInput S0))) >>= fun S =>
          liftM (OracleWorld.query (.inr (paramInput S))) >>= fun Pf =>
            topRoot S Pf >>= fun root => k (⟨ofSeed S0⟩, ⟨root, ofParam (truncateHash Pf)⟩) := by
  unfold keyGenWith publicKeyOf topRoot
  rw [H_eq_queryH, schemeSeed_queryH]
  simp only [publicParamOf_queryH, liftM_bind, bind_assoc, liftM_pure, pure_bind]
  rfl

-- `S` is a hash value, `BitVec hashOutputBits`, and a seed is `BitVec 256`.
-- As in the vendored proof, definitional checks may unfold the width to match them.
set_option backward.isDefEq.respectTransparency false in
/-- EthLib's key generation from `S`, as the real game runs it. -/
theorem liftM_realKeygen_bind {β : Type} (S : HashOutput)
    (k : PublicKey → OracleComp OracleWorld β) :
    (liftM (realKeygen S) : OracleComp OracleWorld _) >>= k
      = liftM (OracleWorld.query (.inr (paramInput S))) >>= fun Pf =>
          topRoot S Pf >>= fun root => k ⟨root, ofParam (truncateHash Pf)⟩ := by
  unfold realKeygen publicKeyOf topRoot
  simp only [publicParamOf_queryH, liftM_bind, bind_assoc, liftM_pure, pure_bind]
  rfl

-- `S` is a hash value, `BitVec hashOutputBits`, and a seed is `BitVec 256`.
-- As in the vendored proof, definitional checks may unfold the width to match them.
set_option backward.isDefEq.respectTransparency false in
/-- EthLib's game, as a game of that shape. -/
theorem gameCore_eq_prefixGame (adversary : Adversary) :
    gameCore adversary
      = prefixGame XmssSecurity.sampleMasterSeed seedHashInput (fun _ S => paramInput S)
          (fun S0 S Pf => topRoot S Pf >>= fun root =>
            ethRest adversary ⟨ofSeed S0⟩ ⟨root, ofParam (truncateHash Pf)⟩) := by
  unfold gameCore sampleSeed
  rw [liftM_map, bind_map_left]
  refine bind_congr fun S0 => ?_
  rw [liftM_keyGenWith_bind]
  rfl

-- `S` is a hash value, `BitVec hashOutputBits`, and a seed is `BitVec 256`.
-- As in the vendored proof, definitional checks may unfold the width to match them.
set_option backward.isDefEq.respectTransparency false in
/-- The real game, as a game of that shape. -/
theorem realGame_eq_prefixGame (adversary : Adversary) :
    realGame adversary
      = prefixGame XmssSecurity.sampleMasterSeed seedHashInput (fun _ S => paramInput S)
          (fun _ S Pf => topRoot S Pf >>= fun root =>
            realRest adversary ⟨root, ofParam (truncateHash Pf)⟩ S) := by
  unfold realGame prefixGame realAfterSeed
  refine bind_congr fun S0 => bind_congr fun S => ?_
  rw [liftM_realKeygen_bind]

-- `S` is a hash value, `BitVec hashOutputBits`, and a seed is `BitVec 256`.
-- As in the vendored proof, definitional checks may unfold the width to match them.
set_option backward.isDefEq.respectTransparency false in
theorem erases_after (adversary : Adversary) (S0 : MasterSeed) (S Pf : HashOutput) :
    Erases (worldKnown (knownKeys S0 S Pf))
      (topRoot S Pf >>= fun root =>
        ethRest adversary ⟨ofSeed S0⟩ ⟨root, ofParam (truncateHash Pf)⟩)
      (topRoot S Pf >>= fun root => realRest adversary ⟨root, ofParam (truncateHash Pf)⟩ S) :=
  (Erases.refl _ _).bind _ _ fun root => erases_rest adversary S0 S Pf root

/-! ## The theorem -/

theorem forgeAdvantage_eq (adversary : Adversary) :
    forgeAdvantage adversary
      = Pr{let x ← (simulateQ romImpl (realGame adversary)).run' ∅}[x = true] := by
  have hEth : forgeAdvantage adversary =
      Pr{let x ← (simulateQ romImpl (gameCore adversary)).run' ∅}[x = true] := by
    unfold forgeAdvantage experiment
    rw [← XmssSecurity.Bridge.probOutput_countHashQueries,
      simulateQ_countHashQueries]
    rfl
  rw [hEth, gameCore_eq_prefixGame, realGame_eq_prefixGame]
  exact (evalDist_prefixGame _ _ _
    (fun S0 S Pf c1 c2 h1 h12 h2 => knownKeys_le S0 S Pf c1 c2 h1 h12 h2)
    fun S0 S Pf => erases_after adversary S0 S Pf).prEvent_eq _

theorem hashQueryBound_realGame (adversary : Adversary) (q : Nat)
    (h : HasHashQueryBound adversary q) : HashQueryBound (realGame adversary) ∅ q := by
  have hEth : HashQueryBound (gameCore adversary) ∅ q := by
    simp only [HashQueryBound, simulateQ_countHashQueries]
    exact h
  rw [gameCore_eq_prefixGame] at hEth
  rw [realGame_eq_prefixGame]
  exact hashQueryBound_prefixGame _ _ _
    (fun S0 S Pf c1 c2 h1 h12 h2 => knownKeys_le S0 S Pf c1 c2 h1 h12 h2)
    (fun S0 S Pf => erases_after adversary S0 S Pf) q hEth

/-- leanXMSS as EthLib computes it has 127 bits of classical security in the random oracle model.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It forges with probability at most `q / 2^127`. -/
theorem unforgeable : HasClassicalSecurityBits 127 := fun q hq adversary hbound =>
  (forgeAdvantage_eq adversary).trans_le
    (XmssSecurity.Bridge.realGame_security q hq adversary
      (hashQueryBound_realGame adversary q hbound))

end EthLib.Cryptography.Xmss.Unforgeability
