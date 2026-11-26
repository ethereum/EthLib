module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Reasons
public import EthLib.Cryptography.Proofs.Xmss.MapMonad
public import EthLib.Cryptography.Proofs.Xmss.Cost
public import EthLib.Cryptography.Proofs.DerivationTable
public import EthLib.Cryptography.Proofs.ChargeBound

/-!
# Proofs: the signer's secrets as derivations, in two hidden-seed hops

The game where some signing request fails derives every secret from `S_0`, through two hashes.

- The scheme seed is `S = H("leanXMSS" | S_0)`.
- Every other secret is a derivation `H(P | A | S | suffix)` from `S`.

Two hidden-seed hops replace these hashes by queries of their own, derivation queries.

1. `S` becomes a derivation query, which key generation reads.
   In the ideal game it is drawn once, uniform, and `S_0` appears nowhere.
2. Every derivation from `S` becomes a derivation query.
   In the ideal game each is drawn from a lazy table on its first use, and `S` appears nowhere.

A hash input fixes the seed it encodes, since the prefixes before the seed have fixed lengths.

So each hop costs at most `q / 2^256`, for a game of at most `q` hash queries.

The event is that some signing request fails, and a hop bounds any event of the game's output.

The game is written once, over a handler of hash queries and a source of derivations.

Its signer keeps its key across requests, and takes its secrets from the derivations.

The real game and the two games with derivation queries are three instances.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants (LAYER_HEIGHT)
open XmssSecurity (OracleWorld HashSpec HashOutput MasterSeed romImpl seedHashInput)

/-- What the game returns: the forgery, the log of the signing requests, and the verification. -/
abbrev FailOutput := Forgery × QueryLog SigningSpec × Bool

/-- Some signing request of the game failed. -/
def SomeFailure (z : FailOutput) : Prop :=
  ∃ entry ∈ z.2.1, entry.2 = none

/-! ## Signing does not read the key's scheme seed -/

section KeySeed

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : Array UInt64 → m Lanes4)
  (prf : SeedPrf m) (trials : TrialSource m)

/-- Fetching a tree with other derivations, a key with another scheme seed gives the same tree.

The updated key keeps that other scheme seed. -/
theorem fetchTreeWith_withSeed (sk : SecretKey) (s : Seed) (b : Nat) :
    Internal.fetchTreeWith H prf { sk with schemeSeed := s } b trials =
      (fun r => (r.1, { r.2 with schemeSeed := s })) <$>
        Internal.fetchTreeWith H prf sk b trials := by
  unfold Internal.fetchTreeWith
  dsimp only
  cases sk.cache.find? (·.index == b) with
  | some t => rw [map_pure]
  | none =>
    rw [map_bind]
    refine bind_congr fun t => ?_
    rw [map_pure]

/-- **Signing with given derivations reads no scheme seed of the key.**

The updated key keeps the scheme seed it had. -/
theorem signWithTrials_withSeed (sk : SecretKey) (s : Seed) (idx : LeafIndex) (msg : Message) :
    Internal.signWithTrials H prf { sk with schemeSeed := s } idx msg trials =
      (fun r => (r.1, { r.2 with schemeSeed := s })) <$>
        Internal.signWithTrials H prf sk idx msg trials := by
  unfold Internal.signWithTrials
  rw [map_bind]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨rho, y⟩
  · rw [map_pure]
  · dsimp only
    rw [fetchTreeWith_withSeed, bind_map_left, map_bind]
    refine bind_congr fun r => ?_
    obtain ⟨t, sk'⟩ := r
    dsimp only
    cases t.top <;> simp only [map_pure]

end KeySeed

/-! ## The game over a source of derivations -/

section Source

variable {ι : Type} {spec : OracleSpec ι}

/-- The hash of a game whose hash and coin queries a handler answers. -/
def hashOf (pass : QueryImpl OracleWorld (OracleComp spec)) (x : Array UInt64) :
    OracleComp spec Lanes4 :=
  ofOutput <$> pass (.inr (Hash.Keccak.lanesBytes x))

/-- The game's oracles: hash and coin queries go to `pass`, and a request signs with the kept key.

The signer takes its secrets from the given derivations. -/
def failSignerOf (pass : QueryImpl OracleWorld (OracleComp spec))
    (prf : SeedPrf (OracleComp spec)) :
    QueryImpl (OracleWorld + ReasonSigningSpec)
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp spec)))
  | .inl t => StateT.mk fun sk => WriterT.mk ((fun u => ((u, sk), [])) <$> pass t)
  | .inr request => StateT.mk fun sk => WriterT.mk ((fun result =>
      ((result.1, result.2), [⟨request, result.1.toOption⟩])) <$>
        Internal.signWithTrials (hashOf pass) prf sk request.leafIndex request.message
          (hashTrials (hashOf pass)))

/-- The game of a signing failure: keys, the adversary, then the verification.

The scheme seed comes from a source, and the secrets from the derivations of that seed. -/
def failGameOf (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec Seed) (prfOf : Seed → SeedPrf (OracleComp spec))
    (adversary : ReasonAdversary) : OracleComp spec FailOutput := do
  let s ← seedSrc
  let keys ← Internal.keyGenFrom (hashOf pass) (prfOf s) s
  let (((forgery, _), log) : (Forgery × SecretKey) × QueryLog SigningSpec) ←
    ((simulateQ (failSignerOf pass (prfOf s)) (adversary.main keys.1)).run keys.2).run
  let verified ← verifyWith (hashOf pass) keys.1 forgery.message forgery.signature
  return (forgery, log, verified)

/-- The signer's run from a key with another scheme seed: the same run, keeping that seed. -/
theorem run_failSignerOf_withSeed (pass : QueryImpl OracleWorld (OracleComp spec))
    (prf : SeedPrf (OracleComp spec)) {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) (sk : SecretKey) (s : Seed) :
    ((simulateQ (failSignerOf pass prf) oa).run { sk with schemeSeed := s }).run =
      (fun p => ((p.1.1, { p.1.2 with schemeSeed := s }), p.2)) <$>
        ((simulateQ (failSignerOf pass prf) oa).run sk).run := by
  induction oa using OracleComp.inductionOn generalizing sk with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind', map_bind]
    rcases t with t | request
    · change ((failSignerOf pass prf (.inl t)).run _).run >>= _ =
        ((failSignerOf pass prf (.inl t)).run sk).run >>= _
      simp only [failSignerOf, StateT.run_mk, WriterT.run_mk, bind_map_left]
      refine bind_congr fun u => ?_
      rw [ih, Functor.map_map, Functor.map_map]
      rfl
    · change ((failSignerOf pass prf (.inr request)).run _).run >>= _ =
        ((failSignerOf pass prf (.inr request)).run sk).run >>= _
      simp only [failSignerOf, StateT.run_mk, WriterT.run_mk, bind_map_left,
        signWithTrials_withSeed]
      refine bind_congr fun r => ?_
      rw [ih, Functor.map_map, Functor.map_map]
      rfl

/-- The game reads the scheme seed it keeps in the key nowhere but there.

So two games that differ only in that seed, with the same derivations, are the same game. -/
theorem failGameOf_pure_seed (pass : QueryImpl OracleWorld (OracleComp spec)) (s s' : Seed)
    (prf : SeedPrf (OracleComp spec)) (adversary : ReasonAdversary) :
    failGameOf pass (pure s) (fun _ => prf) adversary =
      failGameOf pass (pure s') (fun _ => prf) adversary := by
  simp only [failGameOf, Internal.keyGenFrom, pure_bind, bind_assoc]
  refine bind_congr fun publicParam => bind_congr fun top => ?_
  have h := run_failSignerOf_withSeed pass prf
    (adversary.main { root := top.value, publicParam := publicParam })
    { schemeSeed := s, publicParam := publicParam, top, cache := [] } s'
  simp only at h
  rw [h, bind_map_left]

section Map

variable {ι' : Type} {spec' : OracleSpec ι'} (so : QueryImpl spec (OracleComp spec'))

/-- Simulating a hash call gives the hash of the simulated handler. -/
theorem simulateQ_hashOf (pass : QueryImpl OracleWorld (OracleComp spec)) (x : Array UInt64) :
    simulateQ so (hashOf pass x) = hashOf (so ∘ₛ pass) x := by
  simp [hashOf, QueryImpl.apply_compose]

/-- Simulating a query of the game's oracles gives the query over the simulated sources. -/
theorem simulateQ_run_failSignerOf_apply (pass : QueryImpl OracleWorld (OracleComp spec))
    (prf : SeedPrf (OracleComp spec)) (t : (OracleWorld + ReasonSigningSpec).Domain)
    (sk : SecretKey) :
    simulateQ so ((failSignerOf pass prf t).run sk).run =
      ((failSignerOf (so ∘ₛ pass) (fun publicParam a suffix => simulateQ so
        (prf publicParam a suffix)) t).run
        sk).run := by
  rcases t with t | request
  · simp [failSignerOf, QueryImpl.apply_compose]
  · simp only [failSignerOf, StateT.run_mk, WriterT.run_mk, simulateQ_map]
    rw [signWithTrials_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
      (fun x f => simulateQ_bind so x f)]
    simp only [simulateQ_hashOf]

/-- Simulating the run of the game's oracles gives their run over the simulated sources. -/
theorem simulateQ_run_failSignerOf (pass : QueryImpl OracleWorld (OracleComp spec))
    (prf : SeedPrf (OracleComp spec)) {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) (sk : SecretKey) :
    simulateQ so ((simulateQ (failSignerOf pass prf) oa).run sk).run =
      ((simulateQ (failSignerOf (so ∘ₛ pass) (fun publicParam a suffix => simulateQ so
        (prf publicParam a suffix)))
        oa).run sk).run := by
  induction oa using OracleComp.inductionOn generalizing sk with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
      simulateQ_map, simulateQ_run_failSignerOf_apply, ih]

/-- Simulating key generation from a seed gives it over the simulated sources. -/
theorem simulateQ_keyGenFrom (pass : QueryImpl OracleWorld (OracleComp spec)) (s : Seed)
    (prf : SeedPrf (OracleComp spec)) :
    simulateQ so (Internal.keyGenFrom (hashOf pass) prf s) =
      Internal.keyGenFrom (hashOf (so ∘ₛ pass)) (fun publicParam a suffix => simulateQ so
        (prf publicParam a suffix))
        s := by
  simp only [Internal.keyGenFrom, simulateQ_bind, simulateQ_pure]
  rw [publicParamOf_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
    (fun x f => simulateQ_bind so x f)]
  refine bind_congr fun publicParam => ?_
  rw [build_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
    (fun x f => simulateQ_bind so x f)]
  simp only [simulateQ_hashOf]

end Map

/-- Simulating the queries of the game gives the game over the simulated handler and source. -/
theorem simulateQ_failGameOf {ι' : Type} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec')) (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec Seed) (prfOf : Seed → SeedPrf (OracleComp spec))
    (adversary : ReasonAdversary) :
    simulateQ so (failGameOf pass seedSrc prfOf adversary) =
      failGameOf (so ∘ₛ pass) (simulateQ so seedSrc)
        (fun s publicParam a suffix => simulateQ so (prfOf s publicParam a suffix)) adversary := by
  simp only [failGameOf, simulateQ_bind, simulateQ_pure, simulateQ_keyGenFrom,
    simulateQ_run_failSignerOf]
  refine bind_congr fun s => bind_congr fun keys => bind_congr fun z => ?_
  rw [verifyWith_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
    (fun x f => simulateQ_bind so x f)]
  simp only [simulateQ_hashOf]

end Source

/-! ## The real game -/

/-- The game's `H`, lifted to hash and coin queries, is the hash of the identity handler. -/
theorem liftM_H (x : Array UInt64) :
    (liftM (H x) : OracleComp OracleWorld Lanes4) =
      hashOf (QueryImpl.id' OracleWorld) x := by
  simp [H, queryH, HashSig.queryLanes, hashOf, HashSig.oracleHash]
  rfl

/-- The derivations of the game, lifted, are those over the hash of the identity handler. -/
theorem liftM_seedPrf (s : Seed) :
    (fun publicParam a suffix =>
        (liftM (seedPrf H s publicParam a suffix) : OracleComp OracleWorld Lanes4)) =
      seedPrf (hashOf (QueryImpl.id' OracleWorld)) s := by
  funext publicParam a suffix
  exact liftM_H _

/-- Signing, lifted, is signing over the hash of the identity handler, from the key's seed. -/
theorem liftM_signWith (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    (liftM (signWith H sk idx msg) : OracleComp OracleWorld _) =
      Internal.signWithTrials (hashOf (QueryImpl.id' OracleWorld))
        (seedPrf (hashOf (QueryImpl.id' OracleWorld)) sk.schemeSeed) sk idx msg
        (hashTrials (hashOf (QueryImpl.id' OracleWorld))) := by
  unfold signWith
  rw [signWithTrials_map_monad (fun {β} (c : OracleComp HashSpec β) =>
    (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
    liftM_seedPrf, funext liftM_H]

/-- The real game's oracles, from a key of scheme seed `s`, are the game's over its derivations. -/
theorem run_reasonOracles_eq (s : Seed) {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) (sk : SecretKey)
    (hs : sk.schemeSeed = s) :
    ((simulateQ (QueryImpl.ofLift OracleWorld
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) +
        reasonSigningOracle) oa).run sk).run =
      ((simulateQ (failSignerOf (QueryImpl.id' OracleWorld)
        (seedPrf (hashOf (QueryImpl.id' OracleWorld)) s)) oa).run sk).run := by
  induction oa using OracleComp.inductionOn generalizing sk with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind']
    rcases t with t | request
    · rw [QueryImpl.add_apply_inl]
      have hl : ((QueryImpl.ofLift OracleWorld (StateT SecretKey
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) t).run sk).run =
          (fun u => ((u, sk), ([] : QueryLog SigningSpec))) <$>
            (liftM (OracleWorld.query t) : OracleComp OracleWorld _) := by
        simp only [QueryImpl.ofLift_apply]
        rfl
      rw [hl]
      simp only [failSignerOf, StateT.run_mk, WriterT.run_mk, bind_map_left]
      refine bind_congr fun u => ?_
      rw [ih u sk hs]
    · change ((reasonSigningOracle request).run sk).run >>= _ =
        ((failSignerOf (QueryImpl.id' OracleWorld)
          (seedPrf (hashOf (QueryImpl.id' OracleWorld)) s) (.inr request)).run sk).run >>= _
      -- Signing keeps the key's seed `s`, so the run goes on from a key of seed `s`.
      have hkeep := signWithTrials_withSeed (hashOf (QueryImpl.id' OracleWorld))
        (seedPrf (hashOf (QueryImpl.id' OracleWorld)) s)
        (hashTrials (hashOf (QueryImpl.id' OracleWorld))) sk s request.leafIndex request.message
      have hsk : { sk with schemeSeed := s } = sk := by
        rw [← hs]
      rw [hsk] at hkeep
      simp only [reasonSigningOracle, failSignerOf, StateT.run_mk, WriterT.run_mk, liftM_signWith,
        hs]
      rw [hkeep]
      simp only [Functor.map_map]
      erw [bind_map_left, bind_map_left]
      refine bind_congr fun r => ?_
      rw [ih _ _ rfl]

/-- Key generation, lifted, is key generation over the identity handler, from the seed hash. -/
theorem liftM_keyGenWith (seed : Seed) :
    (liftM (keyGenWith H seed) : OracleComp OracleWorld _) =
      schemeSeed (hashOf (QueryImpl.id' OracleWorld)) seed >>= fun s =>
        Internal.keyGenFrom (hashOf (QueryImpl.id' OracleWorld))
          (seedPrf (hashOf (QueryImpl.id' OracleWorld)) s) s := by
  have hseed : (liftM (schemeSeed H seed) : OracleComp OracleWorld Seed) =
      schemeSeed (hashOf (QueryImpl.id' OracleWorld)) seed :=
    liftM_H _
  unfold keyGenWith Internal.keyGenFrom
  simp only [liftM_bind, liftM_pure, hseed]
  refine bind_congr fun s => ?_
  rw [publicParamOf_map_monad (fun {β} (c : OracleComp HashSpec β) =>
    (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
    liftM_seedPrf]
  refine bind_congr fun publicParam => ?_
  rw [build_map_monad (fun {β} (c : OracleComp HashSpec β) =>
    (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
    liftM_seedPrf, funext liftM_H]

/-- The game of a signing failure, before the random oracle, as the game over the seed `S_0`. -/
theorem reasonRun_eq_failGameOf (adversary : ReasonAdversary) :
    reasonRun adversary =
      (liftM XmssSecurity.sampleMasterSeed : OracleComp OracleWorld _) >>=
      fun s0 => failGameOf (QueryImpl.id' OracleWorld)
        (schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0))
        (seedPrf (hashOf (QueryImpl.id' OracleWorld))) adversary := by
  unfold reasonRun sampleSeed
  simp only [liftM_map, bind_map_left]
  refine bind_congr fun s0 => ?_
  simp only [failGameOf, liftM_keyGenWith, bind_assoc]
  refine bind_congr fun s => ?_
  simp only [Internal.keyGenFrom, bind_assoc, pure_bind]
  refine bind_congr fun publicParam => bind_congr fun top => ?_
  rw [run_reasonOracles_eq s _ _ rfl]
  refine bind_congr fun p => ?_
  rcases p with ⟨⟨forgery, sk'⟩, log⟩
  dsimp only
  rw [verifyWith_map_monad (fun {β} (c : OracleComp HashSpec β) =>
    (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
    funext liftM_H]

/-- The real game draws `S_0`, and key generation hashes it into `S`. -/
theorem signingFailure_eq (adversary : ReasonAdversary) :
    signingFailure adversary =
      Pr{let s0 ← XmssSecurity.sampleMasterSeed
         let z ← (simulateQ romImpl (failGameOf (QueryImpl.id' OracleWorld)
           (schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0))
           (seedPrf (hashOf (QueryImpl.id' OracleWorld))) adversary)).run' ∅}[SomeFailure z] := by
  refine (SufCma.prEvent_countedRunIn _ (reasonRun adversary) SomeFailure).trans ?_
  rw [run_randomOracleModel, reasonRun_eq_failGameOf, XmssSecurity.Seeded.run'_lift_sample_bind]
  simp only [prEvent_norm]

/-! ## The first hop: the scheme seed -/

/-- The oracles of a game whose scheme seed is a derivation query. -/
abbrev SeedSpec := HashSpec.withDerivations Unit HashOutput

/-- The game with the scheme seed `S` as a derivation query, which key generation reads. -/
def seedGame (adversary : ReasonAdversary) : OracleComp SeedSpec FailOutput :=
  failGameOf (HashSpec.withDerivationsLift Unit HashOutput)
    (ofOutput <$> SeedSpec.query (.inr ()))
    (seedPrf (hashOf (HashSpec.withDerivationsLift Unit HashOutput))) adversary

/-- `S` is the hash at `"leanXMSS" | S_0`. -/
def seedEncoding : SecretEncoding HashSpec MasterSeed Unit HashOutput where
  enc s0 _ := seedHashInput s0
  range_eq _ _ := rfl
  injective _ _ _ _ := rfl

/-- A hash query of a game with derivation queries. -/
def IsHashD {X : Type} : (HashSpec.withDerivations X HashOutput).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance {X : Type} : DecidablePred (IsHashD (X := X)) := fun t => by
  rcases t with (_ | _) | _ <;> simp only [IsHashD] <;> infer_instance

/-- The input of `S` fixes `S_0`. -/
theorem seedHashInput_inj {s0 s0' : MasterSeed} (h : seedHashInput s0 = seedHashInput s0') :
    s0 = s0' :=
  XmssSecurity.bytesLE_injective 32 (List.append_cancel_left h)

/-- There are `2^256` seeds `S_0`. -/
theorem natCard_masterSeed : Nat.card MasterSeed = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_bitVec]

/-- A given input is the input of `S` for a uniform `S_0` with probability at most `2^-256`. -/
theorem prEvent_mem_range_seedEncoding_le (t : HashSig.HashInput) :
    Pr{let s0 ← XmssSecurity.sampleMasterSeed}[t ∈ Set.range (seedEncoding.enc s0)] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let := SampleableType.ofFintype MasterSeed
  have h := prEvent_mem_range_enc_le seedEncoding
    (fun _ _ _ _ h => seedHashInput_inj h) t
  rw [natCard_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- Answering the scheme seed at its input gives the real game. -/
theorem simulateQ_deriveImpl_seedGame (s0 : MasterSeed) (adversary : ReasonAdversary) :
    simulateQ (seedEncoding.deriveImpl s0) (seedGame adversary) =
      failGameOf (QueryImpl.id' OracleWorld)
        (schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0))
        (seedPrf (hashOf (QueryImpl.id' OracleWorld))) adversary := by
  -- The name's lane is its 8 bytes, and the seed's lanes are its 32 bytes.
  have hinput : Hash.Keccak.lanesBytes (#[Constants.SEED_TAG_LANE] ++ (ofSeed s0).toArray)
      = seedHashInput s0 := by
    rw [Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_singleton, bytesOfLane_seedTagLane,
      toList_ofSeed]
    rfl
  have hsrc : simulateQ (seedEncoding.deriveImpl s0)
      (ofOutput <$> SeedSpec.query (.inr ())) =
        schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0) := by
    rw [simulateQ_map, simulateQ_spec_query]
    unfold schemeSeed hashOf
    rw [hinput]
    rfl
  have hprf : (fun (s : Seed) publicParam a suffix => simulateQ (seedEncoding.deriveImpl s0)
      (seedPrf (hashOf (HashSpec.withDerivationsLift Unit HashOutput)) s publicParam a suffix)) =
        seedPrf (hashOf (QueryImpl.id' OracleWorld)) := by
    funext s publicParam a suffix
    simp only [seedPrf, simulateQ_hashOf, SecretEncoding.deriveImpl_comp_withDerivationsLift]
  unfold seedGame
  erw [simulateQ_failGameOf, SecretEncoding.deriveImpl_comp_withDerivationsLift, hsrc, hprf]

/-- **The first hop.**

Some request fails at most as often as in the ideal game of the scheme seed, plus `q / 2^256`.

The game with the scheme seed as a derivation query makes at most `q` hash queries. -/
theorem signingFailure_le_seedGame (adversary : ReasonAdversary) {q : ℕ}
    (hq : IsQueryBoundP (seedGame adversary) IsHashD q) :
    signingFailure adversary ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec Unit HashOutput)
          (seedGame adversary)).run (∅, ∅)}[SomeFailure z.1] +
        q * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hop := prEvent_romImpl_deriveImpl_le seedEncoding (ms := XmssSecurity.sampleMasterSeed)
    prEvent_mem_range_seedEncoding_le (p := IsHashD) (fun _ _ => trivial) hq
    fun _ z => SomeFailure z
  rw [OracleComp.prEvent_bind_const] at hop
  refine le_of_eq_of_le ?_ hop
  rw [signingFailure_eq]
  have hrom : XmssSecurity.romImpl = HashSpec.romImpl := rfl
  simp [StateT.run'_eq, simulateQ_deriveImpl_seedGame, hrom]

/-! ## The second hop: the derivations from the scheme seed -/

/-- What a derivation from the scheme seed reads: a parameter, an address and a suffix. -/
abbrev PrfInput := PublicParam × Address × Array UInt64

/-- The oracles of a game whose derivations from the scheme seed are derivation queries. -/
abbrev PrfSpec := HashSpec.withDerivations PrfInput HashOutput

/-- The derivations as derivation queries, one per call. -/
def prfD : SeedPrf (OracleComp PrfSpec) := fun publicParam a suffix =>
  ofOutput <$> PrfSpec.query (.inr (publicParam, a, suffix))

/-- The game with every derivation from the scheme seed as a derivation query.

Its key keeps a scheme seed of zero, which nothing reads. -/
def prfGame (adversary : ReasonAdversary) : OracleComp PrfSpec FailOutput :=
  failGameOf (HashSpec.withDerivationsLift PrfInput HashOutput) (pure (ofSeed (0 : MasterSeed)))
    (fun _ => prfD)
    adversary

/-- A derivation from `S` is the hash at `P | A | S | suffix`.

The secret is the first hop's table of one entry, the answer that `S` is. -/
def prfEncoding : SecretEncoding HashSpec (Unit → HashOutput) PrfInput HashOutput where
  enc f x := Hash.Keccak.lanesBytes (thInput x.1 x.2.1 ((ofOutput (f ())).toArray ++ x.2.2))
  range_eq _ _ := rfl
  injective f x y h := by
    obtain ⟨publicParam, a, m⟩ := x
    obtain ⟨publicParam', a', m'⟩ := y
    obtain ⟨hpp, ha, hm⟩ := thInput_inj (Hash.Keccak.lanesBytes_injective h)
    obtain ⟨-, hm⟩ := Array.append_inj hm (by simp [Hash.Keccak.Lanes4.toArray])
    exact Prod.ext hpp (Prod.ext ha hm)

/-- A source that always gives one seed is a game whose derivations are that seed's. -/
theorem failGameOf_pure {ι : Type} {spec : OracleSpec ι}
    (pass : QueryImpl OracleWorld (OracleComp spec)) (s : Seed)
    (prfOf : Seed → SeedPrf (OracleComp spec)) (adversary : ReasonAdversary) :
    failGameOf pass (pure s) prfOf adversary =
      failGameOf pass (pure s) (fun _ => prfOf s) adversary := by
  simp only [failGameOf, pure_bind]

/-- An input fixes the table of the first hop, which it encodes in its seed. -/
theorem prfEncoding_fix (f f' : Unit → HashOutput) (x x' : PrfInput)
    (h : prfEncoding.enc f x = prfEncoding.enc f' x') : f = f' := by
  obtain ⟨-, -, hm⟩ := thInput_inj (Hash.Keccak.lanesBytes_injective h)
  obtain ⟨hs, -⟩ := Array.append_inj hm (by simp [Hash.Keccak.Lanes4.toArray])
  funext u
  -- Equal lanes have equal bytes, and the bytes of a 256-bit answer determine it.
  have hb := congrArg Hash.Keccak.lanesBytes hs
  rw [Hash.Keccak.lanesBytes_lanes4, Hash.Keccak.lanesBytes_lanes4, HashSig.bytes_ofOutputLanes,
    HashSig.bytes_ofOutputLanes] at hb
  exact HashSig.ofBV_inj (n := 32) (by simp [HashSig.hashOutputBits]) (Vector.toList_inj.mp hb)

/-- There are `2^256` tables of the first hop. -/
theorem natCard_table : Nat.card (Unit → HashOutput) = 2 ^ 256 := by
  rw [Nat.card_fun, Nat.card_unique (α := Unit), pow_one, Nat.card_eq_fintype_card,
    Fintype.card_bitVec]
  rfl

/-- A given input encodes a derivation under a uniform table with probability `<= 2^-256`. -/
theorem prEvent_mem_range_prfEncoding_le (t : HashSig.HashInput) :
    Pr{let f ← $ᵗ (Unit → HashOutput)}[t ∈ Set.range (prfEncoding.enc f)] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have h := prEvent_mem_range_enc_le prfEncoding prfEncoding_fix t
  rw [natCard_table, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- Fixing the scheme seed to a table entry gives the game whose derivations use that entry. -/
theorem simulateQ_fixDerivations_seedGame (f : Unit → HashOutput)
    (adversary : ReasonAdversary) :
    simulateQ (fixDerivations f) (seedGame adversary) =
      failGameOf (QueryImpl.id' OracleWorld) (pure (ofSeed (0 : MasterSeed)))
        (fun _ => seedPrf (hashOf (QueryImpl.id' OracleWorld)) (ofOutput (f ()))) adversary := by
  have hlift : fixDerivations f ∘ₛ HashSpec.withDerivationsLift Unit HashOutput =
      QueryImpl.id' OracleWorld := by
    funext t
    rcases t with n | t <;> rfl
  have hsrc : simulateQ (fixDerivations (pub := HashSpec) f)
      (ofOutput <$> (SeedSpec.query (.inr ()) : OracleComp SeedSpec HashOutput)) =
      pure (ofOutput (f ())) := by
    simp [fixDerivations]
  have hprf : (fun (s : Seed) publicParam a suffix => simulateQ (fixDerivations f)
      (seedPrf (hashOf (HashSpec.withDerivationsLift Unit HashOutput)) s publicParam a suffix)) =
        seedPrf (hashOf (QueryImpl.id' OracleWorld)) := by
    funext s publicParam a suffix
    simp only [seedPrf, simulateQ_hashOf, hlift]
  unfold seedGame
  erw [simulateQ_failGameOf, hlift, hsrc, hprf]
  exact (failGameOf_pure (QueryImpl.id' OracleWorld) (ofOutput (f ()))
    (seedPrf (hashOf (QueryImpl.id' OracleWorld))) adversary).trans
    (failGameOf_pure_seed (QueryImpl.id' OracleWorld) (ofOutput (f ()))
      (ofSeed (0 : MasterSeed)) (seedPrf (hashOf (QueryImpl.id' OracleWorld)) (ofOutput (f ())))
      adversary)

/-- Answering the derivations at their inputs under a table gives the game of its entry. -/
theorem simulateQ_deriveImpl_prfGame (f : Unit → HashOutput) (adversary : ReasonAdversary) :
    simulateQ (prfEncoding.deriveImpl f) (prfGame adversary) =
      failGameOf (QueryImpl.id' OracleWorld) (pure (ofSeed (0 : MasterSeed)))
        (fun _ => seedPrf (hashOf (QueryImpl.id' OracleWorld)) (ofOutput (f ()))) adversary := by
  have hprf : (fun (_ : Seed) publicParam a suffix => simulateQ (prfEncoding.deriveImpl f)
      (prfD publicParam a suffix)) =
        fun _ => seedPrf (hashOf (QueryImpl.id' OracleWorld)) (ofOutput (f ())) := by
    funext u publicParam a suffix
    simp only [prfD, simulateQ_map, simulateQ_spec_query]
    rfl
  unfold prfGame
  rw [simulateQ_failGameOf, SecretEncoding.deriveImpl_comp_withDerivationsLift, simulateQ_pure,
    hprf]

/-- **The second hop.**

Some request fails in the scheme seed's ideal game at most `q / 2^256` more often than in the next.

The next game is the ideal game of the derivations.

The game with the derivations as derivation queries makes at most `q` hash queries. -/
theorem prEvent_seedGame_ideal_le (adversary : ReasonAdversary) {q : ℕ}
    (hq : IsQueryBoundP (prfGame adversary) IsHashD q) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec Unit HashOutput)
        (seedGame adversary)).run (∅, ∅)}[SomeFailure z.1] ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
          (prfGame adversary)).run (∅, ∅)}[SomeFailure z.1] +
        q * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hop := prEvent_romImpl_deriveImpl_le prfEncoding (ms := $ᵗ (Unit → HashOutput))
    prEvent_mem_range_prfEncoding_le (p := IsHashD) (fun _ _ => trivial) hq
    fun _ z => SomeFailure z
  rw [OracleComp.prEvent_bind_const] at hop
  rw [prEvent_idealImpl_eq_bind_fixDerivations (seedGame adversary) SomeFailure]
  refine le_of_eq_of_le ?_ hop
  simp only [simulateQ_fixDerivations_seedGame, simulateQ_deriveImpl_prfGame]

/-! ## The budget -/

/-- Key generation: the scheme seed, the parameter, and the top tree of `2^16` keys. -/
def keyGenQueries : ℕ := 205 * 2 ^ 16 + 1

/-- One request: two one-time signatures, and the bottom tree when the key does not keep it.

Each one-time signature makes at most `2^32 + 204` calls: all `2^32` trials, its base and chains.

The tree makes `205 * 2^16 - 1` calls. -/
def requestQueries : ℕ := 2 ^ 33 + 205 * 2 ^ 16 + 407

/-- The verification of the forgery: two layers of a digest, 58 chains, a leaf and a path. -/
def verifyQueries : ℕ := 384

/-- The hash calls of a game whose adversary makes `qH` hash queries and `r` requests. -/
def gameQueries (qH r : ℕ) : ℕ := keyGenQueries + qH + r * requestQueries + verifyQueries

section Budget

/- A concrete height would let Lean unfold a whole tree, so the height stays opaque. -/
attribute [local irreducible] LAYER_HEIGHT

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {pass : QueryImpl OracleWorld (OracleComp spec)} {seedSrc : OracleComp spec Seed}
  {prfOf : Seed → SeedPrf (OracleComp spec)}

/-- A hash call of the game is one call of its handler. -/
theorem isQueryBoundP_hashOf (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1) (x : Array UInt64) :
    IsQueryBoundP (hashOf pass x) p 1 :=
  (isQueryBoundP_map_iff _ _ _).2 (hhash _)

/-- A request costs a signature: two searches, and the bottom tree when the key does not keep it. -/
theorem isQueryBoundP_failSignerOf_inr (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1)
    {prf : SeedPrf (OracleComp spec)} (hprf : ∀ publicParam a suffix, IsQueryBoundP
      (prf publicParam a suffix) p 1)
    (request : SignRequest) (sk : SecretKey) :
    IsQueryBoundP ((failSignerOf pass prf (.inr request)).run sk).run p requestQueries := by
  simp only [failSignerOf, StateT.run_mk, WriterT.run_mk]
  refine (isQueryBoundP_map_iff _ _ _).2
    ((Cost.isQueryBoundP_signWithTrials (isQueryBoundP_hashOf hhash) hprf sk _ _).mono ?_)
  simp [requestQueries, Constants.MAX_RANDOMIZER_TRIALS, LAYER_HEIGHT]

/-- **Answering an adversary costs one call per hash query and a request's worst case per request.**

It holds for any oracles with a kept key that pass coins and hashes through.

A request may reply with anything. -/
theorem isQueryBoundP_run_keyed {R : Type}
    (impl : QueryImpl (OracleWorld + (SignRequest →ₒ R))
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp spec))))
    (hcoin : ∀ n sk, IsQueryBoundP ((impl (.inl (.inl n))).run sk).run p 0)
    (hhash : ∀ x sk, IsQueryBoundP ((impl (.inl (.inr x))).run sk).run p 1)
    (hreq : ∀ request sk, IsQueryBoundP ((impl (.inr request)).run sk).run p requestQueries)
    {α : Type} (oa : OracleComp (OracleWorld + (SignRequest →ₒ R)) α) {qH r : ℕ}
    (hh : IsQueryBoundP oa IsAdversaryHash qH) (hr : IsQueryBoundP oa IsAdversaryRequest r)
    (sk : SecretKey) :
    IsQueryBoundP ((simulateQ impl oa).run sk).run p (qH + r * requestQueries) := by
  have h := ((isQueryBoundP_iff_isChargeBound _ _ _).1 hh).add_mul
    ((isQueryBoundP_iff_isChargeBound _ _ _).1 hr) requestQueries
  rw [zero_mul, add_zero] at h
  refine (isQueryBoundP_iff_isChargeBound _ _ _).2
    (OracleComp.isChargeBound_run_simulateQ impl (fun t sk => ?_) h sk)
  rcases t with (n | x) | request
  · simpa [SignatureAlg.IsHashQuery, SignatureAlg.IsSignQuery] using
      (isQueryBoundP_iff_isChargeBound _ _ _).1 (hcoin n sk)
  · simpa [SignatureAlg.IsHashQuery, SignatureAlg.IsSignQuery] using
      (isQueryBoundP_iff_isChargeBound _ _ _).1 (hhash x sk)
  · simpa [SignatureAlg.IsHashQuery, SignatureAlg.IsSignQuery] using
      (isQueryBoundP_iff_isChargeBound _ _ _).1 (hreq request sk)

/-- Answering an adversary costs one call per hash query and a request's worst case per request. -/
theorem isQueryBoundP_run_failSignerOf (hcoin : ∀ n, IsQueryBoundP (pass (.inl n)) p 0)
    (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1) {prf : SeedPrf (OracleComp spec)}
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1) {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) {qH r : ℕ}
    (hh : IsQueryBoundP oa IsAdversaryHash qH) (hr : IsQueryBoundP oa IsAdversaryRequest r)
    (sk : SecretKey) :
    IsQueryBoundP ((simulateQ (failSignerOf pass prf) oa).run sk).run p
      (qH + r * requestQueries) :=
  isQueryBoundP_run_keyed (failSignerOf pass prf)
    (fun n _ => by simpa [failSignerOf] using hcoin n)
    (fun x _ => by simpa [failSignerOf] using hhash x)
    (fun request sk => isQueryBoundP_failSignerOf_inr hhash hprf request sk) oa hh hr sk

/-- Key generation from a scheme seed, over the game's hash: the parameter and the top tree. -/
theorem isQueryBoundP_keyGenFrom (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1) (s : Seed)
    {prf : SeedPrf (OracleComp spec)} (hprf : ∀ publicParam a suffix, IsQueryBoundP
      (prf publicParam a suffix) p 1) :
    IsQueryBoundP (Internal.keyGenFrom (hashOf pass) prf s) p
      (1 + (2 ^ LAYER_HEIGHT * 205 - 1)) := by
  unfold Internal.keyGenFrom
  exact isQueryBoundP_bind (isQueryBoundP_publicParamOf hprf) fun publicParam _ =>
    (isQueryBoundP_bind (m := 0) (isQueryBoundP_build
      (isQueryBoundP_hashOf hhash) hprf publicParam .top
      LAYER_HEIGHT 0) fun _ _ => isQueryBoundP_pure _ _ 0).mono (le_of_eq (Nat.add_zero _))

/-- The game costs the scheme seed, key generation, the adversary's run and the verification. -/
theorem isQueryBoundP_failGameOf (hcoin : ∀ n, IsQueryBoundP (pass (.inl n)) p 0)
    (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1) (hseed : IsQueryBoundP seedSrc p 1)
    (hprf : ∀ s publicParam a suffix, IsQueryBoundP (prfOf s publicParam a suffix) p 1)
    (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    IsQueryBoundP (failGameOf pass seedSrc prfOf adversary) p (gameQueries qH r) := by
  unfold failGameOf
  refine (isQueryBoundP_bind hseed fun s _ =>
    isQueryBoundP_bind (isQueryBoundP_keyGenFrom hhash s (hprf s))
      fun keys _ => isQueryBoundP_bind (isQueryBoundP_run_failSignerOf hcoin hhash (hprf s)
        (adversary.main keys.1) (hh keys.1) (hr keys.1) keys.2) fun z _ =>
          isQueryBoundP_bind (m := 0) (isQueryBoundP_verifyWith (isQueryBoundP_hashOf hhash)
            _ _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  simp only [gameQueries, keyGenQueries, verifyQueries, LAYER_HEIGHT]
  omega

end Budget

/-- The game with the scheme seed as a derivation query keeps to the budget of hash calls. -/
theorem isQueryBoundP_seedGame (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    IsQueryBoundP (seedGame adversary) IsHashD (gameQueries qH r) :=
  isQueryBoundP_failGameOf
    (fun _ => by simp [IsHashD, OracleSpec.withDerivationsLift])
    (fun _ => by simp [IsHashD, OracleSpec.withDerivationsLift])
    ((isQueryBoundP_map_iff _ _ _).2 (by simp [IsHashD]))
    (fun _ _ _ _ => isQueryBoundP_hashOf
      (fun _ => by simp [IsHashD, OracleSpec.withDerivationsLift]) _)
    adversary hh hr

/-- The game with the derivations as derivation queries keeps to the budget of hash calls. -/
theorem isQueryBoundP_prfGame (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    IsQueryBoundP (prfGame adversary) IsHashD (gameQueries qH r) :=
  isQueryBoundP_failGameOf
    (fun _ => by simp [IsHashD, OracleSpec.withDerivationsLift])
    (fun _ => by simp [IsHashD, OracleSpec.withDerivationsLift])
    (isQueryBoundP_pure _ _ _)
    (fun _ _ _ _ => (isQueryBoundP_map_iff _ _ _).2 (by simp [IsHashD]))
    adversary hh hr

/-- **Both hops.**

The adversary makes at most `qH` hash queries and `r` signing requests.

Let `q = gameQueries qH r`.

Some request then fails at most `2 q / 2^256` more often than in the derivations' ideal game. -/
theorem signingFailure_le_prfGame (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    signingFailure adversary ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
          (prfGame adversary)).run (∅, ∅)}[SomeFailure z.1] +
        2 * (gameQueries qH r : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (signingFailure_le_seedGame adversary (isQueryBoundP_seedGame adversary hh hr)).trans ?_
  refine (add_le_add_left (prEvent_seedGame_ideal_le adversary
    (isQueryBoundP_prfGame adversary hh hr)) _).trans_eq ?_
  ring

end EthLib.Cryptography.Xmss.Unforgeability
