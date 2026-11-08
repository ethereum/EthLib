module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Reasons
public import EthLib.Cryptography.Proofs.Xmss.MapMonad
public import EthLib.Cryptography.Proofs.Xmss.QueryBound
public import EthLib.Cryptography.Proofs.DerivationTable

/-!
# Proofs: the signer's secrets as derivations, in two hidden-seed hops

The game where some signing request fails derives every secret from `S_0`, through two hashes.

- The scheme seed is `S = H("leanXMSS" | S_0)`.
- Every other secret is a derivation `H(P | A | S | suffix)` from `S`.

Two hidden-seed hops replace these hashes by queries of their own, derivation queries.

1. `S` becomes a derivation query, read again at each request.
   In the ideal game it is drawn once, uniform, and `S_0` appears nowhere.
2. Every derivation from `S` becomes a derivation query.
   In the ideal game each is drawn from a lazy table on its first use, and `S` appears nowhere.

A hash input fixes the seed it encodes, since the prefixes before the seed have fixed lengths.

So each hop costs at most `q / 2^256`, for a game of at most `q` hash queries.

The event is that some signing request fails, and a hop bounds any event of the game's output.

The game is written once, over a handler of hash queries and a source of derivations.

The real game and the two games with derivation queries are three instances.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open XmssSecurity (OracleWorld HashSpec HashOutput MasterSeed romImpl seedHashInput)

/-- What the game returns: the forgery, the log of the signing requests, and the verification. -/
abbrev FailOutput := Forgery × QueryLog SigningSpec × Bool

/-- Some signing request of the game failed. -/
def SomeFailure (z : FailOutput) : Prop :=
  ∃ entry ∈ z.2.1, entry.2 = none

/-! ## The game over a source of derivations -/

section Source

variable {ι : Type} {spec : OracleSpec ι}

/-- The hash of a game whose hash and coin queries a handler answers. -/
def hashOf (pass : QueryImpl OracleWorld (OracleComp spec)) (x : ByteArray) :
    OracleComp spec (Vector UInt8 32) :=
  ofOutput <$> pass (.inr x.data.toList)

/-- The game's oracles: hash and coin queries go to `pass`, and a request signs.

A request first obtains the value its secrets derive from, as the signer does. -/
def failSignerOf {σ : Type} (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec σ) (prfOf : σ → SeedPrf (OracleComp spec)) :
    QueryImpl (OracleWorld + ReasonSigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp spec))
  | .inl t => (liftM (pass t) : WriterT (QueryLog SigningSpec) (OracleComp spec) _)
  | .inr request => WriterT.mk (do
      let s ← seedSrc
      let pp ← publicParamOf (prfOf s)
      let result ← signDerived (hashOf pass) (prfOf s) pp request.leafIndex request.message
      return (result, [⟨request, result.toOption⟩]))

/-- The game of a signing failure after the seed: keys, the adversary, then the verification.

The secrets derive from `prfOf s`, where `s` comes from `seedSrc`. -/
def failGameOf {σ : Type} (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec σ) (prfOf : σ → SeedPrf (OracleComp spec))
    (adversary : ReasonAdversary) : OracleComp spec FailOutput := do
  let s ← seedSrc
  let pk ← publicKeyOf (hashOf pass) (prfOf s)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (failSignerOf pass seedSrc prfOf) (adversary.main pk)).run
  let verified ← verifyWith (hashOf pass) pk forgery.message forgery.signature
  return (forgery, log, verified)

section Map

variable {ι' : Type} {spec' : OracleSpec ι'} (so : QueryImpl spec (OracleComp spec'))

/-- Simulating a hash call gives the hash of the simulated handler. -/
theorem simulateQ_hashOf (pass : QueryImpl OracleWorld (OracleComp spec)) (x : ByteArray) :
    simulateQ so (hashOf pass x) = hashOf (so ∘ₛ pass) x := by
  simp [hashOf, QueryImpl.apply_compose]

/-- Simulating a request gives the request over the simulated handler and source. -/
theorem simulateQ_run_failSignerOf_apply {σ : Type}
    (pass : QueryImpl OracleWorld (OracleComp spec)) (seedSrc : OracleComp spec σ)
    (prfOf : σ → SeedPrf (OracleComp spec)) (t : (OracleWorld + ReasonSigningSpec).Domain) :
    simulateQ so (failSignerOf pass seedSrc prfOf t).run =
      (failSignerOf (so ∘ₛ pass) (simulateQ so seedSrc)
        (fun s pp a suffix => simulateQ so (prfOf s pp a suffix)) t).run := by
  rcases t with t | request
  · simp [failSignerOf, QueryImpl.apply_compose]
  · simp only [failSignerOf, WriterT.run_mk, simulateQ_bind, simulateQ_pure]
    refine bind_congr fun s => ?_
    rw [publicParamOf_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
      (fun x f => simulateQ_bind so x f)]
    refine bind_congr fun pp => ?_
    rw [signDerived_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
      (fun x f => simulateQ_bind so x f) _ _ (fun f x => simulateQ_map so x f)]
    simp only [simulateQ_hashOf]

/-- Simulating the run of the game's oracles gives their run over the simulated sources. -/
theorem simulateQ_run_failSignerOf {σ : Type}
    (pass : QueryImpl OracleWorld (OracleComp spec)) (seedSrc : OracleComp spec σ)
    (prfOf : σ → SeedPrf (OracleComp spec)) {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) :
    simulateQ so (simulateQ (failSignerOf pass seedSrc prfOf) oa).run =
      (simulateQ (failSignerOf (so ∘ₛ pass) (simulateQ so seedSrc)
        (fun s pp a suffix => simulateQ so (prfOf s pp a suffix))) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', simulateQ_map,
      simulateQ_run_failSignerOf_apply, ih]

end Map

/-- Simulating the queries of the game gives the game over the simulated handler and source. -/
theorem simulateQ_failGameOf {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}
    (so : QueryImpl spec (OracleComp spec')) (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec σ) (prfOf : σ → SeedPrf (OracleComp spec))
    (adversary : ReasonAdversary) :
    simulateQ so (failGameOf pass seedSrc prfOf adversary) =
      failGameOf (so ∘ₛ pass) (simulateQ so seedSrc)
        (fun s pp a suffix => simulateQ so (prfOf s pp a suffix)) adversary := by
  simp only [failGameOf, simulateQ_bind, simulateQ_pure, simulateQ_run_failSignerOf]
  refine bind_congr fun s => ?_
  rw [publicKeyOf_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
    (fun x f => simulateQ_bind so x f)]
  simp only [simulateQ_hashOf]
  refine bind_congr fun pk => bind_congr fun z => ?_
  rw [verifyWith_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
    (fun x f => simulateQ_bind so x f)]
  simp only [simulateQ_hashOf]

end Source

/-! ## The real game -/

/-- The game's `H`, lifted to hash and coin queries, is the hash of the identity handler. -/
theorem liftM_H (x : ByteArray) :
    (liftM (H x) : OracleComp OracleWorld (Vector UInt8 32)) =
      hashOf (QueryImpl.id' OracleWorld) x := by
  simp [H, queryH, hashOf, HashSig.oracleHash]
  rfl

/-- The derivations of the game, lifted, are those over the hash of the identity handler. -/
theorem liftM_seedPrf (s : Seed) :
    (fun pp a suffix =>
        (liftM (seedPrf H s pp a suffix) : OracleComp OracleWorld (Vector UInt8 32))) =
      seedPrf (hashOf (QueryImpl.id' OracleWorld)) s := by
  funext pp a suffix
  exact liftM_H _

/-- The real game's oracles, for the secret key of a seed, are the game's over that seed. -/
theorem reasonOracles_eq_failSignerOf (seed : Seed) :
    QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        reasonSigningOracle ⟨seed⟩ =
      failSignerOf (QueryImpl.id' OracleWorld)
        (schemeSeed (hashOf (QueryImpl.id' OracleWorld)) seed)
        (seedPrf (hashOf (QueryImpl.id' OracleWorld))) := by
  funext t
  rcases t with t | request
  · rfl
  · rw [QueryImpl.add_apply_inr]
    simp only [reasonSigningOracle, failSignerOf]
    refine congrArg WriterT.mk ?_
    have hseed : (liftM (schemeSeed H seed) : OracleComp OracleWorld Seed) =
        schemeSeed (hashOf (QueryImpl.id' OracleWorld)) seed :=
      liftM_H _
    simp only [signWith, liftM_bind, map_bind, hseed]
    refine bind_congr fun s => ?_
    rw [publicParamOf_map_monad (fun {β} (c : OracleComp HashSpec β) =>
      (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
      liftM_seedPrf]
    refine bind_congr fun pp => ?_
    rw [signDerived_map_monad (fun {β} (c : OracleComp HashSpec β) =>
      (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f)
      _ _ (fun f x => liftM_map f x), liftM_seedPrf, funext liftM_H]
    simp

/-- The game of a signing failure, before the random oracle, as the game over the seed `S_0`. -/
theorem reasonRun_eq_failGameOf (adversary : ReasonAdversary) :
    reasonRun adversary = (liftM XmssSecurity.sampleMasterSeed : OracleComp OracleWorld _) >>=
      fun s0 => failGameOf (QueryImpl.id' OracleWorld)
        (schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0))
        (seedPrf (hashOf (QueryImpl.id' OracleWorld))) adversary := by
  unfold reasonRun sampleSeed
  simp only [liftM_map, bind_map_left]
  refine bind_congr fun s0 => ?_
  have hseed : (liftM (schemeSeed H (ofSeed s0)) : OracleComp OracleWorld Seed) =
      schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0) :=
    liftM_H _
  simp only [failGameOf, keyGenWith, liftM_bind, liftM_pure, bind_assoc, pure_bind, hseed]
  refine bind_congr fun s => ?_
  rw [publicKeyOf_map_monad (fun {β} (c : OracleComp HashSpec β) =>
    (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
    reasonOracles_eq_failSignerOf, funext liftM_H, liftM_seedPrf]
  refine bind_congr fun pk => bind_congr fun z => ?_
  rw [verifyWith_map_monad (fun {β} (c : OracleComp HashSpec β) =>
    (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
    funext liftM_H]

/-- The real game draws `S_0`, and each request hashes it again into `S`, as the signer does. -/
theorem signingFailure_eq (adversary : ReasonAdversary) :
    signingFailure adversary =
      Pr{let s0 ← XmssSecurity.sampleMasterSeed
         let z ← (simulateQ romImpl (failGameOf (QueryImpl.id' OracleWorld)
           (schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0))
           (seedPrf (hashOf (QueryImpl.id' OracleWorld))) adversary)).run' ∅}[SomeFailure z] := by
  refine (prEvent_countedOracle (reasonRun adversary) SomeFailure).trans ?_
  rw [reasonRun_eq_failGameOf, XmssSecurity.Seeded.run'_lift_sample_bind]
  simp only [prEvent_norm]

/-! ## The first hop: the scheme seed -/

/-- The oracles of a game whose scheme seed is a derivation query. -/
abbrev SeedSpec := HashSpec.withDerivations Unit HashOutput

/-- The game with the scheme seed `S` as a derivation query, which each request reads again. -/
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
  have hinput : (ByteArray.mk Constants.SEED_TAG.toArray ++ packBytes (ofSeed s0)).data.toList
      = seedHashInput s0 := by
    simp only [HashSig.toList_data_append, HashSig.toList_data_packBytes, toList_ofSeed]
    rfl
  have hsrc : simulateQ (seedEncoding.deriveImpl s0)
      (ofOutput <$> SeedSpec.query (.inr ())) =
        schemeSeed (hashOf (QueryImpl.id' OracleWorld)) (ofSeed s0) := by
    rw [simulateQ_map, simulateQ_spec_query]
    unfold schemeSeed hashOf
    rw [hinput]
    rfl
  have hprf : (fun (s : Seed) pp a suffix => simulateQ (seedEncoding.deriveImpl s0)
      (seedPrf (hashOf (HashSpec.withDerivationsLift Unit HashOutput)) s pp a suffix)) =
        seedPrf (hashOf (QueryImpl.id' OracleWorld)) := by
    funext s pp a suffix
    simp only [seedPrf, simulateQ_hashOf, SecretEncoding.deriveImpl_comp_withDerivationsLift]
  unfold seedGame
  erw [simulateQ_failGameOf, SecretEncoding.deriveImpl_comp_withDerivationsLift, hsrc, hprf]
  rfl

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
abbrev PrfInput := PublicParam × Address × ByteArray

/-- The oracles of a game whose derivations from the scheme seed are derivation queries. -/
abbrev PrfSpec := HashSpec.withDerivations PrfInput HashOutput

/-- The derivations as derivation queries, one per call. -/
def prfD : SeedPrf (OracleComp PrfSpec) := fun pp a suffix =>
  ofOutput <$> PrfSpec.query (.inr (pp, a, suffix))

/-- The game with every derivation from the scheme seed as a derivation query. -/
def prfGame (adversary : ReasonAdversary) : OracleComp PrfSpec FailOutput :=
  failGameOf (HashSpec.withDerivationsLift PrfInput HashOutput) (pure ()) (fun _ => prfD)
    adversary

/-- A derivation from `S` is the hash at `P | A | S | suffix`.

The secret is the first hop's table of one entry, the answer that `S` is. -/
def prfEncoding : SecretEncoding HashSpec (Unit → HashOutput) PrfInput HashOutput where
  enc f x := (thInput x.1 x.2.1 (packBytes (ofOutput (f ())) ++ x.2.2)).data.toList
  range_eq _ _ := rfl
  injective f x y h := by
    obtain ⟨pp, a, m⟩ := x
    obtain ⟨pp', a', m'⟩ := y
    obtain ⟨hpp, ha, hm⟩ := thInput_inj (ByteArray.ext (Array.toList_inj.mp h))
    obtain ⟨-, hm⟩ := HashSig.byteArray_append_inj hm rfl
    exact Prod.ext hpp (Prod.ext ha hm)

/-- A source that always gives one value is a game whose derivations fix that value. -/
theorem failGameOf_pure {σ : Type} (pass : QueryImpl OracleWorld (OracleComp spec)) (s : σ)
    (prfOf : σ → SeedPrf (OracleComp spec)) (adversary : ReasonAdversary) :
    failGameOf pass (pure s) prfOf adversary =
      failGameOf pass (pure ()) (fun _ => prfOf s) adversary := by
  have h : failSignerOf pass (pure s) prfOf = failSignerOf pass (pure ()) (fun _ => prfOf s) := by
    funext t
    rcases t with t | request
    · rfl
    · simp only [failSignerOf, pure_bind]
  simp only [failGameOf, pure_bind, h]

/-- An input fixes the table of the first hop, which it encodes in its seed. -/
theorem prfEncoding_fix (f f' : Unit → HashOutput) (x x' : PrfInput)
    (h : prfEncoding.enc f x = prfEncoding.enc f' x') : f = f' := by
  obtain ⟨-, -, hm⟩ := thInput_inj (ByteArray.ext (Array.toList_inj.mp h))
  obtain ⟨hs, -⟩ := HashSig.byteArray_append_inj hm (by simp)
  funext u
  exact HashSig.ofBV_inj (n := 32) (by simp [HashSig.hashOutputBits])
    (packBytes_injective hs)

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
      failGameOf (QueryImpl.id' OracleWorld) (pure ())
        (fun _ => seedPrf (hashOf (QueryImpl.id' OracleWorld)) (ofOutput (f ()))) adversary := by
  have hlift : fixDerivations f ∘ₛ HashSpec.withDerivationsLift Unit HashOutput =
      QueryImpl.id' OracleWorld := by
    funext t
    rcases t with n | t <;> rfl
  have hsrc : simulateQ (fixDerivations (pub := HashSpec) f)
      (ofOutput <$> (SeedSpec.query (.inr ()) : OracleComp SeedSpec HashOutput)) =
      pure (ofOutput (f ())) := by
    simp [fixDerivations]
  have hprf : (fun (s : Seed) pp a suffix => simulateQ (fixDerivations f)
      (seedPrf (hashOf (HashSpec.withDerivationsLift Unit HashOutput)) s pp a suffix)) =
        seedPrf (hashOf (QueryImpl.id' OracleWorld)) := by
    funext s pp a suffix
    simp only [seedPrf, simulateQ_hashOf, hlift]
  unfold seedGame
  erw [simulateQ_failGameOf, hlift, hsrc, hprf, failGameOf_pure]

/-- Answering the derivations at their inputs under a table gives the game of its entry. -/
theorem simulateQ_deriveImpl_prfGame (f : Unit → HashOutput) (adversary : ReasonAdversary) :
    simulateQ (prfEncoding.deriveImpl f) (prfGame adversary) =
      failGameOf (QueryImpl.id' OracleWorld) (pure ())
        (fun _ => seedPrf (hashOf (QueryImpl.id' OracleWorld)) (ofOutput (f ()))) adversary := by
  have hprf : (fun (_ : Unit) pp a suffix => simulateQ (prfEncoding.deriveImpl f)
      (prfD pp a suffix)) =
        fun _ => seedPrf (hashOf (QueryImpl.id' OracleWorld)) (ofOutput (f ())) := by
    funext u pp a suffix
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

/-- A hash query of the adversary. -/
def IsAdversaryHash : (OracleWorld + ReasonSigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- A signing request of the adversary. -/
def IsAdversaryRequest : (OracleWorld + ReasonSigningSpec).Domain → Prop
  | .inr _ => True
  | _ => False

instance : DecidablePred IsAdversaryHash := fun t => by
  rcases t with (_ | _) | _ <;> simp only [IsAdversaryHash] <;> infer_instance

instance : DecidablePred IsAdversaryRequest := fun t => by
  rcases t with (_ | _) | _ <;> simp only [IsAdversaryRequest] <;> infer_instance

/-- Key generation: the scheme seed, the parameter, and the `2^16` keys of the top tree. -/
def keyGenQueries : ℕ := 205 * 2 ^ 16 + 1

/-- One request: the scheme seed, the parameter, two searches of `2^32` trials, and three trees. -/
def requestQueries : ℕ := 2 ^ 33 + 615 * 2 ^ 16

/-- The verification of the forgery: two layers of a digest, 58 chains, a leaf and a path. -/
def verifyQueries : ℕ := 384

/-- The hash calls of a game whose adversary makes `qH` hash queries and `r` requests. -/
def gameQueries (qH r : ℕ) : ℕ := keyGenQueries + qH + r * requestQueries + verifyQueries

section Budget

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {σ : Type}
  {pass : QueryImpl OracleWorld (OracleComp spec)} {seedSrc : OracleComp spec σ}
  {prfOf : σ → SeedPrf (OracleComp spec)}

/-- A hash call of the game is one call of its handler. -/
theorem isQueryBoundP_hashOf (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1) (x : ByteArray) :
    IsQueryBoundP (hashOf pass x) p 1 :=
  (isQueryBoundP_map_iff _ _ _).2 (hhash _)

/-- A request costs the seed, the parameter and a signature. -/
theorem isQueryBoundP_failSignerOf_inr (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1)
    (hseed : IsQueryBoundP seedSrc p 1)
    (hprf : ∀ s pp a suffix, IsQueryBoundP (prfOf s pp a suffix) p 1) (request : SignRequest) :
    IsQueryBoundP (failSignerOf pass seedSrc prfOf (.inr request)).run p requestQueries := by
  simp only [failSignerOf, WriterT.run_mk]
  refine (isQueryBoundP_bind hseed fun s _ =>
    isQueryBoundP_bind (isQueryBoundP_publicParamOf (hprf s)) fun pp _ =>
      isQueryBoundP_bind (m := 0) (isQueryBoundP_signDerived (isQueryBoundP_hashOf hhash) (hprf s)
        pp _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  simp only [requestQueries]
  omega

/-- Answering an adversary costs one call per hash query and a request's worst case per request. -/
theorem isQueryBoundP_run_failSignerOf (hcoin : ∀ n, IsQueryBoundP (pass (.inl n)) p 0)
    (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1) (hseed : IsQueryBoundP seedSrc p 1)
    (hprf : ∀ s pp a suffix, IsQueryBoundP (prfOf s pp a suffix) p 1) {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) {qH r : ℕ}
    (hh : IsQueryBoundP oa IsAdversaryHash qH) (hr : IsQueryBoundP oa IsAdversaryRequest r) :
    IsQueryBoundP (simulateQ (failSignerOf pass seedSrc prfOf) oa).run p
      (qH + r * requestQueries) := by
  induction oa using OracleComp.inductionOn generalizing qH r with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hh hr
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind']
    rcases t with (n | x) | request
    · simp only [IsAdversaryHash, IsAdversaryRequest, ite_false] at hh hr
      refine (isQueryBoundP_bind (n := 0) ?_ fun u _ =>
        (isQueryBoundP_map_iff _ _ _).2 (ih u.1 (hh.2 u.1) (hr.2 u.1))).mono (by omega)
      simpa [failSignerOf] using hcoin n
    · simp only [IsAdversaryHash, IsAdversaryRequest, ite_true, ite_false] at hh hr
      have : 0 < qH := by simpa using hh.1
      refine (isQueryBoundP_bind (n := 1) ?_ fun u _ =>
        (isQueryBoundP_map_iff _ _ _).2 (ih u.1 (hh.2 u.1) (hr.2 u.1))).mono (by omega)
      simpa [failSignerOf] using hhash x
    · simp only [IsAdversaryHash, IsAdversaryRequest, ite_true, ite_false] at hh hr
      have : 0 < r := by simpa using hr.1
      refine (isQueryBoundP_bind (isQueryBoundP_failSignerOf_inr hhash hseed hprf request)
        fun u _ => (isQueryBoundP_map_iff _ _ _).2 (ih u.1 (hh.2 u.1) (hr.2 u.1))).mono ?_
      have : (r - 1) * requestQueries + requestQueries = r * requestQueries := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this]
      omega

/-- The game costs key generation, the adversary's run and the verification. -/
theorem isQueryBoundP_failGameOf (hcoin : ∀ n, IsQueryBoundP (pass (.inl n)) p 0)
    (hhash : ∀ x, IsQueryBoundP (pass (.inr x)) p 1) (hseed : IsQueryBoundP seedSrc p 1)
    (hprf : ∀ s pp a suffix, IsQueryBoundP (prfOf s pp a suffix) p 1)
    (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    IsQueryBoundP (failGameOf pass seedSrc prfOf adversary) p (gameQueries qH r) := by
  unfold failGameOf
  refine (isQueryBoundP_bind hseed fun s _ =>
    isQueryBoundP_bind (isQueryBoundP_publicKeyOf (isQueryBoundP_hashOf hhash) (hprf s))
      fun pk _ => isQueryBoundP_bind (isQueryBoundP_run_failSignerOf hcoin hhash hseed hprf
        (adversary.main pk) (hh pk) (hr pk)) fun z _ =>
          isQueryBoundP_bind (m := 0) (isQueryBoundP_verifyWith (isQueryBoundP_hashOf hhash)
            _ _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  simp only [gameQueries, keyGenQueries, verifyQueries]
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
