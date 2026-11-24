module

public import EthLib.Cryptography.Proofs.Sphincs.Cost
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Count

/-!
# Proofs: the scheme's hash calls in a run are at most a constant per request

Under one answer function, a run of the game makes the calls of the adversary and of the scheme.

With `q` calls of the adversary and `r` requests, a run makes at most `q + 264193 + r * S + 491`.

Here `S` is `470595 + 3 * 2^32`.

Key generation makes 264193 calls.

A verification makes at most 491 calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)

variable (f : QueryImpl HashSpec Id)

/-! ## The scheme's calls -/

/-- The game's hash makes one oracle call, on every path. -/
theorem isTotalQueryBound_H (x : ByteArray) : IsTotalQueryBound (H x) 1 :=
  (isQueryBound_map_iff _ _ _ _ _).2 ((isQueryBound_query_iff _ _ _ _).2 Nat.one_pos)

/-! ## The game with the adversary's counter -/

/-- Forgetting the count gives the computation back. -/
theorem fst_map_counted {ι : Type} {spec : OracleSpec ι} {α : Type} (p : ι → Prop)
    [DecidablePred p] (oa : OracleComp spec α) :
    Prod.fst <$> SphincsSecurity.QueryCap.counted p oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [SphincsSecurity.QueryCap.counted_query_bind]
    simp only [map_bind, map_pure]
    refine bind_congr fun a => ?_
    conv_rhs => rw [← ih a]
    rw [map_eq_bind_pure_comp]
    rfl

/-- The game is the game with the adversary's counter, its count forgotten. -/
theorem gameCore_eq_map (adversary : Adversary) :
    gameCore adversary = Prod.fst <$> adversaryGameCore adversary := by
  unfold gameCore adversaryGameCore
  simp only [map_bind, map_pure]
  refine bind_congr fun seed => bind_congr fun ⟨sk, pk⟩ => ?_
  conv_lhs => rw [← fst_map_counted IsAdversaryHashCall (adversary.main pk)]
  rw [simulateQ_map, WriterT.run_map, bind_map_left]

/-- Coins make no hash call. -/
theorem countedRun_liftM_coins {α : Type} (p : ProbComp α) :
    countedRun f (liftM p : OracleComp OracleWorld α) = (fun x => (x, 0)) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure x => exact countedRun_pure f x
  | query_bind t k ih =>
    rw [← liftComp_eq_liftM, liftComp_bind, liftComp_liftM_query]
    simp only [liftComp_eq_liftM]
    have hq : countedRun f (liftM (unifSpec.query t) : OracleComp OracleWorld _) =
        (fun x => (x, 0)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
      change simulateQ (unifFwdAnswerImpl f)
        (SphincsSecurity.QueryCap.counted isHashCall
          (liftM (OracleWorld.query (.inl t)))) = _
      rw [SphincsSecurity.QueryCap.counted_query]
      simp only [simulateQ_map, simulateQ_spec_query, unifFwdAnswerImpl, isHashCall,
        Sum.isRight_inl]
      rfl
    rw [countedRun_bind, hq, bind_map_left, map_bind]
    simp only [ih, Nat.zero_add, map_eq_bind_pure_comp, Prod.mk.eta, bind_pure]

/-- A query costs 1 if it is a hash call and 0 if it is a coin. -/
theorem countedRun_query (t : OracleWorld.Domain) :
    countedRun f (liftM (OracleWorld.query t)) =
      (fun u => (u, if isHashCall t then 1 else 0)) <$> unifFwdAnswerImpl f t := by
  change simulateQ (unifFwdAnswerImpl f)
    (SphincsSecurity.QueryCap.counted isHashCall (liftM (OracleWorld.query t))) = _
  rw [SphincsSecurity.QueryCap.counted_query, simulateQ_map, simulateQ_spec_query]

/-- A run of a bound computation is a run of the first part, then of the rest. -/
theorem mem_support_countedRun_bind {α β : Type} (oa : OracleComp OracleWorld α)
    (k : α → OracleComp OracleWorld β) (r : β × Nat) :
    r ∈ support (countedRun f (oa >>= k)) ↔
      ∃ x ∈ support (countedRun f oa), ∃ y ∈ support (countedRun f (k x.1)),
        r = (y.1, x.2 + y.2) := by
  rw [countedRun_bind, mem_support_bind_iff]
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]

/-- The adversary's run with its counter makes its own calls and those of its requests.

Each request makes at most `S` calls. -/
theorem calls_run_counted {α : Type} (s : QueryImpl SigningSpec (OracleComp OracleWorld))
    (S : Nat) (hs : ∀ msg, ∀ r ∈ support (countedRun f (s msg)), r.2 ≤ S)
    (A : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ r ∈ support (countedRun f (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + QueryImpl.withLogging s)
        (SphincsSecurity.QueryCap.counted IsAdversaryHashCall A)).run),
      r.2 ≤ r.1.1.2 + r.1.2.length * S := by
  induction A using OracleComp.inductionOn with
  | pure a =>
    intro r hr
    rw [SphincsSecurity.QueryCap.counted_pure, simulateQ_pure, WriterT.run_pure',
      countedRun_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Nat.zero_le _
  | query_bind t k ih =>
    intro r hr
    rw [SphincsSecurity.QueryCap.counted_query_bind] at hr
    rcases t with t | msg
    · simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind,
        QueryImpl.add_apply_inl, QueryImpl.ofLift_apply, simulateQ_pure, WriterT.run_pure',
        map_pure] at hr
      have hl : (liftM (OracleWorld.query t) :
          WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run =
            (fun u => (u, ∅)) <$> liftM (OracleWorld.query t) := rfl
      rw [hl, bind_map_left, mem_support_countedRun_bind] at hr
      obtain ⟨x, hx, y, hy, rfl⟩ := hr
      rw [countedRun_query, support_map] at hx
      obtain ⟨u, -, rfl⟩ := hx
      simp only [map_bind, map_pure] at hy
      rw [bind_pure_comp, countedRun_map, support_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' := ih u z hz
      have hc : IsAdversaryHashCall (.inl t) ↔ isHashCall t := Iff.rfl
      simp only [hc, List.empty_eq, List.nil_append, List.append_nil]
      split <;> omega
    · simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.add_apply_inr,
        QueryImpl.withLogging_apply, WriterT.run_tell, bind_assoc,
        map_eq_bind_pure_comp, Function.comp_def, pure_bind, simulateQ_pure,
        WriterT.run_pure'] at hr
      have hl : (liftM (s msg) : WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run =
          (fun u => (u, ∅)) <$> s msg := rfl
      rw [hl, bind_map_left, mem_support_countedRun_bind] at hr
      obtain ⟨x, hx, y, hy, rfl⟩ := hr
      rw [bind_pure_comp, countedRun_map, support_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' := ih x.1 z hz
      have hx' := hs msg x hx
      have hc : ¬IsAdversaryHashCall (.inr msg) := id
      simp only [hc, ↓reduceIte, Nat.zero_add, List.empty_eq, List.nil_append, List.append_nil,
        List.length_cons, List.singleton_append]
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- A run of a hash computation, then more, is a run of the rest after the computation's calls. -/
theorem mem_support_countedRun_liftM_bind {β γ : Type} (oc : OracleComp HashSpec β)
    (k : β → OracleComp OracleWorld γ) (r : γ × Nat) :
    r ∈ support (countedRun f ((liftM oc : OracleComp OracleWorld β) >>= k)) ↔
      ∃ y ∈ support (countedRun f (k (evalWithAnswerFn f oc))),
        r = (y.1, hashCalls f oc + y.2) := by
  rw [countedRun_bind, countedRun_liftM, pure_bind, mem_support_bind_iff]
  simp only [support_pure, Set.mem_singleton_iff]

/-- A hash computation with at most `n` calls under `f` makes at most `n` calls in every run. -/
theorem calls_liftM_le {β : Type} (oc : OracleComp HashSpec β) (n : Nat)
    (h : hashCalls f oc ≤ n) :
    ∀ r ∈ support (countedRun f (liftM oc : OracleComp OracleWorld β)), r.2 ≤ n := by
  intro r hr
  rw [countedRun_liftM, support_pure, Set.mem_singleton_iff] at hr
  rw [hr]
  exact h

/-- The answer of the signing oracle of the game, on a secret key and a message. -/
def signerOf (sk : SecretKey) (msg : Message) : OracleComp HashSpec (Option Signature) :=
  Except.toOption <$> signWith H sk msg

/-- The verification of the game, on a public key and a forgery. -/
def verifierOf (pk : PublicKey) (forgery : Forgery) : OracleComp HashSpec Bool :=
  verifyWith H pk forgery.message forgery.signature

/-- The verdict of the game, on a forgery, the log of requests and the verification. -/
def verdictOf (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool) : Bool :=
  decide (Valid log ∧ ¬Contains log forgery) && verified

/-- A signing request makes at most `470595 + 3 * 2^32` calls.

Each counter search makes at most `2^32` of them. -/
theorem hashCalls_signerOf_le (sk : SecretKey) (msg : Message) :
    hashCalls f (signerOf sk msg) ≤ signCalls :=
  (hashCalls_map f _ _).trans_le (Cost.hashCalls_signWith_le f H (hashCalls_queryH f) sk msg)

/-- A game of this shape makes the adversary's calls, at most `K`, then `S` per request, then `V`.

Key generation makes at most `K` calls, a request at most `S` and the verification at most `V`. -/
theorem calls_game {Seed' SK PK : Type} (seeds : ProbComp Seed')
    (keygen : Seed' → OracleComp HashSpec (SK × PK))
    (signer : SK → Message → OracleComp HashSpec (Option Signature))
    (verify : PK → Forgery → OracleComp HashSpec Bool)
    (win : Forgery → QueryLog SigningSpec → Bool → Bool)
    (main : PK → OracleComp (OracleWorld + SigningSpec) Forgery) (K S V : Nat)
    (hK : ∀ seed, hashCalls f (keygen seed) ≤ K)
    (hS : ∀ sk msg, hashCalls f (signer sk msg) ≤ S)
    (hV : ∀ seed ∈ support seeds, ∀ forgery,
      hashCalls f (verify (evalWithAnswerFn f (keygen seed)).2 forgery) ≤ V) :
    ∀ r ∈ support (countedRun f (do
      let seed ← liftM seeds
      let keys ← liftM (keygen seed)
      let run ← (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
            QueryImpl.withLogging (fun msg => liftM (signer keys.1 msg) :
              QueryImpl SigningSpec (OracleComp OracleWorld)))
          (SphincsSecurity.QueryCap.counted IsAdversaryHashCall (main keys.2))).run
      let verified ← liftM (verify keys.2 run.1.1)
      pure (win run.1.1 run.2 verified, run.1.2, run.2.length))),
      r.2 ≤ r.1.2.1 + K + r.1.2.2 * S + V := by
  intro r hr
  rw [mem_support_countedRun_bind, countedRun_liftM_coins, support_map] at hr
  obtain ⟨x, ⟨seed, hseed, rfl⟩, y, hy, rfl⟩ := hr
  rw [mem_support_countedRun_liftM_bind] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hk := hK seed
  have hv := hV seed hseed
  generalize evalWithAnswerFn f (keygen seed) = kp at hz hv
  rw [mem_support_countedRun_bind] at hz
  obtain ⟨⟨⟨⟨forgery, calls⟩, log⟩, n⟩, hw, v, hv', rfl⟩ := hz
  have hw' := calls_run_counted f _ S (fun msg => calls_liftM_le f _ S (hS kp.1 msg)) _ _ hw
  rw [mem_support_countedRun_liftM_bind, countedRun_pure, support_pure] at hv'
  obtain ⟨u, hu, rfl⟩ := hv'
  rw [Set.mem_singleton_iff] at hu
  subst hu
  have := hv forgery
  dsimp only at hw' this ⊢
  omega

/-- The game with the adversary's counter, with its keys and its run read by projection. -/
theorem adversaryGameCore_eq (adversary : Adversary) :
    adversaryGameCore adversary = (do
      let seed ← liftM sampleSeed
      let keys : SecretKey × PublicKey ← liftM (keyGenWith H seed)
      let run : (Forgery × Nat) × QueryLog SigningSpec ←
        (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
            QueryImpl.withLogging (fun msg => liftM (signerOf keys.1 msg) :
              QueryImpl SigningSpec (OracleComp OracleWorld)))
          (SphincsSecurity.QueryCap.counted IsAdversaryHashCall (adversary.main keys.2))).run
      let verified ← liftM (verifierOf keys.2 run.1.1)
      pure (verdictOf run.1.1 run.2 verified, run.1.2, run.2.length)) := by
  unfold adversaryGameCore signingOracle signerOf verifierOf verdictOf
  refine bind_congr fun seed => bind_congr fun ⟨sk, pk⟩ => ?_
  refine bind_congr fun ⟨⟨forgery, calls⟩, log⟩ => ?_
  rfl

/-- A run of the game makes the adversary's calls, those of key generation and of verification.

It also makes at most `470595 + 3 * 2^32` calls per signing request. -/
theorem calls_adversaryGameCore (adversary : Adversary) :
    ∀ r ∈ support (countedRun f (adversaryGameCore adversary)),
      r.2 ≤ r.1.2.1 + keyGenCalls + r.1.2.2 * signCalls + verifyCalls := by
  rw [adversaryGameCore_eq]
  refine calls_game f sampleSeed (keyGenWith H) signerOf verifierOf verdictOf adversary.main
    keyGenCalls signCalls verifyCalls
    -- Key generation makes 264193 calls.
    (fun seed => (Cost.hashCalls_keyGenWith_eq f H (hashCalls_queryH f) seed).le)
    (hashCalls_signerOf_le f)
    -- A verification makes at most 491 calls.
    (fun _ _ _ => Cost.hashCalls_verifyWith_le f H isTotalQueryBound_H _ _ _)

/-! ## The budget transfers -/

omit f in
/-- The oracles of the experiment with the adversary's counter are the plain random oracle. -/
theorem adversaryOracle_eq : (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec
    (StateT (QueryCache HashSpec) ProbComp))) = HashSpec.romImpl := rfl

omit f in
/-- The experiment with the adversary's counter runs its game against the plain random oracle. -/
theorem adversaryExperiment_eq (adversary : Adversary) :
    adversaryExperiment adversary =
      (simulateQ HashSpec.romImpl (adversaryGameCore adversary)).run' ∅ := by
  rw [adversaryExperiment, adversaryOracle_eq]

omit f in
/-- Forgetting the count of a counted run gives a run against the plain random oracle. -/
theorem mem_support_run'_of_withAddCost {α : Type} (oa : OracleComp OracleWorld α)
    (r : α × Nat)
    (h : r ∈ support ((simulateQ (HashSpec.romImpl.withAddCost hashCost) oa).run.run' ∅)) :
    r.1 ∈ support ((simulateQ HashSpec.romImpl oa).run' ∅) := by
  rw [← QueryImpl.fst_map_run_simulateQ_withAddCost _ hashCost]
  simp only [StateT.run'_eq, StateT.run_map, support_map, Set.mem_image] at h ⊢
  obtain ⟨⟨r', cache⟩, hmem, rfl⟩ := h
  exact ⟨(r'.1, cache), ⟨(r', cache), hmem, rfl⟩, rfl⟩

/-- A run of the game with its counter under `f` gives a result of the experiment. -/
theorem mem_support_adversaryExperiment (adversary : Adversary) (r : (Bool × Nat × Nat) × Nat)
    (hr : r ∈ support (countedRun f (adversaryGameCore adversary))) :
    r.1 ∈ support (adversaryExperiment adversary) := by
  rw [countedRun.eq_1] at hr
  rw [adversaryExperiment_eq]
  exact mem_support_run'_of_withAddCost _ r
    ((mem_support_counted_iff (adversaryGameCore adversary) hashCost hashCost_eq r).2 ⟨f, hr⟩)

omit f in
/-- The probability of a forgery is the same in the game with the adversary's counter. -/
theorem forgeAdvantage_eq (adversary : Adversary) :
    forgeAdvantage adversary =
      Pr{let result ← adversaryExperiment adversary}[result.1 = true] := by
  have hE : forgeAdvantage adversary =
      Pr{let result ←
        (simulateQ HashSpec.romImpl (gameCore adversary)).run' ∅}[result = true] := by
    rw [forgeAdvantage, experiment_eq]
    exact HashSig.prEvent_run_withAddCost (gameCore adversary) hashCost
  rw [hE, gameCore_eq_map, simulateQ_map, adversaryExperiment_eq]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]

omit f in
/-- A budget of `q` calls of the adversary's own and `r` requests is one of `q + C` calls in all.

`C` bounds the calls of key generation, of `r` requests and of verification. -/
theorem hasHashQueryBound_of_adversary (adversary : Adversary) (q r : Nat)
    (hq : HasAdversaryQueryBound adversary q r) :
    HasHashQueryBound adversary (q + schemeCalls r) := by
  intro result hr
  obtain ⟨f, hr⟩ := exists_countedRun_of_mem_support _ _ (experiment_eq adversary) result hr
  rw [gameCore_eq_map] at hr
  obtain ⟨run, hrun, rfl⟩ := mem_support_countedRun_map f _ _ result hr
  have hcalls := calls_adversaryGameCore f adversary run hrun
  obtain ⟨hq₁, hq₂⟩ := hq run.1 (mem_support_adversaryExperiment f adversary run hrun)
  have hmul := Nat.mul_le_mul_right signCalls hq₂
  unfold schemeCalls
  dsimp only
  omega

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
