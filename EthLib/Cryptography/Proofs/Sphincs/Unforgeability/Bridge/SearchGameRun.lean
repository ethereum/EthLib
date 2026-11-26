module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.SearchBudget

/-!
# Proofs: the adversary's run and the wrapped run agree until a long search

Both runs answer the adversary's queries with the same oracles from the same cache.

Until a signing answer has a long search, they make the same queries and get the same answers.

So the adversary's run, cut off at its first long answer, is at most the wrapped run.

This holds in expectation, for every nonnegative function of the final state.

A long answer leaves a failed search in the cache, and the cache only grows afterwards.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic
open scoped OracleComp.Lower
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld)

variable (T : Nat) (s : QueryImpl SigningSpec (OracleComp OracleWorld))

/-- The game's oracles answer a coin or hash query of the adversary by that query. -/
theorem run_simulateQ_game_inl {α : Type} (t : OracleWorld.Domain)
    (k : OracleWorld.Range t → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + QueryImpl.withLogging s)
      (liftM ((OracleWorld + SigningSpec).query (.inl t)) >>= k)).run =
    liftM (OracleWorld.query t) >>= fun u =>
      (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + QueryImpl.withLogging s)
        (k u)).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.add_apply_inl,
    QueryImpl.ofLift_apply]
  have hl : (liftM (OracleWorld.query t) :
      WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run =
        (fun u => (u, ∅)) <$> liftM (OracleWorld.query t) := rfl
  rw [hl, bind_map_left]
  simp

/-- The game's oracles answer a signing request by the signer, and log it first. -/
theorem run_simulateQ_game_inr {α : Type} (msg : Message)
    (k : Option Signature → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + QueryImpl.withLogging s)
      (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= k)).run =
    s msg >>= fun a =>
      (fun z => (z.1, ⟨msg, a⟩ :: z.2)) <$>
      (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + QueryImpl.withLogging s)
        (k a)).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.add_apply_inr,
    QueryImpl.withLogging_apply, WriterT.run_tell, bind_assoc]
  have hl : (liftM (s msg) : WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run =
      (fun u => (u, ∅)) <$> s msg := rfl
  rw [hl, bind_map_left]
  simp

/-- Before the flag, the wrapper forwards a coin or hash query and keeps the flag down. -/
theorem run_simulateQ_capImpl_inl {α : Type} (t : OracleWorld.Domain)
    (k : OracleWorld.Range t → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (capImpl T) (liftM ((OracleWorld + SigningSpec).query (.inl t)) >>= k)).run
        false =
      liftM ((OracleWorld + SigningSpec).query (.inl t)) >>= fun u =>
        (simulateQ (capImpl T) (k u)).run false := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rcases t with n | x <;> simp [capImpl, StateT.run]

/-- Before the flag, the wrapper forwards a signing request and raises the flag on a long answer. -/
theorem run_simulateQ_capImpl_inr {α : Type} (msg : Message)
    (k : Option Signature → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (capImpl T) (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= k)).run
        false =
      liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= fun a =>
        (simulateQ (capImpl T) (k a)).run (!decide (SearchesBelow T a)) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp [capImpl, StateT.run]

/-- The adversary's run, counted only while its answers search short, is at most the wrapped run. -/
theorem wp_cut_le_wp_capImpl {α : Type} (oa : OracleComp (OracleWorld + SigningSpec) α)
    (cache : HashSpec.QueryCache) (h : (α × QueryLog SigningSpec) × HashSpec.QueryCache → ℝ≥0∞) :
    wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + QueryImpl.withLogging s)
        oa).run).run cache)
      (fun z => if ∀ e ∈ z.1.2, SearchesBelow T e.2 then h z else 0) ≤
    wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + QueryImpl.withLogging s)
        ((simulateQ (capImpl T) oa).run false)).run).run cache)
      (fun z => h ((z.1.1.1, z.1.2), z.2)) := by
  induction oa using OracleComp.inductionOn generalizing cache h with
  | pure x =>
    simp
  | query_bind t k ih =>
    rcases t with t | msg
    · rw [run_simulateQ_capImpl_inl, run_simulateQ_game_inl, run_simulateQ_game_inl,
        simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, wp_bind, wp_bind]
      exact wp_mono _ fun w => ih w.1 w.2 h
    · rw [run_simulateQ_capImpl_inr, run_simulateQ_game_inr, run_simulateQ_game_inr,
        simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, wp_bind, wp_bind]
      refine wp_mono _ fun w => ?_
      simp only [simulateQ_map, StateT.run_map, wp_map]
      by_cases hs : SearchesBelow T w.1
      · simpa only [Function.comp_def, List.forall_mem_cons, hs, true_and, decide_true,
          Bool.not_true] using ih w.1 w.2 (fun z => h ((z.1.1, ⟨msg, w.1⟩ :: z.1.2), z.2))
      · simp only [Function.comp_def, List.forall_mem_cons, hs, false_and, ite_false]
        simp

/-- A long answer in the adversary's run leaves a failed search of `T` trials in its final cache. -/
theorem failedSearch_of_mem_support_run (hT : T ≤ MAX_COUNTER_TRIALS) (sk : SecretKey) {α : Type}
    (oa : OracleComp (OracleWorld + SigningSpec) α) (cache : HashSpec.QueryCache)
    (z : (α × QueryLog SigningSpec) × HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          QueryImpl.withLogging (fun msg => liftM (signerOf sk msg) :
            QueryImpl SigningSpec (OracleComp OracleWorld))) oa).run).run cache))
    (hbad : ¬∀ e ∈ z.1.2, SearchesBelow T e.2) :
    HashSig.FailedSearch searchPoint SearchMiss T z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache z with
  | pure x =>
    simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    simp at hbad
  | query_bind t k ih =>
    rcases t with t | msg
    · rw [run_simulateQ_game_inl, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨w, -, hz⟩ := hz
      exact ih w.1 w.2 z hz hbad
    · rw [run_simulateQ_game_inr, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      simp only [simulateQ_map, StateT.run_map, support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      simp only [List.forall_mem_cons, not_and_or] at hbad
      rcases hbad with hb | hb
      · exact (failedSearch_of_signerOf T hT sk msg cache w hw hb).mono _ _ _
          (HashSig.le_snd_of_mem_support_run_romImpl (z := z') _ hz')
      · exact ih w.1 w.2 z' hz' hb

/-- The game is key generation, then the adversary's run with its oracles, then the verdict. -/
theorem game_eq_keys_run (adversary : Adversary) :
    SufCma.game scheme adversary = (do
      let keys : SecretKey × PublicKey ← (do
        let seed ← liftM sampleSeed
        liftM (keyGenWith H seed) : OracleComp OracleWorld (SecretKey × PublicKey))
      let run : SufCma.Forgery Message Signature × QueryLog SigningSpec ←
        (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
            QueryImpl.withLogging (fun msg => liftM (signerOf keys.1 msg) :
              QueryImpl SigningSpec (OracleComp OracleWorld))) (adversary.main keys.2)).run
      let verified ← liftM (verifierOf keys.2 run.1)
      pure (verdictOf run.1 run.2 verified)) := by
  rw [game_eq]
  unfold signingOracle signer signerOf verifierOf verdictOf
  rw [bind_assoc]

/-- In the random-oracle model, an expectation over the game is one over its three stages. -/
theorem wp_run_game (adversary : Adversary) (E : Bool × HashSpec.QueryCache → ℝ≥0∞) :
    wp ((simulateQ HashSpec.romImpl (SufCma.game scheme adversary)).run ∅) E =
      wp ((simulateQ HashSpec.romImpl (do
        let seed ← liftM sampleSeed
        liftM (keyGenWith H seed) : OracleComp OracleWorld (SecretKey × PublicKey))).run ∅)
        fun w => wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
            QueryImpl.withLogging (fun msg => liftM (signerOf w.1.1 msg) :
              QueryImpl SigningSpec (OracleComp OracleWorld))) (adversary.main w.1.2)).run).run
          w.2)
        fun v => wp ((simulateQ HashSpec.romImpl (liftM (verifierOf w.1.2 v.1.1) >>=
          fun verified => pure (verdictOf v.1.1 v.1.2 verified) :
            OracleComp OracleWorld Bool)).run v.2) E := by
  rw [game_eq_keys_run]
  simp only [simulateQ_bind, StateT.run_bind, wp_bind]

/-- From the same keys, the adversary wins at most as often as the wrapped one or a search fails. -/
theorem wp_run_le_wp_capSearches (hT : T ≤ MAX_COUNTER_TRIALS) (adversary : Adversary)
    (sk : SecretKey) (pk : PublicKey) (cache : HashSpec.QueryCache)
    (P : SufCma.Forgery Message Signature × QueryLog SigningSpec → OracleComp OracleWorld Bool) :
    wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          QueryImpl.withLogging (fun msg => liftM (signerOf sk msg) :
            QueryImpl SigningSpec (OracleComp OracleWorld))) (adversary.main pk)).run).run cache)
      (fun v => wp ((simulateQ HashSpec.romImpl (P v.1)).run v.2)
        fun x => propInd (x.1 = true)) ≤
    wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          QueryImpl.withLogging (fun msg => liftM (signerOf sk msg) :
            QueryImpl SigningSpec (OracleComp OracleWorld)))
          ((capSearches T adversary).main pk)).run).run cache)
      (fun v => wp ((simulateQ HashSpec.romImpl (P v.1)).run v.2)
        fun x => propInd (x.1 = true)) +
    wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          QueryImpl.withLogging (fun msg => liftM (signerOf sk msg) :
            QueryImpl SigningSpec (OracleComp OracleWorld))) (adversary.main pk)).run).run cache)
      (fun v => wp ((simulateQ HashSpec.romImpl (P v.1)).run v.2)
        fun x => propInd (HashSig.FailedSearch searchPoint SearchMiss T x.2)) := by
  -- The wrapped run is the run of the wrapper's handler, its flag forgotten.
  have hcap := wp_cut_le_wp_capImpl T (fun msg => liftM (signerOf sk msg)) (adversary.main pk)
    cache (fun v => wp ((simulateQ HashSpec.romImpl (P v.1)).run v.2)
      fun x => propInd (x.1 = true))
  have heq : ∀ (f : (SufCma.Forgery Message Signature × QueryLog SigningSpec) ×
      HashSpec.QueryCache → ℝ≥0∞),
      wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          QueryImpl.withLogging (fun msg => liftM (signerOf sk msg) :
            QueryImpl SigningSpec (OracleComp OracleWorld)))
          ((capSearches T adversary).main pk)).run).run cache) f =
      wp ((simulateQ HashSpec.romImpl (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          QueryImpl.withLogging (fun msg => liftM (signerOf sk msg) :
            QueryImpl SigningSpec (OracleComp OracleWorld)))
          ((simulateQ (capImpl T) (adversary.main pk)).run false)).run).run cache)
        (fun z => f ((z.1.1.1, z.1.2), z.2)) := fun f => by
    simp only [capSearches, StateT.run'_eq, simulateQ_map, WriterT.run_map, StateT.run_map,
      wp_map]
    rfl
  rw [heq]
  refine le_trans ?_ (add_le_add hcap le_rfl)
  rw [← ExpectationWP.Lower.wp_add_of_oracle]
  refine ExpectationWP.Lower.wp_mono_of_support _ fun v hv => ?_
  by_cases hg : ∀ e ∈ v.1.2, SearchesBelow T e.2
  · rw [ite_eq_left hg]
    exact le_self_add
  · -- A long answer leaves a failed search, which the check keeps in the cache.
    rw [ite_eq_right hg, zero_add]
    have hfs := failedSearch_of_mem_support_run T hT sk _ cache v hv hg
    calc _ ≤ (1 : ℝ≥0∞) :=
          ExpectationWP.Lower.wp_le_const_of_support _ fun x _ => propInd_le_one _
      _ = wp ((simulateQ HashSpec.romImpl (P v.1)).run v.2) (fun _ => 1) :=
          (ExpectationWP.Lower.wp_const_of_oracle _ _).symm
      _ ≤ _ := ExpectationWP.Lower.wp_mono_of_support _ fun x hx =>
          (propInd_eq_one_iff.2 (hfs.mono _ _ _
            (HashSig.le_snd_of_mem_support_run_romImpl _ hx))).ge

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
