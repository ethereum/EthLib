module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Proofs: random oracles beside uniform coins

A query of a random oracle caches its answer and changes no other entry of the cache.

Two computations that do not read each other's answers commute, in law, with their cache.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleComp OracleSpec

variable {ι : Type} {hs : OracleSpec.{0, 0} ι}

/-- A query of the oracles `hs`, beside the uniform coins. -/
abbrev queryRight (t : ι) : OracleComp (unifSpec + hs) (hs.Range t) :=
  (unifSpec + hs).query (.inr t)

/-- An output reachable in the random-oracle model is a possible output of the computation. -/
theorem fst_mem_support_of_mem_support_run_romImpl [DecidableEq ι]
    [∀ t : hs.Domain, SampleableType (hs.Range t)] {β : Type}
    {X : OracleComp (unifSpec + hs) β} {c : hs.QueryCache} {z : β × hs.QueryCache}
    (hz : z ∈ support ((simulateQ hs.romImpl X).run c)) : z.1 ∈ support X :=
  support_simulateQ_run'_subset hs.romImpl X c (by
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩)

/-! ## The part of a cache for the left oracle -/

section LeftCache

variable {τ D R : Type} {O : OracleSpec.{0, 0} τ} [DecidableEq D] [DecidableEq τ]

/-- Caching an answer of the left oracle commutes with forgetting `O`. -/
theorem QueryCache.fst_cacheQuery_inl (c : ((D →ₒ R) + O).QueryCache) (m : D) (d : R) :
    (c.cacheQuery (.inl m) d).fst = c.fst.cacheQuery m d := by
  refine QueryCache.ext fun m' => ?_
  by_cases h : m' = m
  · subst h
    simp
  · rw [QueryCache.fst_apply, QueryCache.cacheQuery_of_ne _ _ (by simpa using h),
      QueryCache.cacheQuery_of_ne _ _ h, QueryCache.fst_apply]

/-- Caching an answer of `O` leaves the part of the left oracle alone. -/
theorem QueryCache.fst_cacheQuery_inr (c : ((D →ₒ R) + O).QueryCache) (x : τ) (t : O.Range x) :
    (c.cacheQuery (.inr x) t).fst = c.fst := by
  refine QueryCache.ext fun m' => ?_
  rw [QueryCache.fst_apply, QueryCache.cacheQuery_of_ne _ _ (by simp), QueryCache.fst_apply]

variable [SampleableType R] [∀ t, SampleableType (O.Range t)]

/-- A query of the left oracle, seen through the part of its cache. -/
theorem fst_randomOracle_inl (m : D) (c : ((D →ₒ R) + O).QueryCache) :
    (fun w => (w.1, w.2.fst)) <$> (((D →ₒ R) + O).randomOracle (.inl m)).run c =
      ((D →ₒ R).randomOracle m).run c.fst := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  rcases h : c (.inl m) with _ | d
  · simp [h, QueryCache.fst_cacheQuery_inl]
  · simp [h]

end LeftCache

variable [DecidableEq ι] [∀ t : hs.Domain, SampleableType (hs.Range t)]

/-! ## One query -/

/-- A query of `hs`, in the random-oracle model, is one query of the random oracle. -/
theorem run_queryRight (t : ι) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (queryRight t)).run c = (hs.randomOracle t).run c := by
  simp [queryRight]

/-- A query of a random oracle keeps the cache, caches its answer and changes no other entry. -/
theorem caches_of_mem_support_randomOracle_run (t : ι) (c : hs.QueryCache)
    {z : hs.Range t × hs.QueryCache} (hz : z ∈ support ((hs.randomOracle t).run c)) :
    c ≤ z.2 ∧ z.2 t = some z.1 ∧ ∀ t', t' ≠ t → z.2 t' = c t' :=
  ⟨QueryImpl.withCaching_cache_le _ t c z hz, QueryImpl.withCaching_run_caches _ t c z hz,
    fun _ ht' => by
      rw [QueryImpl.withCaching_run_eq_cacheQuery _ hz]
      exact QueryCache.cacheQuery_of_ne _ _ ht'⟩

/-! ## Commuting computations -/

/-- Any two steps of the random-oracle model commute: answers and cache keep their joint law.

Each step is a coin draw or a query, so it is the general form of the swap of two queries. -/
theorem romImpl_run_bind_comm (q q' : (unifSpec + hs).Domain) (c : hs.QueryCache) {β : Type}
    (f : (unifSpec + hs).Range q → (unifSpec + hs).Range q' → hs.QueryCache → ProbComp β) :
    ((hs.romImpl q).run c >>= fun v => (hs.romImpl q').run v.2 >>= fun w => f v.1 w.1 w.2) =ᵈ
      ((hs.romImpl q').run c >>= fun w => (hs.romImpl q).run w.2 >>= fun v => f v.1 w.1 v.2) := by
  rcases q with n | s <;> rcases q' with n' | t
  · simp only [roSim.run_apply_inl, bind_map_left]
    exact EvalDistEq.bind_bind_swap _ _ _
  · simp only [roSim.run_apply_inl, bind_map_left, romImpl_apply_inr]
    exact EvalDistEq.bind_bind_swap _ _ _
  · simp only [roSim.run_apply_inl, bind_map_left, romImpl_apply_inr]
    exact EvalDistEq.bind_bind_swap _ _ _
  · simp only [romImpl_apply_inr]
    let : MeasurableSpace β := ⊤
    have : DiscreteMeasurableSpace β := ⟨fun _ => trivial⟩
    exact EvalDistEq.of_evalDist_eq (randomOracle.evalDist_run_bind_run_swap s t c f)

/-- One query commutes, in law, with a computation that does not read its answer. -/
theorem run_query_bind_comm (q : (unifSpec + hs).Domain) {γ δ : Type}
    (Y : OracleComp (unifSpec + hs) γ)
    (V : (unifSpec + hs).Range q → γ → OracleComp (unifSpec + hs) δ) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (liftM ((unifSpec + hs).query q) >>= fun a =>
        Y >>= fun r => V a r)).run c =ᵈ
      (simulateQ hs.romImpl (Y >>= fun r =>
        liftM ((unifSpec + hs).query q) >>= fun a => V a r)).run c := by
  induction Y using OracleComp.inductionOn generalizing c with
  | pure r => simp
  | query_bind q' k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc] at ih ⊢
    refine (romImpl_run_bind_comm q q' c fun a a' c' =>
      (simulateQ hs.romImpl (k a')).run c' >>= fun p =>
        (simulateQ hs.romImpl (V a p.1)).run p.2).trans
      (EvalDistEq.bind_right _ fun w => ?_)
    exact ih w.1 w.2

/-- **Independent computations commute** in the random-oracle model.

Running `X` then `Y` gives the joint law of outputs and cache of running `Y` then `X`.

Both may draw coins and query, so it is the general form of commuting hash computations.
-/
theorem run_bind_bind_comm {β γ δ : Type} (X : OracleComp (unifSpec + hs) β)
    (Y : OracleComp (unifSpec + hs) γ) (W : β → γ → OracleComp (unifSpec + hs) δ)
    (c : hs.QueryCache) :
    (simulateQ hs.romImpl (X >>= fun b => Y >>= fun r => W b r)).run c =ᵈ
      (simulateQ hs.romImpl (Y >>= fun r => X >>= fun b => W b r)).run c := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure b => simp
  | query_bind q k ih =>
    calc (simulateQ hs.romImpl ((liftM ((unifSpec + hs).query q) >>= k) >>= fun b =>
          Y >>= fun r => W b r)).run c
        = (simulateQ hs.romImpl (liftM ((unifSpec + hs).query q) >>= fun a =>
            k a >>= fun b => Y >>= fun r => W b r)).run c := by rw [bind_assoc]
      _ =ᵈ (simulateQ hs.romImpl (liftM ((unifSpec + hs).query q) >>= fun a =>
            Y >>= fun r => k a >>= fun b => W b r)).run c := by
          simp only [simulateQ_bind, StateT.run_bind]
          exact EvalDistEq.bind_right _ fun w => by
            have := ih w.1 w.2
            simp only [simulateQ_bind, StateT.run_bind] at this
            exact this
      _ =ᵈ (simulateQ hs.romImpl (Y >>= fun r => liftM ((unifSpec + hs).query q) >>= fun a =>
            k a >>= fun b => W b r)).run c :=
          run_query_bind_comm q Y (fun a r => k a >>= fun b => W b r) c
      _ = _ := by simp only [bind_assoc]

end EthLib.Cryptography
