module

public import EthLib.Cryptography.Proofs.Sponge.Fresh

/-!
# Proofs: the simulator over path values is the simulator of the sponge

The simulator over path values takes the value of a new rooted state from the oracle on paths.

The simulator draws it uniformly, and the oracle on paths is asked at most once per path.

So the two have one law once the answers of the oracle on paths are forgotten.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation Indifferentiability

/-! ## Projections in distribution -/

section Projection

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}

/-- **State projection in law**: steps that project from invariant states make runs project. -/
theorem map_run_simulateQ_evalDistEq_of_inv
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl₁ t).run s), inv z.2)
    (hproj : ∀ t s, inv s → Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =ᵈ (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    calc ((impl₁ t).run s >>= fun z => Prod.map id proj <$> (simulateQ impl₁ (k z.1)).run z.2)
        =ᵈ ((impl₁ t).run s >>= fun z => (simulateQ impl₂ (k z.1)).run (proj z.2)) :=
          EvalDistEq.bind_congr_of_support _ fun z hz => ih z.1 z.2 (hinv t s hs z hz)
      _ = ((Prod.map id proj <$> (impl₁ t).run s) >>= fun z =>
            (simulateQ impl₂ (k z.1)).run z.2) := by
          rw [bind_map_left]
          rfl
      _ =ᵈ ((impl₂ t).run (proj s) >>= fun z => (simulateQ impl₂ (k z.1)).run z.2) :=
          EvalDistEq.bind_left (hproj t s hs) _

/-- The outputs of two runs related by a projection in distribution have one law. -/
theorem run'_simulateQ_evalDistEq_of_inv
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl₁ t).run s), inv z.2)
    (hproj : ∀ t s, inv s → Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s) :
    (simulateQ impl₁ oa).run' s =ᵈ (simulateQ impl₂ oa).run' (proj s) := by
  have h := (map_run_simulateQ_evalDistEq_of_inv impl₁ impl₂ inv proj hinv hproj oa s hs).map
    Prod.fst
  simpa [StateT.run'_eq, Functor.map_map, Function.comp_def] using h

end Projection

/-! ## The hash part of a cache -/

section RoPart

variable {Msg Dg τ : Type} {O : OracleSpec.{0, 0} τ}

/-- The hash part of a cache of the hash and another oracle `O`. -/
def roPart (c : ((Msg →ₒ Dg) + O).QueryCache) : (Msg →ₒ Dg).QueryCache :=
  QueryCache.ofFn fun m => c (.inl m)

@[simp] theorem roPart_apply (c : ((Msg →ₒ Dg) + O).QueryCache) (m : Msg) :
    roPart c m = c (.inl m) := rfl

variable [DecidableEq Msg] [DecidableEq τ]

/-- Caching a hash answer commutes with forgetting `O`. -/
theorem roPart_cacheQuery_inl (c : ((Msg →ₒ Dg) + O).QueryCache) (m : Msg) (d : Dg) :
    roPart (c.cacheQuery (.inl m) d) = (roPart c).cacheQuery m d := by
  refine QueryCache.ext fun m' => ?_
  by_cases h : m' = m
  · subst h
    simp
  · rw [roPart_apply, QueryCache.cacheQuery_of_ne _ _ (by simpa using h),
      QueryCache.cacheQuery_of_ne _ _ h, roPart_apply]

/-- Caching an answer of `O` leaves the hash part alone. -/
theorem roPart_cacheQuery_inr (c : ((Msg →ₒ Dg) + O).QueryCache) (x : τ) (t : O.Range x) :
    roPart (c.cacheQuery (.inr x) t) = roPart c := by
  refine QueryCache.ext fun m' => ?_
  rw [roPart_apply, QueryCache.cacheQuery_of_ne _ _ (by simp), roPart_apply]

variable [SampleableType Dg] [∀ t, SampleableType (O.Range t)]

/-- A hash query, seen through the hash part. -/
theorem roPart_randomOracle_inl (m : Msg) (c : ((Msg →ₒ Dg) + O).QueryCache) :
    (fun w => (w.1, roPart w.2)) <$> (((Msg →ₒ Dg) + O).randomOracle (.inl m)).run c =
      ((Msg →ₒ Dg).randomOracle m).run (roPart c) := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  rcases h : c (.inl m) with _ | d
  · simp [h, roPart_cacheQuery_inl]
  · simp [h]

end RoPart

/-! ## One step of each simulator -/

section Setting

variable {Dg E C Msg : Type} [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-- The rest of the rate and the capacity of a uniform state are uniform. -/
theorem uniform_rest_evalDistEq {β : Type} (f : E × C → ProbComp β) :
    (($ᵗ (SpongeState Dg E C)) >>= fun t => f (t.1.2, t.2)) =ᵈ (($ᵗ (E × C)) >>= f) := by
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind,
    SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  exact EvalDistEq.bind_const _ _

/-- The simulator's answer at a path that pads a message. -/
theorem rootedAnswer_run_some {β : List (Dg × E)} {m : Msg} (hm : P.unpad β = some m)
    (c : (Msg →ₒ Dg).QueryCache) :
    (simulateQ (Msg →ₒ Dg).romImpl (rootedAnswer (C := C) P β)).run c =
      (((Msg →ₒ Dg).randomOracle m).run c >>= fun w =>
        ($ᵗ (E × C)) >>= fun ec => pure (((w.1, ec.1), ec.2), w.2)) := by
  simp [rootedAnswer, hm, simulateQ_romImpl_liftM_run]

/-- The simulator's answer at a path that pads no message. -/
theorem rootedAnswer_run_none {β : List (Dg × E)} (hm : P.unpad β = none)
    (c : (Msg →ₒ Dg).QueryCache) :
    (simulateQ (Msg →ₒ Dg).romImpl (rootedAnswer (C := C) P β)).run c =
      (fun y => (y, c)) <$> ($ᵗ (SpongeState Dg E C)) := by
  simp only [rootedAnswer, hm]
  exact simulateQ_romImpl_liftM_run _ _

variable [XorOp Dg] [XorOp E] [DecidableEq Dg] [DecidableEq E] [DecidableEq C]

/-- A coin of the ideal world. -/
theorem ideal_coin_run (n : ℕ) (σ : SimState Dg E C) (c : (Msg →ₒ Dg).QueryCache) :
    (simulateQ (Msg →ₒ Dg).romImpl
      ((idealImpl (simulator (C := C) P) (.inl (.inl n))).run σ)).run c =
      (fun u => ((u, σ), c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp [idealImpl, unifFwdImpl]

/-- A hash query of the ideal world. -/
theorem ideal_hash_run (m : Msg) (σ : SimState Dg E C) (c : (Msg →ₒ Dg).QueryCache) :
    (simulateQ (Msg →ₒ Dg).romImpl ((idealImpl (simulator (C := C) P) (.inr m)).run σ)).run c =
      (fun w => ((w.1, σ), w.2)) <$> ((Msg →ₒ Dg).randomOracle m).run c := by
  simp [idealImpl]

omit [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- The value of a path that pads a message, at a path the oracle on paths has not answered. -/
theorem val_run_fresh_some {β : List (Dg × E)} {m : Msg} (hm : P.unpad β = some m)
    (c : ACache Msg Dg E C) (hβ : c (.inr β) = none) :
    (simulateQ (ASpec Msg Dg E C).romImpl (val P β)).run c =
      (((ASpec Msg Dg E C).randomOracle (.inl m)).run c >>= fun w =>
        ($ᵗ (SpongeState Dg E C)) >>= fun t =>
          pure (((w.1, t.1.2), t.2), w.2.cacheQuery (.inr β) t)) := by
  simp only [val, hm, simulateQ_bind, StateT.run_bind, run_hq, simulateQ_pure, StateT.run_pure]
  refine bind_congr_of_forall_mem_support _ fun w hw => ?_
  have hwβ : w.2 (.inr β) = none := by
    rw [(randomOracle_run_support _ c hw).2.2 _ (by simp)]
    exact hβ
  rw [randomOracle.run_eq]
  simp [hwβ]

omit [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- The value of a path that pads no message, at a path the oracle on paths has not answered. -/
theorem val_run_fresh_none {β : List (Dg × E)} (hm : P.unpad β = none)
    (c : ACache Msg Dg E C) (hβ : c (.inr β) = none) :
    (simulateQ (ASpec Msg Dg E C).romImpl (val P β)).run c =
      (($ᵗ (SpongeState Dg E C)) >>= fun t => pure (t, c.cacheQuery (.inr β) t)) := by
  simp only [val, hm, run_hq]
  rw [randomOracle.run_eq]
  simp [hβ]

/-- The state of the simulator over path values, with the oracle on paths forgotten. -/
def projT (s : SimState Dg E C × ACache Msg Dg E C) :
    SimState Dg E C × (Msg →ₒ Dg).QueryCache := (s.1, roPart s.2)

/-- The simulator over path values, with its random oracles folded into the state. -/
noncomputable abbrev foldIdealT :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (SimState Dg E C × ACache Msg Dg E C) ProbComp) :=
  ((ASpec Msg Dg E C).romImpl.mapStateTBase (idealTImpl P)).flattenStateT

/-- The ideal world, with its random oracle folded into the state. -/
noncomputable abbrev foldSim :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (SimState Dg E C × (Msg →ₒ Dg).QueryCache) ProbComp) :=
  ((Msg →ₒ Dg).romImpl.mapStateTBase (idealImpl (simulator (C := C) P))).flattenStateT

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- **One step of the simulator over path values is one step of the simulator**, in law.

The answers of the oracle on paths are forgotten. -/
theorem idealT_step_evalDistEq (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (σ : SimState Dg E C) (c : ACache Msg Dg E C) (hV : VStruct P iv σ c) :
    Prod.map id projT <$> (foldIdealT P t).run (σ, c) =ᵈ (foldSim P t).run (projT (σ, c)) := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run,
    QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rcases t with (n | x | y) | m
  · rw [idealT_coin_run, ideal_coin_run]
    simp [projT, Functor.map_map]
  · rw [idealT_fwd_run]
    change _ =ᵈ (fun y => (y.1.1, y.1.2, y.2)) <$> (simulateQ (Msg →ₒ Dg).romImpl
      ((simulator P (.inl x)).run σ)).run (roPart c)
    simp only [simulator, StateT.run_mk]
    rcases hy : σ.edges.lookup x with _ | y
    · rcases hch : chainOf σ.chains x with _ | ⟨s, β⟩
      · -- A new state that is not rooted.
        simp only [visFwd, hy, hch]
        simp [simulateQ_romImpl_liftM_run, Functor.map_map, projT]
      · -- A new rooted state: the oracle on paths has not answered at its path.
        have hfresh : c (.inr (β ++ [blockTo s x])) = none := by
          by_contra h
          exact rootedPath_notMem hV hy hch (hV.tFresh _ h)
        simp only [visFwd, hy, hch, simulateQ_bind, StateT.run_bind, simulateQ_pure,
          StateT.run_pure]
        rcases hm : P.unpad (β ++ [blockTo s x]) with _ | m
        · rw [val_run_fresh_none P hm c hfresh, rootedAnswer_run_none P hm]
          simp only [bind_assoc, pure_bind, map_bind, map_pure, bind_map_left]
          refine (EvalDistEq.bind_const _ _).trans ?_
          simp [roPart_cacheQuery_inr, projT]
        · rw [val_run_fresh_some P hm c hfresh, rootedAnswer_run_some P hm,
            ← roPart_randomOracle_inl]
          simp only [bind_assoc, pure_bind, map_bind, map_pure, bind_map_left]
          refine (EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_right _ fun w => ?_)
          simp only [Prod.map_apply, id_eq, projT, roPart_cacheQuery_inr]
          -- The digest is the hash, and the rest of the value is uniform on both sides.
          exact uniform_rest_evalDistEq fun ec => pure ((((w.1, ec.1), ec.2),
            (⟨(x, ((w.1, ec.1), ec.2)) :: σ.edges,
              (((w.1, ec.1), ec.2), β ++ [blockTo s x]) :: σ.chains⟩ : SimState Dg E C),
            roPart w.2))
    · -- A recorded state.
      simp only [visFwd, hy, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
      exact EvalDistEq.bind_const _ _
  · rw [idealT_inv_run]
    change _ =ᵈ (fun y => (y.1.1, y.1.2, y.2)) <$> (simulateQ (Msg →ₒ Dg).romImpl
      ((simulator P (.inr y)).run σ)).run (roPart c)
    simp only [simulator, StateT.run_mk, visInv]
    rcases hx : (σ.edges.map Prod.swap).lookup y with _ | x
    · simp [simulateQ_romImpl_liftM_run, Functor.map_map, projT]
    · simp only [simulateQ_pure, StateT.run_pure, Functor.map_map]
      exact EvalDistEq.map_const _ _
  · rw [idealT_hash_run, ideal_hash_run, projT, ← roPart_randomOracle_inl]
    simp [projT, Functor.map_map]

/-- **The simulator over path values is the simulator**, on a whole run, in law. -/
theorem idealT_run_evalDistEq {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) :
    (simulateQ (foldIdealT P) oa).run' (SimState.init iv, ∅) =ᵈ
      (simulateQ (foldSim P) oa).run' (SimState.init iv, ∅) := by
  have h := run'_simulateQ_evalDistEq_of_inv (foldIdealT P) (foldSim P)
    (fun s => VStruct P iv s.1 s.2) projT
    (fun t s hs z hz => by
      rw [QueryImpl.flattenStateT_mapStateTBase_apply_run] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact vStruct_idealT t hs hw)
    (fun t s hs => idealT_step_evalDistEq P iv t s.1 s.2 hs) oa (SimState.init iv, ∅)
    vStruct_init
  have h0 : projT ((SimState.init iv : SimState Dg E C), (∅ : ACache Msg Dg E C)) =
      (SimState.init iv, ∅) := by
    simp only [projT, Prod.mk.injEq, true_and]
    exact QueryCache.ext fun m => rfl
  rwa [h0] at h

/-- **The simulator over path values is the ideal world.**

Run in the random-oracle model from no answer, both give each output with one chance. -/
theorem idealTGame_evalDistEq_idealGame {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) :
    (simulateQ (ASpec Msg Dg E C).romImpl
      ((simulateQ (idealTImpl P) oa).run' (SimState.init iv))).run' ∅ =ᵈ
      (simulateQ (Msg →ₒ Dg).romImpl
        ((simulateQ (idealImpl (simulator P)) oa).run' (SimState.init iv))).run' ∅ := by
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [StateT.run'_eq] using idealT_run_evalDistEq P iv oa

end Setting

end EthLib.Cryptography.Sponge
