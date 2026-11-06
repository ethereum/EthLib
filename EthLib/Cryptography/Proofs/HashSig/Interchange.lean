module

public import EthLib.Cryptography.Proofs.HashSig.Commute
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proofs: hash computations that agree on every answer function are interchangeable

A game here draws uniform coins and queries a hash that is a lazily sampled random oracle.

Take two hash computations that return the same value for every fixed answer function.

They may query different inputs, in different orders.

Inside any game, either one can replace the other, and the game's output keeps its distribution.

The proof runs both computations, one after the other.

Both outputs agree, since one answer function is consistent with the joint run.

Then each computation can move past the rest of the game and be dropped.

Some hash computations agree only on the answer functions that keep a few answers already fixed.

A signer that derives its key again from a seed is one example.

It agrees with a signer that reads the derived key once the cache holds the derivation's answers.

Such computations can replace each other inside a game, from any cache that holds those answers.

A relation packages this fact, for a set of known answers.

It is closed under binds, under hash queries that add answers, and under logged adversary runs.

With no known answer, it is interchangeability from every cache.

The last section moves an adversary's requests to another oracle, with its log translated.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleComp OracleSpec MeasureTheory

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- A query to the lazy random oracle commutes with a computation that also draws coins.

The answer, the output and the final cache have the same joint distribution in either order. -/
theorem evalDist_run_bind_romImpl_swap {β γ : Type} [MeasurableSpace γ] (t : ι₀)
    (ob : OracleComp (unifSpec + spec₀) β) (cache : spec₀.QueryCache)
    (f : spec₀.Range t → β → spec₀.QueryCache → ProbComp γ) :
    𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦
        (simulateQ (OracleSpec.romImpl spec₀) ob).run z.2 >>= fun w ↦ f z.1 w.1 w.2] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) ob).run cache >>= fun w ↦
        (spec₀.randomOracle t).run w.2 >>= fun z ↦ f z.1 w.1 z.2] := by
  induction ob using OracleComp.inductionOn generalizing cache with
  | pure b => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t' k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases t' with n | t'
    · simp only [roSim.run_apply_inl, bind_map_left]
      rw [OracleComp.evalDist_bind_bind_swap]
      exact evalDist_bind_congr_of_support _ _ _ fun u _ ↦ ih u cache
    · rw [romImpl_apply_inr]
      refine (randomOracle.evalDist_run_bind_run_swap t t' cache fun u u' c ↦
        (simulateQ (OracleSpec.romImpl spec₀) (k u')).run c >>= fun w ↦ f u w.1 w.2).trans ?_
      exact evalDist_bind_congr_of_support _ _ _ fun y _ ↦ ih y.1 y.2

/-- A hash computation commutes with a computation that also draws coins.

Both outputs and the final cache have the same joint distribution in either order. -/
theorem evalDist_simulateQ_run_bind_romImpl_swap {α β γ : Type} [MeasurableSpace γ]
    (oa : OracleComp spec₀ α) (ob : OracleComp (unifSpec + spec₀) β) (cache : spec₀.QueryCache)
    (f : α → β → spec₀.QueryCache → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) ob).run w.2 >>= fun v ↦ f w.1 v.1 v.2] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) ob).run cache >>= fun v ↦
        (simulateQ spec₀.randomOracle oa).run v.2 >>= fun w ↦ f w.1 v.1 w.2] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rw [evalDist_bind_congr_of_support _ _ _ fun z _ ↦ ih z.1 z.2]
    exact evalDist_run_bind_romImpl_swap t ob cache fun u b c ↦
      (simulateQ spec₀.randomOracle (k u)).run c >>= fun w ↦ f w.1 b w.2

/-- A hash computation whose output and cache are discarded changes nothing that follows.

The later computation may draw coins. -/
theorem evalDist_simulateQ_run_bind_romImpl_discard {α β γ : Type} [MeasurableSpace γ]
    (oa : OracleComp spec₀ α) (ob : OracleComp (unifSpec + spec₀) β) (cache : spec₀.QueryCache)
    (g : β → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) ob).run w.2 >>= fun v ↦ g v.1] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) ob).run cache >>= fun v ↦ g v.1] := by
  rw [evalDist_simulateQ_run_bind_romImpl_swap oa ob cache fun _ b _ ↦ g b]
  exact evalDist_bind_congr_of_support _ _ _ fun v _ ↦
    (OracleComp.EvalDistEq.bind_const _ _).evalDist_eq

/-- A run in the random oracle model only adds entries to the cache. -/
theorem le_snd_of_mem_support_run_romImpl {α : Type} (oa : OracleComp (unifSpec + spec₀) α)
    {cache : spec₀.QueryCache} {z : α × spec₀.QueryCache}
    (hz : z ∈ support ((simulateQ (OracleSpec.romImpl spec₀) oa).run cache)) : cache ≤ z.2 :=
  le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl oa hz

omit [DecidableEq ι₀] [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] in
/-- An answer function that agrees with a cache agrees with every smaller cache. -/
theorem agreesWithFn_of_le {known cache : spec₀.QueryCache} {f : QueryImpl spec₀ Id}
    (hle : known ≤ cache) (hf : cache.AgreesWithFn f) : known.AgreesWithFn f :=
  fun _ _ h ↦ hf (hle h)

/-- Two runs in a row return the same value, from a cache that extends `known`.

The computations must agree on every answer function that agrees with `known`. -/
theorem eq_of_mem_support_run_bind_run_of_le {α : Type} {known : spec₀.QueryCache}
    (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, known.AgreesWithFn f →
      evalWithAnswerFn f oa = evalWithAnswerFn f ob)
    {cache : spec₀.QueryCache} (hle : known ≤ cache) {w : α × spec₀.QueryCache}
    {v : α × spec₀.QueryCache}
    (hw : w ∈ support ((simulateQ spec₀.randomOracle oa).run cache))
    (hv : v ∈ support ((simulateQ spec₀.randomOracle ob).run w.2)) : w.1 = v.1 := by
  have hjoint : ((w.1, v.1), v.2) ∈ support ((simulateQ spec₀.randomOracle
      (oa >>= fun a ↦ ob >>= fun b ↦ pure (a, b))).run cache) := by
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨w, hw, v, hv, rfl⟩
  obtain ⟨f, hagree, hf⟩ := (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support _ cache _).2
    ⟨_, hjoint⟩
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Prod.mk.injEq] at hf
  rw [← hf.1, ← hf.2, h f (agreesWithFn_of_le hle hagree)]

/-- Two hash computations that agree once `known` holds can replace each other.

The continuation then has the same output distribution, from every cache that extends `known`. -/
theorem evalDist_interchange_of_le {α β γ : Type} [MeasurableSpace γ]
    {known : spec₀.QueryCache} (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, known.AgreesWithFn f →
      evalWithAnswerFn f oa = evalWithAnswerFn f ob)
    (cont : α → OracleComp (unifSpec + spec₀) β) {cache : spec₀.QueryCache}
    (hle : known ≤ cache) (g : β → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont w.1)).run w.2 >>= fun v ↦ g v.1] =
      𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont w.1)).run w.2 >>= fun v ↦ g v.1] := by
  calc _ = 𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ spec₀.randomOracle ob).run w.2 >>= fun u ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont w.1)).run u.2 >>= fun v ↦ g v.1] :=
        evalDist_bind_congr_of_support _ _ _ fun w _ ↦
          (evalDist_simulateQ_run_bind_romImpl_discard ob (cont w.1) w.2 g).symm
    _ = 𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ spec₀.randomOracle ob).run w.2 >>= fun u ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont u.1)).run u.2 >>= fun v ↦ g v.1] :=
        evalDist_bind_congr_of_support _ _ _ fun w hw ↦ evalDist_bind_congr_of_support _ _ _
          fun u hu ↦ by rw [eq_of_mem_support_run_bind_run_of_le oa ob h hle hw hu]
    _ = 𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun u ↦
        (simulateQ spec₀.randomOracle oa).run u.2 >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont u.1)).run w.2 >>= fun v ↦ g v.1] :=
        evalDist_simulateQ_run_bind_swap oa ob cache fun _ b c ↦
          (simulateQ (OracleSpec.romImpl spec₀) (cont b)).run c >>= fun v ↦ g v.1
    _ = _ := evalDist_bind_congr_of_support _ _ _ fun u _ ↦
        evalDist_simulateQ_run_bind_romImpl_discard oa (cont u.1) u.2 g

/-- Two runs in a row that agree on every answer function return the same value.

One answer function is consistent with the joint run. -/
theorem eq_of_mem_support_run_bind_run {α : Type} (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, evalWithAnswerFn f oa = evalWithAnswerFn f ob)
    (cache : spec₀.QueryCache) {w : α × spec₀.QueryCache} {v : α × spec₀.QueryCache}
    (hw : w ∈ support ((simulateQ spec₀.randomOracle oa).run cache))
    (hv : v ∈ support ((simulateQ spec₀.randomOracle ob).run w.2)) : w.1 = v.1 :=
  eq_of_mem_support_run_bind_run_of_le (known := ∅) oa ob (fun f _ ↦ h f)
    (fun _ _ h ↦ by simp at h) hw hv

/-- Two hash computations that agree on every answer function can replace each other.

The continuation then has the same output distribution. -/
theorem evalDist_interchange {α β γ : Type} [MeasurableSpace γ] (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, evalWithAnswerFn f oa = evalWithAnswerFn f ob)
    (cont : α → OracleComp (unifSpec + spec₀) β) (cache : spec₀.QueryCache)
    (g : β → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont w.1)).run w.2 >>= fun v ↦ g v.1] =
      𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont w.1)).run w.2 >>= fun v ↦ g v.1] :=
  evalDist_interchange_of_le (known := ∅) oa ob (fun f _ ↦ h f) cont
    (fun _ _ h ↦ by simp at h) g

/-- Counting the hash calls does not change the probability of an event on the output. -/
theorem prEvent_run_withAddCost (oa : OracleComp (unifSpec + spec₀) Bool)
    (cost : (unifSpec + spec₀).Domain → Nat) :
    Pr{let r ← (simulateQ ((OracleSpec.romImpl spec₀).withAddCost cost) oa).run.run' ∅}[
        r.1 = true] =
      Pr{let r ← (simulateQ (OracleSpec.romImpl spec₀) oa).run' ∅}[r = true] := by
  rw [← QueryImpl.fst_map_run_withCost (OracleSpec.romImpl spec₀)
    (fun t ↦ Multiplicative.ofAdd (cost t)) oa]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]
  rfl

/-- Two computations are interchangeable in the random oracle model.

Followed by any continuation and run from any cache, they give the same output distribution. -/
def RomEquiv {α : Type} (x y : OracleComp (unifSpec + spec₀) α) : Prop :=
  ∀ {β : Type} [MeasurableSpace β] (cont : α → OracleComp (unifSpec + spec₀) β)
    (cache : spec₀.QueryCache),
    𝒟[(simulateQ (OracleSpec.romImpl spec₀) (x >>= cont)).run' cache] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) (y >>= cont)).run' cache]

/-- Two computations are interchangeable once the cache holds `known`.

Followed by any continuation, they give one output distribution from each cache above `known`. -/
def RomEquivFrom {α : Type} (known : spec₀.QueryCache) (x y : OracleComp (unifSpec + spec₀) α) :
    Prop :=
  ∀ {β : Type} [MeasurableSpace β] (cont : α → OracleComp (unifSpec + spec₀) β)
    (cache : spec₀.QueryCache), known ≤ cache →
    𝒟[(simulateQ (OracleSpec.romImpl spec₀) (x >>= cont)).run' cache] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) (y >>= cont)).run' cache]

namespace RomEquivFrom

/-- With no known answer, the relation is interchangeability from every cache. -/
theorem empty_iff {α : Type} {x y : OracleComp (unifSpec + spec₀) α} :
    RomEquivFrom ∅ x y ↔ RomEquiv x y :=
  ⟨fun h _ _ cont cache ↦ h cont cache fun _ _ h ↦ by simp at h,
    fun h _ _ cont cache _ ↦ h cont cache⟩

/-- A relation that holds for fewer known answers holds for more. -/
theorem mono {α : Type} {known known' : spec₀.QueryCache} (hle : known ≤ known')
    {x y : OracleComp (unifSpec + spec₀) α} (h : RomEquivFrom known x y) :
    RomEquivFrom known' x y :=
  fun cont cache hc ↦ h cont cache (hle.trans hc)

/-- A computation is interchangeable with itself. -/
theorem refl {α : Type} (known : spec₀.QueryCache) (x : OracleComp (unifSpec + spec₀) α) :
    RomEquivFrom known x x :=
  fun _ _ _ ↦ rfl

/-- The relation is symmetric. -/
theorem symm {α : Type} {known : spec₀.QueryCache} {x y : OracleComp (unifSpec + spec₀) α}
    (h : RomEquivFrom known x y) : RomEquivFrom known y x :=
  fun cont cache hc ↦ (h cont cache hc).symm

/-- The relation is transitive. -/
theorem trans {α : Type} {known : spec₀.QueryCache} {x y z : OracleComp (unifSpec + spec₀) α}
    (h₁ : RomEquivFrom known x y) (h₂ : RomEquivFrom known y z) : RomEquivFrom known x z :=
  fun cont cache hc ↦ (h₁ cont cache hc).trans (h₂ cont cache hc)

/-- Related computations stay related when the same continuation follows. -/
theorem bind_left {α β : Type} {known : spec₀.QueryCache} {x y : OracleComp (unifSpec + spec₀) α}
    (h : RomEquivFrom known x y) (k : α → OracleComp (unifSpec + spec₀) β) :
    RomEquivFrom known (x >>= k) (y >>= k) := by
  intro γ _ cont cache hc
  simpa only [bind_assoc] using h (fun a ↦ k a >>= cont) cache hc

/-- Continuations related from the cache that a first computation leaves give related binds.

Only the runs of the first computation from a cache that extends `known` matter. -/
theorem bind_right_of_mem_support {α β : Type} {known : spec₀.QueryCache}
    (x : OracleComp (unifSpec + spec₀) α) {k k' : α → OracleComp (unifSpec + spec₀) β}
    (h : ∀ cache, known ≤ cache →
      ∀ z ∈ support ((simulateQ (OracleSpec.romImpl spec₀) x).run cache),
        RomEquivFrom z.2 (k z.1) (k' z.1)) :
    RomEquivFrom known (x >>= k) (x >>= k') := by
  intro γ _ cont cache hc
  simp only [bind_assoc, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
  simpa only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] using
    h cache hc w hw cont w.2 le_rfl

/-- Pointwise related continuations of one computation give related binds. -/
theorem bind_right {α β : Type} {known : spec₀.QueryCache} (x : OracleComp (unifSpec + spec₀) α)
    {k k' : α → OracleComp (unifSpec + spec₀) β} (h : ∀ a, RomEquivFrom known (k a) (k' a)) :
    RomEquivFrom known (x >>= k) (x >>= k') :=
  bind_right_of_mem_support x fun _ hc _ hz ↦
    mono (hc.trans (le_snd_of_mem_support_run_romImpl x hz)) (h _)

/-- A hash query adds its answer to the known ones.

The continuations need to be related only for the answers that the query can return.

That is any answer when `t` is not known yet, and the known answer otherwise. -/
theorem query_bind {β : Type} {known : spec₀.QueryCache} (t : ι₀)
    {k k' : spec₀.Range t → OracleComp (unifSpec + spec₀) β}
    (h : ∀ u, (known t = none ∨ known t = some u) →
      RomEquivFrom (known.cacheQuery t u) (k u) (k' u)) :
    RomEquivFrom known
      (OracleComp.liftComp (spec₀.query t : OracleComp spec₀ _) (unifSpec + spec₀) >>= k)
      (OracleComp.liftComp (spec₀.query t : OracleComp spec₀ _) (unifSpec + spec₀) >>= k') := by
  refine bind_right_of_mem_support _ fun cache hc z hz ↦ ?_
  rw [QueryImpl.simulateQ_add_liftComp_right, simulateQ_spec_query] at hz
  have hle : cache ≤ z.2 := QueryImpl.withCaching_cache_le _ t cache z hz
  have hz' : z.2 t = some z.1 := QueryImpl.withCaching_run_caches _ t cache z hz
  have hknown : known t = none ∨ known t = some z.1 := by
    rcases hkt : known t with _ | v
    · exact Or.inl rfl
    · exact Or.inr ((hle (hc hkt)).symm.trans hz')
  have hcache : known.cacheQuery t z.1 ≤ z.2 := by
    intro t' u' h'
    by_cases ht : t' = t
    · subst ht
      rw [QueryCache.cacheQuery_self] at h'
      rw [hz', h']
    · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h'
      exact hle (hc h')
  intro β _ cont cache' hc'
  exact h z.1 hknown cont cache' (hcache.trans hc')

/-- Two hash computations that agree on every answer function agreeing with `known` are related.

The hash computations are lifted to the world with coins. -/
theorem liftComp {α : Type} {known : spec₀.QueryCache} (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, known.AgreesWithFn f →
      evalWithAnswerFn f oa = evalWithAnswerFn f ob) :
    RomEquivFrom known (OracleComp.liftComp oa (unifSpec + spec₀))
      (OracleComp.liftComp ob (unifSpec + spec₀)) := by
  intro γ _ cont cache hc
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    QueryImpl.simulateQ_add_liftComp_right, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  exact evalDist_interchange_of_le oa ob h cont hc fun b ↦ pure b

/-- Two runs of one adversary, each with a logging oracle, are related.

Each query to the two oracles must be answered by related computations.

The run returns the adversary's output and the log of its oracle queries. -/
theorem run_simulateQ_withLogging {ιS : Type} {S : OracleSpec.{0, 0} ιS} {α : Type}
    {known : spec₀.QueryCache} (s₁ s₂ : QueryImpl S (OracleComp (unifSpec + spec₀)))
    (h : ∀ t, RomEquivFrom known (s₁ t) (s₂ t)) (A : OracleComp ((unifSpec + spec₀) + S) α) :
    RomEquivFrom known
      (simulateQ (QueryImpl.ofLift (unifSpec + spec₀)
        (WriterT (QueryLog S) (OracleComp (unifSpec + spec₀))) +
          QueryImpl.withLogging s₁) A).run
      (simulateQ (QueryImpl.ofLift (unifSpec + spec₀)
        (WriterT (QueryLog S) (OracleComp (unifSpec + spec₀))) +
          QueryImpl.withLogging s₂) A).run := by
  induction A using OracleComp.inductionOn with
  | pure a => exact refl _ _
  | query_bind t k ih =>
    rcases t with t | t
    · simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
      refine bind_right _ fun x ↦ ?_
      simp only [map_eq_bind_pure_comp]
      exact bind_left (ih x.1) _
    · simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.add_apply_inr,
        QueryImpl.withLogging_apply, WriterT.run_tell, bind_assoc,
        map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      have hl : ∀ s : QueryImpl S (OracleComp (unifSpec + spec₀)),
          (liftM (s t) : WriterT (QueryLog S) (OracleComp (unifSpec + spec₀)) _).run =
            s t >>= fun u ↦ pure (u, ∅) := fun s ↦ by
          change (monadLift (s t) : WriterT (QueryLog S) (OracleComp (unifSpec + spec₀)) _).run = _
          rw [WriterT.run_monadLift', map_eq_bind_pure_comp]; rfl
      simp only [hl, bind_assoc, pure_bind]
      apply RomEquivFrom.trans (bind_left (h t) _)
      apply bind_right
      intro u
      exact bind_left (ih u) _

end RomEquivFrom

namespace RomEquiv

/-- Interchangeable computations, run alone from one cache, have one output distribution. -/
theorem evalDist_run' {α : Type} [MeasurableSpace α] {x y : OracleComp (unifSpec + spec₀) α}
    (h : RomEquiv x y) (cache : spec₀.QueryCache) :
    𝒟[(simulateQ (OracleSpec.romImpl spec₀) x).run' cache] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) y).run' cache] := by
  simpa only [bind_pure] using h pure cache

/-- A computation is interchangeable with itself. -/
theorem refl {α : Type} (x : OracleComp (unifSpec + spec₀) α) : RomEquiv x x :=
  RomEquivFrom.empty_iff.1 (RomEquivFrom.refl ∅ x)

/-- Interchangeability is symmetric. -/
theorem symm {α : Type} {x y : OracleComp (unifSpec + spec₀) α} (h : RomEquiv x y) :
    RomEquiv y x :=
  RomEquivFrom.empty_iff.1 (RomEquivFrom.symm (RomEquivFrom.empty_iff.2 h))

/-- Interchangeability is transitive. -/
theorem trans {α : Type} {x y z : OracleComp (unifSpec + spec₀) α} (h₁ : RomEquiv x y)
    (h₂ : RomEquiv y z) : RomEquiv x z :=
  RomEquivFrom.empty_iff.1
    (RomEquivFrom.trans (RomEquivFrom.empty_iff.2 h₁) (RomEquivFrom.empty_iff.2 h₂))

/-- Interchangeable computations stay so when the same continuation follows. -/
theorem bind_left {α β : Type} {x y : OracleComp (unifSpec + spec₀) α} (h : RomEquiv x y)
    (k : α → OracleComp (unifSpec + spec₀) β) : RomEquiv (x >>= k) (y >>= k) :=
  RomEquivFrom.empty_iff.1 (RomEquivFrom.bind_left (RomEquivFrom.empty_iff.2 h) k)

/-- Pointwise interchangeable continuations of one computation give interchangeable binds. -/
theorem bind_right {α β : Type} (x : OracleComp (unifSpec + spec₀) α)
    {k k' : α → OracleComp (unifSpec + spec₀) β} (h : ∀ a, RomEquiv (k a) (k' a)) :
    RomEquiv (x >>= k) (x >>= k') :=
  RomEquivFrom.empty_iff.1 (RomEquivFrom.bind_right x fun a ↦ RomEquivFrom.empty_iff.2 (h a))

/-- Two hash computations that agree on every answer function are interchangeable.

The hash computations are lifted to the world with coins. -/
theorem liftComp {α : Type} (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, evalWithAnswerFn f oa = evalWithAnswerFn f ob) :
    RomEquiv (OracleComp.liftComp oa (unifSpec + spec₀))
      (OracleComp.liftComp ob (unifSpec + spec₀)) :=
  RomEquivFrom.empty_iff.1 (RomEquivFrom.liftComp oa ob fun f _ ↦ h f)

/-- Two queries asked in either order are interchangeable.

The two computations may differ, since they query in different orders. -/
theorem liftComp_query_swap (t t' : ι₀) :
    RomEquiv
      (OracleComp.liftComp (spec := spec₀) (do
        let u ← spec₀.query t; let v ← spec₀.query t'; pure (u, v))
        (unifSpec + spec₀))
      (OracleComp.liftComp (spec := spec₀) (do
        let v ← spec₀.query t'; let u ← spec₀.query t; pure (u, v))
        (unifSpec + spec₀)) := by
  apply liftComp
  intro f
  rfl

/-- Two runs of one adversary, each with a logging oracle, are interchangeable.

Each query to the two oracles must be answered by interchangeable computations.

The run returns the adversary's output and the log of its oracle queries. -/
theorem run_simulateQ_withLogging {ιS : Type} {S : OracleSpec.{0, 0} ιS} {α : Type}
    (s₁ s₂ : QueryImpl S (OracleComp (unifSpec + spec₀)))
    (h : ∀ t, RomEquiv (s₁ t) (s₂ t)) (A : OracleComp ((unifSpec + spec₀) + S) α) :
    RomEquiv
      (simulateQ (QueryImpl.ofLift (unifSpec + spec₀)
        (WriterT (QueryLog S) (OracleComp (unifSpec + spec₀))) +
          QueryImpl.withLogging s₁) A).run
      (simulateQ (QueryImpl.ofLift (unifSpec + spec₀)
        (WriterT (QueryLog S) (OracleComp (unifSpec + spec₀))) +
          QueryImpl.withLogging s₂) A).run :=
  RomEquivFrom.empty_iff.1
    (RomEquivFrom.run_simulateQ_withLogging s₁ s₂ (fun t ↦ RomEquivFrom.empty_iff.2 (h t)) A)

end RomEquiv

section Translate

variable {ιW : Type} {W : OracleSpec.{0, 0} ιW} {D₁ R₁ D₂ R₂ : Type}

/-- Requests to one oracle, sent translated to another, with the answers translated back.

Queries to every other oracle pass through. -/
def translateImpl (ψ : D₁ → D₂) (φ : R₂ → R₁) :
    QueryImpl (W + (D₁ →ₒ R₁)) (OracleComp (W + (D₂ →ₒ R₂))) :=
  (fun t ↦ ((W + (D₂ →ₒ R₂)).query (.inl t) : OracleComp (W + (D₂ →ₒ R₂)) _)) +
    fun d ↦ φ <$> ((W + (D₂ →ₒ R₂)).query (.inr (ψ d)) : OracleComp (W + (D₂ →ₒ R₂)) R₂)

omit [DecidableEq ι₀] [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] in
theorem translateImpl_inl (ψ : D₁ → D₂) (φ : R₂ → R₁) (t : ιW) :
    translateImpl (W := W) ψ φ (.inl t) =
      ((W + (D₂ →ₒ R₂)).query (.inl t) : OracleComp (W + (D₂ →ₒ R₂)) _) := rfl

omit [DecidableEq ι₀] [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] in
theorem translateImpl_inr (ψ : D₁ → D₂) (φ : R₂ → R₁) (d : D₁) :
    translateImpl (W := W) ψ φ (.inr d) =
      φ <$> ((W + (D₂ →ₒ R₂)).query (.inr (ψ d)) : OracleComp (W + (D₂ →ₒ R₂)) R₂) := rfl

omit [DecidableEq ι₀] [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] in
/-- An adversary run with translated requests is the adversary run against the translated oracle.

The log of the translated requests, translated back entry by entry, is the log of the direct run.

Translating back needs a left inverse of the request translation. -/
theorem map_run_simulateQ_withLogging_translateImpl {α : Type}
    (s : QueryImpl (D₂ →ₒ R₂) (OracleComp W)) (ψ : D₁ → D₂) (φ : R₂ → R₁) (χ : D₂ → D₁)
    (hχ : ∀ d, χ (ψ d) = d) (A : OracleComp (W + (D₁ →ₒ R₁)) α) :
    (fun p ↦ (p.1, p.2.map fun e ↦ (⟨χ e.1, φ e.2⟩ : (_ : D₁) × R₁))) <$>
        (simulateQ (QueryImpl.ofLift W (WriterT (QueryLog (D₂ →ₒ R₂)) (OracleComp W)) +
          QueryImpl.withLogging s) (simulateQ (translateImpl ψ φ) A)).run =
      (simulateQ (QueryImpl.ofLift W (WriterT (QueryLog (D₁ →ₒ R₁)) (OracleComp W)) +
          QueryImpl.withLogging (fun d ↦ φ <$> s (ψ d) : QueryImpl (D₁ →ₒ R₁) (OracleComp W)))
        A).run := by
  have hl : ∀ {ω : Type} [EmptyCollection ω] [Append ω] (t : ιW),
      (liftM (W.query t) : WriterT ω (OracleComp W) _).run =
        (fun u ↦ (u, ∅)) <$> (W.query t : OracleComp W _) :=
    fun t ↦ by
      change (monadLift (W.query t : OracleComp W _) : WriterT _ (OracleComp W) _).run = _
      rw [WriterT.run_monadLift']
  induction A using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with t | d
    · simp [translateImpl_inl, WriterT.run_bind, ← ih, QueryImpl.add_apply_inl,
        QueryImpl.ofLift_apply, hl]
    · simp [translateImpl_inr, WriterT.run_bind, ← ih, QueryImpl.add_apply_inr, hχ]

end Translate

end EthLib.Cryptography.HashSig
