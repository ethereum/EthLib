module

public import EthLib.Cryptography.Proofs.HashSig.Commute
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
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

A relation packages this fact.

It is closed under binds, and under the run of an adversary with a logging oracle.
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

/-- Two runs in a row that agree on every answer function return the same value.

One answer function is consistent with the joint run. -/
theorem eq_of_mem_support_run_bind_run {α : Type} (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, evalWithAnswerFn f oa = evalWithAnswerFn f ob)
    (cache : spec₀.QueryCache) {w : α × spec₀.QueryCache} {v : α × spec₀.QueryCache}
    (hw : w ∈ support ((simulateQ spec₀.randomOracle oa).run cache))
    (hv : v ∈ support ((simulateQ spec₀.randomOracle ob).run w.2)) : w.1 = v.1 := by
  have hjoint : ((w.1, v.1), v.2) ∈ support ((simulateQ spec₀.randomOracle
      (oa >>= fun a ↦ ob >>= fun b ↦ pure (a, b))).run cache) := by
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨w, hw, v, hv, rfl⟩
  obtain ⟨f, -, hf⟩ := (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support _ cache _).2
    ⟨_, hjoint⟩
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Prod.mk.injEq] at hf
  rw [← hf.1, ← hf.2, h]

/-- Two hash computations that agree on every answer function can replace each other.

The continuation then has the same output distribution. -/
theorem evalDist_interchange {α β γ : Type} [MeasurableSpace γ] (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, evalWithAnswerFn f oa = evalWithAnswerFn f ob)
    (cont : α → OracleComp (unifSpec + spec₀) β) (cache : spec₀.QueryCache)
    (g : β → ProbComp γ) :
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
          fun u hu ↦ by rw [eq_of_mem_support_run_bind_run oa ob h cache hw hu]
    _ = 𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun u ↦
        (simulateQ spec₀.randomOracle oa).run u.2 >>= fun w ↦
        (simulateQ (OracleSpec.romImpl spec₀) (cont u.1)).run w.2 >>= fun v ↦ g v.1] :=
        evalDist_simulateQ_run_bind_swap oa ob cache fun _ b c ↦
          (simulateQ (OracleSpec.romImpl spec₀) (cont b)).run c >>= fun v ↦ g v.1
    _ = _ := evalDist_bind_congr_of_support _ _ _ fun u _ ↦
        evalDist_simulateQ_run_bind_romImpl_discard oa (cont u.1) u.2 g

/-- Two computations are interchangeable in the random oracle model.

Followed by any continuation and run from any cache, they give the same output distribution. -/
def RomEquiv {α : Type} (x y : OracleComp (unifSpec + spec₀) α) : Prop :=
  ∀ {β : Type} [MeasurableSpace β] (cont : α → OracleComp (unifSpec + spec₀) β)
    (cache : spec₀.QueryCache),
    𝒟[(simulateQ (OracleSpec.romImpl spec₀) (x >>= cont)).run' cache] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) (y >>= cont)).run' cache]

namespace RomEquiv

/-- Interchangeable computations, run alone from one cache, have one output distribution. -/
theorem evalDist_run' {α : Type} [MeasurableSpace α] {x y : OracleComp (unifSpec + spec₀) α}
    (h : RomEquiv x y) (cache : spec₀.QueryCache) :
    𝒟[(simulateQ (OracleSpec.romImpl spec₀) x).run' cache] =
      𝒟[(simulateQ (OracleSpec.romImpl spec₀) y).run' cache] := by
  simpa only [bind_pure] using h pure cache

/-- A computation is interchangeable with itself. -/
theorem refl {α : Type} (x : OracleComp (unifSpec + spec₀) α) : RomEquiv x x := by
  intro β _ cont cache; rfl

/-- Interchangeability is symmetric. -/
theorem symm {α : Type} {x y : OracleComp (unifSpec + spec₀) α} (h : RomEquiv x y) :
    RomEquiv y x := by
  intro β _ cont cache; exact (h cont cache).symm

/-- Interchangeability is transitive. -/
theorem trans {α : Type} {x y z : OracleComp (unifSpec + spec₀) α} (h₁ : RomEquiv x y)
    (h₂ : RomEquiv y z) : RomEquiv x z := by
  intro β _ cont cache; exact (h₁ cont cache).trans (h₂ cont cache)

/-- Interchangeable computations stay so when the same continuation follows. -/
theorem bind_left {α β : Type} {x y : OracleComp (unifSpec + spec₀) α} (h : RomEquiv x y)
    (k : α → OracleComp (unifSpec + spec₀) β) : RomEquiv (x >>= k) (y >>= k) := by
  intro γ _ cont cache
  simpa only [bind_assoc] using h (fun a ↦ k a >>= cont) cache

/-- Pointwise interchangeable continuations of one computation give interchangeable binds. -/
theorem bind_right {α β : Type} (x : OracleComp (unifSpec + spec₀) α)
    {k k' : α → OracleComp (unifSpec + spec₀) β} (h : ∀ a, RomEquiv (k a) (k' a)) :
    RomEquiv (x >>= k) (x >>= k') := by
  intro γ _ cont cache
  simp only [bind_assoc, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine evalDist_bind_congr_of_support _ _ _ fun w _ ↦ ?_
  simpa only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] using
    h w.1 cont w.2

/-- Two hash computations that agree on every answer function are interchangeable.

The hash computations are lifted to the world with coins. -/
theorem liftComp {α : Type} (oa ob : OracleComp spec₀ α)
    (h : ∀ f : QueryImpl spec₀ Id, evalWithAnswerFn f oa = evalWithAnswerFn f ob) :
    RomEquiv (OracleComp.liftComp oa (unifSpec + spec₀))
      (OracleComp.liftComp ob (unifSpec + spec₀)) := by
  intro γ _ cont cache
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    QueryImpl.simulateQ_add_liftComp_right, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  exact evalDist_interchange oa ob h cont cache fun b ↦ pure b

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
          QueryImpl.withLogging s₂) A).run := by
  induction A using OracleComp.inductionOn with
  | pure a => exact refl _
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
      apply RomEquiv.trans (bind_left (h t) _)
      apply bind_right
      intro u
      exact bind_left (ih u) _

end RomEquiv

end EthLib.Cryptography.HashSig
