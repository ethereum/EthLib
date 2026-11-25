module

public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Proofs: runs that project onto other runs in law

Take two stateful oracles, and a map from the states of the first to those of the second.

When each step from a state of an invariant projects in law onto a step of the second, so do runs.

It also rewrites the law of a draw followed by a continuation.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleComp OracleSpec

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

/-- The outputs of two runs related by a projection in law have one law. -/
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

/-! ## A draw, then a continuation -/

/-- A continuation that reads only the first component of a draw sees its first marginal. -/
theorem bind_fst_evalDistEq {β γ : Type} {X : ProbComp (α × β)} {Y : ProbComp α}
    (h : Prod.fst <$> X =ᵈ Y) (R : α → ProbComp γ) : (X >>= fun w => R w.1) =ᵈ (Y >>= R) := by
  rw [← bind_map_left]
  exact EvalDistEq.bind_left h R

/-- The chance of an event after a draw, then a run, is its chance after their bind. -/
theorem prEvent_bind_assoc {β γ : Type} (mx : ProbComp β) (f : β → ProbComp γ) (q : γ → Prop) :
    Pr{let b ← mx; let c ← f b}[q c] = Pr{let c ← mx >>= f}[q c] := by
  simp [map_bind]

end EthLib.Cryptography
