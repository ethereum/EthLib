module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: a bad event charged to a query budget

A stateful oracle answers a run that stays within a query budget.

A potential maps each budget to a bound in `[0, ∞]`.

Take a query that the budget allows, from a good state.

Add the chance that it turns the state bad and the potential of the budget after it.

The sum is at most the potential of the budget before it.

The steps may also keep an invariant that reads the budget, such as a bound on the size of a table.

Then the run ends bad with chance at most the potential of its budget.

This is the union bound over the queries of the run.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleComp OracleSpec ENNReal

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **The union bound with a potential on the query budget.**

Take a run within a query budget, from a good state that meets the invariant of that budget.

Take a good state that meets the invariant of a budget, and a query that the budget allows.

The chance that it turns the state bad, plus the potential after it, is at most the potential.

A good state after the query meets the invariant of the budget after it.

Then the run ends bad with chance at most the potential of its budget. -/
theorem prEvent_bad_le_of_isQueryBound {B : Type} {impl : QueryImpl spec (StateT σ ProbComp)}
    {canQuery : ι → B → Prop} {cost : ι → B → B} (inv : B → σ → Prop) (bad : σ → Prop)
    (Φ : B → ℝ≥0∞)
    (hinv : ∀ t b s, canQuery t b → inv b s → ¬bad s →
      ∀ z ∈ support ((impl t).run s), ¬bad z.2 → inv (cost t b) z.2)
    (hstep : ∀ t b s, canQuery t b → inv b s → ¬bad s →
      Pr{let z ← (impl t).run s}[bad z.2] + Φ (cost t b) ≤ Φ b)
    {α : Type} {oa : OracleComp spec α} {b : B} (hb : IsQueryBound oa b canQuery cost) {s : σ}
    (hs : inv b s) (hbad : ¬bad s) :
    Pr{let z ← (simulateQ impl oa).run s}[bad z.2] ≤ Φ b := by
  induction oa using OracleComp.inductionOn generalizing b s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    simp [hbad]
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at hb
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z ↦ bad z.2) _
      (ε := Φ (cost t b)) fun z hz hbz ↦ ?_).trans (hstep t b s hb.1 hs hbad)
    exact ih z.1 (hb.2 z.1) (hinv t b s hb.1 hs hbad z hz hbz) hbz

end EthLib.Cryptography
