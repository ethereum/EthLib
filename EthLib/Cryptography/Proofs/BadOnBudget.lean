module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: a bad event charged to a query budget

A stateful oracle answers a run that stays within a query budget.

A potential maps each budget to a bound in `[0, ∞]` on the chance that the run ends bad.

This is the union bound over the queries of the run.

With a weight on each query, a size and the chance of each step grow with the weights.
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
    -- The invariant may read the budget, as a bound on the size of a table does.
    (hinv : ∀ t b s, canQuery t b → inv b s → ¬bad s →
      ∀ z ∈ support ((impl t).run s), ¬bad z.2 → inv (cost t b) z.2)
    (hstep : ∀ t b s, canQuery t b → inv b s → ¬bad s →
      Pr{let z ← (impl t).run s}[bad z.2] + Φ (cost t b) ≤ Φ b)
    {α : Type} {oa : OracleComp spec α} {b : B} (hb : IsQueryBound oa b canQuery cost) {s : σ}
    (hs : inv b s) (hbad : ¬bad s) :
    Pr{let z ← (simulateQ impl oa).run s}[bad z.2] ≤ Φ b := by
  -- Induction on the run, one query at a time.
  induction oa using OracleComp.inductionOn generalizing b s with
  -- A run that asks nothing ends in its good start state.
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    simp [hbad]
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at hb
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    -- The first query turns the state bad, or the rest of the run does from a good state.
    --
    -- The rest is charged the potential after the first query, by the induction hypothesis.
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z ↦ bad z.2) _
      (ε := Φ (cost t b)) fun z hz hbz ↦ ?_).trans (hstep t b s hb.1 hs hbad)
    exact ih z.1 (hb.2 z.1) (hinv t b s hb.1 hs hbad z hz hbz) hbz

/-! ## Budgets of weights -/

section Weights

variable {ι' : Type} {spec' : OracleSpec ι'} {α : Type}

/-- Along a run within a budget of weights, a size grows by at most the budget.

Each step from a state of the invariant raises the size by at most the weight of its query. -/
theorem size_le_of_mem_support_run_weightBudget
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (inv : σ → Prop) (w : ι → ℕ)
    (size : σ → ℕ)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (hsize : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), size z.2 ≤ size s + w t)
    {oa : OracleComp spec α} {Q : ℕ}
    (hQ : IsQueryBound oa Q (fun t n => w t ≤ n) fun t n => n - w t) {s₀ : σ} (hs₀ : inv s₀) :
    ∀ z ∈ support ((simulateQ impl oa).run s₀), size z.2 ≤ size s₀ + Q := by
  induction oa using OracleComp.inductionOn generalizing Q s₀ with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at hQ
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    have h1 := hsize t s₀ hs₀ us hus
    have h2 := ih us.1 (hQ.2 us.1) (hinv t s₀ hs₀ us hus) z hz
    omega

/-- **The union bound over a budget of weights.**

A run of budget `Q` from a good state turns bad with chance at most `Q δ`.

Each step of weight `w` must turn bad with chance at most `w δ` while its size stays within `N`. -/
theorem prEvent_bad_le_of_weightBudget (impl : QueryImpl spec (StateT σ ProbComp))
    (bad inv : σ → Prop)
    (w : ι → ℕ) (size : σ → ℕ) (N : ℕ) (δ : ℝ≥0∞)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (hsize : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), size z.2 ≤ size s + w t)
    -- The step starts in a good state of the invariant, and its size stays within `N`.
    (hstep : ∀ t s, inv s → ¬bad s → size s + w t ≤ N →
      Pr{let z ← (impl t).run s}[bad z.2] ≤ w t * δ)
    {oa : OracleComp spec α} {Q : ℕ}
    (hQ : IsQueryBound oa Q (fun t n => w t ≤ n) fun t n => n - w t) {s₀ : σ} (hs₀ : inv s₀)
    -- The run starts in a good state, with room for its budget below `N`.
    (hb : ¬bad s₀) (hN : size s₀ + Q ≤ N) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤ Q * δ := by
  -- The potential of a budget `b` is `b δ`; the invariant also bounds the size by `N - b`.
  refine prEvent_bad_le_of_isQueryBound (fun b s => inv s ∧ size s + b ≤ N) bad
    (fun b => (b : ℝ≥0∞) * δ) (fun t b s hc hs _ z hz _ => ⟨hinv t s hs.1 z hz, ?_⟩)
    (fun t b s hc hs hbs => ?_) hQ ⟨hs₀, hN⟩ hb
  · have := hsize t s hs.1 z hz
    have := hs.2
    omega
  · have hle := hstep t s hs.1 hbs (by have := hs.2; omega)
    calc Pr{let z ← (impl t).run s}[bad z.2] + ((b - w t : ℕ) : ℝ≥0∞) * δ
        ≤ (w t : ℝ≥0∞) * δ + ((b - w t : ℕ) : ℝ≥0∞) * δ := add_le_add hle le_rfl
      _ = (b : ℝ≥0∞) * δ := by
        rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hc]

end Weights

end EthLib.Cryptography
