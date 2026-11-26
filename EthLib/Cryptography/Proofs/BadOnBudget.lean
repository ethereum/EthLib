module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Proofs: a bad event charged to a query budget

A stateful oracle answers a run that stays within a query budget.

A potential maps each budget to a bound in `[0, ∞]` on the chance that the run ends bad.

This is the union bound over the queries of the run.

The potential can also read the state, and charge a good final state.
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

/-- Weigh a bad outcome one and a good outcome at most `c`.

The weighted outcomes sum to at most the chance of a bad outcome plus `c`. -/
theorem tsum_ite_le_prEvent_add {β : Type} (oa : ProbComp β) (bad : β → Prop) [DecidablePred bad]
    (f : β → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ z ∈ support oa, ¬bad z → f z ≤ c) :
    ∑' z, Pr{let y ← oa}[y = z] * (if bad z then 1 else f z) ≤ Pr{let z ← oa}[bad z] + c := by
  rw [prEvent_eq_tsum_ite]
  calc _ ≤ ∑' z, ((if bad z then Pr{let y ← oa}[y = z] else 0) + Pr{let y ← oa}[y = z] * c) :=
        tsum_le_tsum fun z => by
          by_cases hz : z ∈ support oa
          · split_ifs with hb
            · simp
            · rw [zero_add]
              gcongr
              exact h z hz hb
          · simp [prEvent_eq_zero_of_not_mem_support _ hz]
    _ ≤ _ := by
      rw [tsum_add, ENNReal.tsum_mul_right]
      gcongr
      exact mul_le_of_le_one_left' (tsum_prEvent_le_one oa)

/-- **The union bound with a potential on the budget and the state.**

A run within a query budget, from a good state of the invariant, ends bad or good.

Weigh a bad end one and a good end its final charge: the total is at most the starting potential. -/
theorem tsum_le_of_isQueryBound {B : Type} {impl : QueryImpl spec (StateT σ ProbComp)}
    {canQuery : ι → B → Prop} {cost : ι → B → B} (inv : B → σ → Prop) (bad : σ → Prop)
    [DecidablePred bad] (Φ : B → σ → ℝ≥0∞) (T : σ → ℝ≥0∞)
    -- A bad state stays bad.
    (hmono : ∀ t s, bad s → ∀ z ∈ support ((impl t).run s), bad z.2)
    -- A good state after a query meets the invariant of the budget after it.
    (hinv : ∀ t b s, canQuery t b → inv b s → ¬bad s →
      ∀ z ∈ support ((impl t).run s), ¬bad z.2 → inv (cost t b) z.2)
    -- From a good state, a query's outcomes weigh at most the potential.
    --
    -- A bad outcome weighs one, and a good one its potential after the query.
    (hstep : ∀ t b s, canQuery t b → inv b s → ¬bad s →
      ∑' z, Pr{let y ← (impl t).run s}[y = z] *
        (if bad z.2 then 1 else Φ (cost t b) z.2) ≤ Φ b s)
    -- A good state of the invariant is charged at most its potential at the end.
    (hstop : ∀ b s, inv b s → ¬bad s → T s ≤ Φ b s)
    {α : Type} {oa : OracleComp spec α} {b : B} (hb : IsQueryBound oa b canQuery cost) {s : σ}
    (hs : inv b s) (hbad : ¬bad s) :
    ∑' z, Pr{let y ← (simulateQ impl oa).run s}[y = z] * (if bad z.2 then 1 else T z.2) ≤
      Φ b s := by
  induction oa using OracleComp.inductionOn generalizing b s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul, hbad,
      ↓reduceIte]
    exact hstop b s hs hbad
  | query_bind t k ih =>
    rw [isQueryBound_query_bind_iff] at hb
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp_rw [OracleComp.prEvent_bind_eq_tsum _ _ (· = _), ← ENNReal.tsum_mul_right]
    rw [tsum_comm]
    refine (tsum_le_tsum fun u => ?_).trans (hstep t b s hb.1 hs hbad)
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    -- An unreachable first step weighs nothing.
    by_cases hu : u ∈ support ((impl t).run s)
    swap
    · simp [prEvent_eq_zero_of_not_mem_support _ hu]
    gcongr
    split_ifs with hbu
    -- After a bad first step the run stays bad, and its masses sum to at most one.
    · refine (tsum_le_tsum fun z => ?_).trans
        (tsum_prEvent_le_one ((simulateQ impl (k u.1)).run u.2))
      by_cases hz : z ∈ support ((simulateQ impl (k u.1)).run u.2)
      · simp [simulateQ_run_preserves_inv_of_query impl bad hmono (k u.1) u.2 hbu z hz]
      · simp [prEvent_eq_zero_of_not_mem_support _ hz]
    -- After a good first step, the rest of the run is charged by induction.
    · exact ih u.1 (hb.2 u.1) (hinv t b s hb.1 hs hbad u hu hbu) hbu

end EthLib.Cryptography
