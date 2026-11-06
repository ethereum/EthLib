module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.Interpreter

/-!
# Linear potentials with payments on the interpreted comparison

A linear potential pays a fixed amount per message-digest query and per query in a second class.

Assume that every step keeps the potential in expectation.

Then the start potential bounds the expected payoff plus the payments.
-/

@[expose] public section

section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- The number of message-digest queries of a trace. -/
noncomputable def digestCount (entries : List (Entry D)) : ℕ :=
  (entries.filter fun entry => match entry with
    | .inl input => decide (tg.digest input)
    | .inr _ => false).length

omit [Params] [Fintype ι] [SampleableType R] in
theorem digestCount_append (first second : List (Entry D)) :
    digestCount tg (first ++ second) = digestCount tg first + digestCount tg second := by
  simp [digestCount, List.filter_append]

/-- The expected final payoff of a state, once its unexposed coordinates are completed. -/
noncomputable def endValue (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞)
    (state : DebtState D R ι) :
    ℝ≥0∞ :=
  ∑' table, Pr{let x ← completion state.known}[x = table] * payoff table state

end SphincsSecurity.Security.HiddenDebt

end

section

/-!
### A potential with two payments

The first payment is a fixed amount per message-digest query.

The second is a fixed amount per query whose input lies in a second class, fresh or cached.

The FORS leaf inputs are meant to form that class.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- The number of queries of a trace whose input lies in the class. -/
noncomputable def fleafCount (IsFleaf : D → Prop) (entries : List (Entry D)) : ℕ :=
  (entries.filter fun entry => match entry with
    | .inl input => decide (IsFleaf input)
    | .inr _ => false).length

theorem fleafCount_append (IsFleaf : D → Prop) (first second : List (Entry D)) :
    fleafCount IsFleaf (first ++ second) = fleafCount IsFleaf first +
        fleafCount IsFleaf second := by
  simp [fleafCount, List.filter_append]

@[simp]
theorem fleafCount_nil (IsFleaf : D → Prop) : fleafCount IsFleaf ([] : List (Entry D)) = 0 := rfl

@[simp]
theorem fleafCount_cons_inr (IsFleaf : D → Prop) (amount : ℕ) (entries : List (Entry D)) :
    fleafCount IsFleaf (.inr amount :: entries) = fleafCount IsFleaf entries := by
  simp [fleafCount]

theorem fleafCount_cons_inl (IsFleaf : D → Prop) (input : D) (entries : List (Entry D)) :
    (fleafCount IsFleaf (.inl input :: entries) : ℝ≥0∞) =
      (if IsFleaf input then 1 else 0) + fleafCount IsFleaf entries := by
  by_cases h : IsFleaf input
  · simp [fleafCount, h, add_comm]
  · simp [fleafCount, h]

theorem fleafCount_recorded_inl (IsFleaf : D → Prop) (input : D) :
    (fleafCount IsFleaf (recorded (D := D) (R := R) (ι := ι) (.inl (.inr (.inl input)))) : ℝ≥0∞) =
      if IsFleaf input then 1 else 0 := by
  change (fleafCount IsFleaf [.inl input] : ℝ≥0∞) = _
  have h := fleafCount_cons_inl IsFleaf input []
  simpa using h

/-- Steps other than ordinary queries record no input of the class. -/
theorem fleafCount_recorded_eq_zero (IsFleaf : D → Prop) (input : (SourceCostSpec D R ι).Domain)
    (h : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬IsFleaf bytes) :
    fleafCount IsFleaf (recorded input) = 0 := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · rfl
  · have hb := h bytes rfl
    simp [fleafCount, recorded, hb]
  · rfl
  · simp [fleafCount, recorded]

/-- Interpreted runs lose no mass. -/
theorem interp_mass {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (state : DebtState D R ι) :
    ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] = 1 := by
  simp

/-- A linear potential with two payments bounds the interpreted run.

Take a step within the budget, from a state with the invariant.

The step must keep the potential in expectation, with both payments.

The steps must keep the invariant.

At each state with the invariant, the potential must bound the final payoff.

Then the start potential bounds the expected final payoff plus all payments of the run. -/
theorem interp_potential2 {α : Type} (IsFleaf : D → Prop) (Inv : DebtState D R ι → Prop)
    (Φ : ℕ → DebtState D R ι → ℝ≥0∞) (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞)
    (pay pay2 : ℝ≥0∞)
    (hfinal : ∀ budget state, Inv state → endValue payoff state ≤ Φ budget state)
    (hstep : ∀ (input : (SourceCostSpec D R ι).Domain) budget state, Inv state → sourceCost input ≤
        budget →
      ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ
          (budget - sourceCost input) result.2 +
        pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input) ≤
            Φ budget state)
    (hinv : ∀ input state, Inv state → ∀ result ∈ support (costStep model input state),
        Inv result.2)
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget state, Inv state →
      ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] *
        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 *
            fleafCount IsFleaf out.1.2.2.1) ≤
          Φ budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hstate
      rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
      simpa [digestCount, fleafCount] using hfinal budget state hstate
  | query_bind input next ih =>
      intro budget state hstate
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [OracleComp.tsum_prEvent_bind_mul]
        set c : ℝ≥0∞ := pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf
            (recorded input)
          with hc
        calc ∑' result, Pr{let x ← costStep model input state}[x = result] *
              ∑' out, Pr{let x ← ((fun out => ((out.1.1, revealed input ++ out.1.2.1,
                  recorded input ++ out.1.2.2.1, touch tg initial state input ++ out.1.2.2.2),
                      out.2)) <$>
                interp tg initial model (next result.1)
                    (budget - sourceCost input) result.2)}[x = out] *
                (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 *
                    fleafCount IsFleaf out.1.2.2.1)
            ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] *
                (Φ (budget - sourceCost input) result.2 + c) := by
              refine ENNReal.tsum_le_tsum fun result => ?_
              by_cases hr : result ∈ support (costStep model input state)
              · refine mul_le_mul_right ?_ _
                rw [OracleComp.tsum_prEvent_map_mul]
                simp only [digestCount_append, fleafCount_append, Nat.cast_add]
                calc ∑' out, Pr{let x ← (interp tg initial model (next result.1)
                    (budget - sourceCost input)
                        result.2)}[x = out] *
                      (endValue payoff out.2 + pay * ((digestCount tg (recorded input) : ℝ≥0∞) +
                        digestCount tg out.1.2.2.1) + pay2 *
                            ((fleafCount IsFleaf (recorded input) : ℝ≥0∞) +
                        fleafCount IsFleaf out.1.2.2.1))
                    = ∑' out, Pr{let x ← (interp tg initial model (next result.1)
                        (budget - sourceCost input)
                          result.2)}[x = out] *
                        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                          pay2 * fleafCount IsFleaf out.1.2.2.1) +
                      (∑' out, Pr{let x ← (interp tg initial model (next result.1)
                        (budget - sourceCost input) result.2)}[x = out]) * c := by
                      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                      refine tsum_congr fun out => ?_
                      rw [hc]
                      ring
                  _ ≤ Φ (budget - sourceCost input) result.2 + 1 * c :=
                      add_le_add (ih result.1 _ _ (hinv input state hstate result hr))
                        (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
                  _ = _ := by rw [one_mul]
              · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
          _ = ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ
              (budget - sourceCost input) result.2 +
                (∑' result, Pr{let x ← costStep model input state}[x = result]) * c := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              refine tsum_congr fun result => ?_
              ring
          _ ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ
              (budget - sourceCost input) result.2 +
                1 * c := add_le_add le_rfl (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
          _ ≤ _ := by
              rw [one_mul, hc, ← add_assoc]
              exact hstep input budget state hstate hcost
      · rw [OracleComp.tsum_prEvent_pure_mul]
        simpa [digestCount, fleafCount] using hfinal budget state hstate

end SphincsSecurity.Security.HiddenDebt

end
