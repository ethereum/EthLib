module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Proofs: a bad event that only a new table entry can cause

A stateful oracle keeps a table, and a step adds at most one entry to it.

From a good state, a step either keeps the size and stays good, or adds one entry.

A step that adds an entry turns bad with probability at most `ε`.

Then a run that ends with at most `n` entries ends bad with probability at most `(n - k) * ε`.

Here `k` is the size at the start, from a good state.

This is the union bound over the entries that the run adds.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleComp OracleSpec ENNReal

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- The steps of `impl` never shrink `size`, and only a step that adds one to it turns bad.

From a good state, a step keeps `size` and stays good, or adds one to `size`.

In the second case, it turns bad with probability at most `ε`. -/
structure BadOnGrowth (impl : QueryImpl spec (StateT σ ProbComp)) (size : σ → ℕ)
    (bad : σ → Prop) (ε : ℝ≥0∞) : Prop where
  /-- No step shrinks the size. -/
  mono : ∀ t s, ∀ z ∈ support ((impl t).run s), size s ≤ size z.2
  /-- From a good state, a step stays good at the same size, or grows by one.

  A step that grows turns bad with probability at most `ε`. -/
  step : ∀ t s, ¬bad s →
    (∀ z ∈ support ((impl t).run s), size z.2 = size s ∧ ¬bad z.2) ∨
      ((∀ z ∈ support ((impl t).run s), size z.2 = size s + 1) ∧
        Pr{let z ← (impl t).run s}[bad z.2] ≤ ε)

/-- No run of a handler that never shrinks the size ends smaller than it starts. -/
theorem BadOnGrowth.le_size_of_mem_support {impl : QueryImpl spec (StateT σ ProbComp)}
    {size : σ → ℕ} {bad : σ → Prop} {ε : ℝ≥0∞} (h : BadOnGrowth impl size bad ε) {α : Type}
    (oa : OracleComp spec α) (s : σ) :
    ∀ z ∈ support ((simulateQ impl oa).run s), size s ≤ size z.2 :=
  simulateQ_run_preservesInv impl (fun st ↦ size s ≤ size st)
    (fun t s₀ hs₀ z hz ↦ hs₀.trans (h.mono t s₀ z hz)) oa s le_rfl

/-- **The union bound over new entries.**

Take a run from a good state of size `k`, which always ends with at most `n` entries.

It ends bad with probability at most `(n - k) * ε`. -/
theorem BadOnGrowth.prEvent_bad_le {impl : QueryImpl spec (StateT σ ProbComp)} {size : σ → ℕ}
    {bad : σ → Prop} {ε : ℝ≥0∞} (h : BadOnGrowth impl size bad ε) {α : Type}
    (oa : OracleComp spec α) (s : σ) (hs : ¬bad s) {n : ℕ}
    (hn : ∀ z ∈ support ((simulateQ impl oa).run s), size z.2 ≤ n) :
    Pr{let z ← (simulateQ impl oa).run s}[bad z.2] ≤ ((n - size s : ℕ) : ℝ≥0∞) * ε := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    simp [hs]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hn ⊢
    rcases h.step t s hs with hstay | ⟨hgrow, hε⟩
    · refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz ↦ ?_
      have hz' := hstay z hz
      rw [← hz'.1]
      exact ih z.1 z.2 hz'.2 fun w hw ↦ hn w ((mem_support_bind_iff _ _ _).2 ⟨z, hz, hw⟩)
    · obtain ⟨z, hz⟩ := support_nonempty ((impl t).run s)
      obtain ⟨w, hw⟩ := support_nonempty ((simulateQ impl (k z.1)).run z.2)
      have hle : size s + 1 ≤ n := by
        rw [← hgrow z hz]
        exact (h.le_size_of_mem_support _ _ w hw).trans
          (hn w ((mem_support_bind_iff _ _ _).2 ⟨z, hz, hw⟩))
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z ↦ bad z.2) _
        (ε := ((n - (size s + 1) : ℕ) : ℝ≥0∞) * ε) fun z hz hbz ↦ ?_).trans ?_
      · rw [← hgrow z hz]
        exact ih z.1 z.2 hbz fun w hw ↦ hn w ((mem_support_bind_iff _ _ _).2 ⟨z, hz, hw⟩)
      · calc _ ≤ ε + ((n - (size s + 1) : ℕ) : ℝ≥0∞) * ε := add_le_add_left hε _
          _ = ((n - size s : ℕ) : ℝ≥0∞) * ε := by
            rw [show n - size s = (n - (size s + 1)) + 1 by omega]
            push_cast; ring

end EthLib.Cryptography
