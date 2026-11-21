module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphErase
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Expected charges in the observed graph game

Every expected cost is taken over the same distribution of completed and stopped runs.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch

open HashSig OracleComp OracleSpec TwoLayerGraph
open scoped ENNReal

/-- Mean of a terminal charge, including the state of refused requests. -/
@[expose] noncomputable def mean {α : Type} (m : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' z, Pr{let u ← m}[u = z] * f z

private theorem mean_add {α : Type} (m : ProbComp α) (f g : α → ℝ≥0∞) :
    mean m f + mean m g = mean m (fun z => f z + g z) := by
  simp only [mean, mul_add, tsum_add]

private theorem mean_le {α : Type} (m : ProbComp α) (f : α → ℝ≥0∞) (q : ℝ≥0∞)
    (bound : ∀ z ∈ support m, f z ≤ q) : mean m f ≤ q := by
  classical
  have mass := tsum_prEvent_mul_of_const_on_support m (f := fun _ => q) (fun _ _ => rfl)
  rw [← mass]
  apply tsum_le_tsum
  intro z
  by_cases present : z ∈ support m
  · exact mul_le_mul_of_nonneg_left (bound z present) zero_le
  · simp [prEvent_eq_zero_of_not_mem_support m present]

/-- Graph, registered, unregistered and seed charges use one expected physical budget. -/
theorem expected_budget {Note R α : Type} (pp : PublicParam) (notice : Note → R → R)
    (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool)
    (body : OracleComp (Spec Note) α) (left : Nat) (reg : R) :
    let m := (simulateQ (observe pp notice registered q test)
      (WeightedCap.capCompOpt fee left body)).run (((((∅, ∅), []), reg), 0), 0, 0)
    mean m (fun z => (addressedInputs pp z.2.1.1.1.1.1).encard) +
      (mean m (fun z => z.2.1.2) + mean m (fun z => z.2.2.1)) +
      mean m (fun z => (seedInputs z.2.1.1.1.1.1).encard) ≤ left := by
  intro m
  rw [mean_add m (fun z => z.2.1.2) (fun z => z.2.2.1), mean_add, mean_add]
  apply mean_le
  intro z hz
  exact_mod_cast total_budget pp notice registered q test body left reg hz

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch
