module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedTariff

/-!
# Charging message trials and graph addresses in the same deferred state

Both graph halves and both message-trial charges can use the same physical public budget.

The numerical statement requires a bound for each component on the indicated address class.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleSpec OracleComp HashSig TwoLayerGraph CanonicalGraph.PairedQueries
open ChainGraph (Word Public)
open scoped ENNReal

/-- The end fill preserves the exact ordinary table, even with pending honest touches on refusal. -/
theorem filled_classes {α S : Type} (pp : PublicParam) (left : Nat)
    (body : OracleComp (Mixed HashInput HashOutput Start Row Word) α) (draw : ProbComp S) {z}
    (reach : z ∈ support ((graph pp).deferredFillDraw draw (guardedGraph left body))) :
    (addressedInputs pp z.2.1.1).encard + (messageInputs pp z.2.1.1).encard +
      (seedInputs z.2.1.1).encard ≤ left := by
  obtain ⟨run, fill, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp reach
  rw [RelabelState.fst_eq_of_mem_support_endFill fill]
  exact (normalized_path pp left body run).1

/-- Each graph or message input incurs two 128-bit charges.

Each seed input incurs two 256-bit charges.

All three use the same physical budget. -/
theorem class_charge_le (pp : PublicParam) (c : Public.QueryCache) (q : Nat)
    (budget : (addressedInputs pp c).encard + (messageInputs pp c).encard +
      (seedInputs c).encard ≤ q) :
    2 * ((addressedInputs pp c).encard : ℝ≥0∞) / 2 ^ 128 +
      2 * ((messageInputs pp c).encard : ℝ≥0∞) / 2 ^ 128 +
      2 * ((seedInputs c).encard : ℝ≥0∞) / 2 ^ 256 ≤ (q : ℝ≥0∞) / 2 ^ 127 := by
  have inv : (2 ^ 256 : ℝ≥0∞)⁻¹ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    norm_num
  have h : (((addressedInputs pp c).encard + (messageInputs pp c).encard +
      (seedInputs c).encard : ℕ∞) : ℝ≥0∞) ≤ q := by
    exact_mod_cast budget
  simp only [ENat.toENNReal_add] at h
  simp only [div_eq_mul_inv]
  calc
    _ ≤ 2 * ((addressedInputs pp c).encard : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
        2 * ((messageInputs pp c).encard : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
        2 * ((seedInputs c).encard : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by gcongr
    _ = (2 * (2 ^ 128 : ℝ≥0∞)⁻¹) * (((addressedInputs pp c).encard : ℝ≥0∞) +
        ((messageInputs pp c).encard : ℝ≥0∞) + ((seedInputs c).encard : ℝ≥0∞)) := by ring
    _ ≤ (2 * (2 ^ 128 : ℝ≥0∞)⁻¹) * q := by gcongr
    _ = _ := by
      change _ = (q : ℝ≥0∞) / 2 ^ 127
      calc
        _ = (2 * q : ℝ≥0∞) / 2 ^ 128 := by rw [div_eq_mul_inv]; ring
        _ = _ := by
          rw [show (2 : ℝ≥0∞) ^ 128 = 2 * 2 ^ 127 by rw [pow_succ, mul_comm],
            ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
