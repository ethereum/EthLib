module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerMixed
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSeedInputs

/-!
# A shared physical query bound for graph failures and seed guesses

The graph charges a low row only at a chain, leaf or node address.
A hidden seed guess uses an input outside that set.
Each paid public input therefore contributes at most twice the probability of guessing a digest.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open HashSig OracleComp OracleSpec
open ChainGraph (Public Word)
open CanonicalGraph.PairedQueries
open scoped ENNReal

private theorem total_charge (pp : PublicParam) (c : Public.QueryCache) :
    2 * ((addressedInputs pp c).encard : ℝ≥0∞) / Nat.card Word +
      2 * (2 ^ 256 : ℝ≥0∞)⁻¹ * ((seedInputs c).encard : ℝ≥0∞) ≤
      2 * ((physicalInputs c).encard : ℝ≥0∞) / 2 ^ 128 := by
  have card : Nat.card Word = 2 ^ 128 := by
    rw [Nat.card_eq_fintype_card]
    norm_num [Word, digestBits]
  have split := Set.encard_sdiff_add_encard_of_subset (addressed_subset pp c)
  have units : (2 ^ 256 : ℝ≥0∞)⁻¹ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    norm_num
  have subset := Set.encard_le_encard (seedInputs_subset_other pp c)
  rw [card, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ ≤ 2 * ((addressedInputs pp c).encard : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
        2 * (2 ^ 128 : ℝ≥0∞)⁻¹ * ((otherInputs pp c).encard : ℝ≥0∞) := by gcongr
    _ = 2 * ((physicalInputs c).encard : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      rw [← split, ENat.toENNReal_add]
      unfold otherInputs
      ring

/-- The two-layer graph and both independent seed guesses fit in the same observed query budget. -/
theorem prEvent_graph_or_seed_and_cost (pp : PublicParam) {α : Type}
    (cost : (Internal Start Row Word).Domain → Nat)
    (body : OracleComp (Mixed HashInput HashOutput Start Row Word) α) (q : Nat) :
    Pr{let z ← (graph pp).deferredFillDraw drawSeeds (runMixed PairedHashWord.halves cost body)}[
      ((graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1 ∨ SeedGuess z.2.1.1 z.2.2) ∧
        z.1.1.2 ≤ q] ≤ (q : ℝ≥0∞) / 2 ^ 127 := by
  classical
  let f := subgraph pp
  let nk := keys pp
  have empty : ¬((lowGraph pp).Conflict (f.project (∅, ∅)) ∨ nk.TCHazard (f.project (∅, ∅))) := by
    change ¬((lowGraph pp).Conflict (∅, ∅) ∨ nk.TCHazard (∅, ∅))
    exact not_or.mpr ⟨(lowGraph pp).not_conflict_empty, CanonicalGraph.NodeKeys.not_tcHazard_empty⟩
  have charged := (f.isCharged nk.isCharged).prEvent_deferredFillDraw_and_le empty
    (fun c => 2 * ((addressedInputs pp c).encard : ℝ≥0∞) / Nat.card Word)
    (potential_le_addressed pp) drawSeeds (fun s st => SeedGuess st.1 s)
    (fun c => 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ * ((seedInputs c).encard : ℝ≥0∞))
    (fun st => prEvent_seedGuess st.1) (runMixed PairedHashWord.halves cost body)
    ((q : ℝ≥0∞) / 2 ^ 127) (by finiteness)
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) charged
  rintro z hz ⟨bad, budget⟩
  obtain ⟨before, filled, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp hz
  have stable := RelabelState.fst_eq_of_mem_support_endFill filled
  constructor
  · rcases bad with conflict | off | seed
    · have present := mixed_present (graph pp) PairedHashWord.halves cost body ((∅, ∅), [])
          (by simp [PresentTogether]) (ready_pair pp) _ before
      exact Or.inl (Or.inl (lowConflict pp _ (by simpa only [PresentTogether, PairedPresence, stable] using present) conflict))
    · exact Or.inl (Or.inr (lowCollision pp _ off))
    · exact Or.inr seed
  · apply (total_charge pp _).trans
    rw [stable, show (2 : ℝ≥0∞) ^ 128 = 2 * 2 ^ 127 by rw [pow_succ, mul_comm],
      ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
    have count := mixed_footprint (graph pp) PairedHashWord.halves cost body ((∅, ∅), []) _ before
    have bounded : (physicalInputs z.1.2.1.1).encard ≤ (q : ℕ∞) := by
      apply le_trans _ (Nat.cast_le.mpr budget)
      simpa [physicalInputs, CanonicalGraph.PairedQueries.physicalInputs] using count
    gcongr
    exact_mod_cast bounded

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
