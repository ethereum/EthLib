module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerGraph
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PairedGame
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.ProjectedHits

/-!
# Off-path hash hits within the recorded leanXMSS budget

The leanXMSS draft counts each full hash query in its "Security" section.

The two layers share a cache and a counter for the original caller.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open HashSig OracleComp OracleSpec Constants
open CanonicalGraph.PairedQueries
open scoped ENNReal

/-- Expanding the virtual rows executes the paired game caller with the original cost. -/
theorem meteredCaller_eq {α : Type} (p : OracleComp XmssSecurity.OracleWorld α) :
    meteredCaller (X := Start) (K := Row) PairedHashWord.halves p =
      simulateQ liftPublic (simulateQ PairedHashWord.readHalves (PairedGame.meter p)) := by
  have same : rawCost (L := HashInput) = PairedGame.physicalCharge := by
    funext t
    cases t <;> rfl
  simp only [meteredCaller, PairedGame.meter, PairedHashWord.readHalves, same]

/-- A paid graph setup followed by any adaptive leanXMSS caller has one bound for both layers.

The event includes only runs whose original charge, including setup, is at most q. -/
theorem prEvent_offPath_and_cost (pp : PublicParam) {α β : Type}
    (setup : OracleComp (ChainGraph.Public.withLabels Start Row ChainGraph.Word) (β × Nat))
    (p : β → OracleComp XmssSecurity.OracleWorld α)
    (paid : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl setup).run ((∅, ∅), [])),
      (physicalInputs z.2.1.1).encard ≤ z.1.2) (q : Nat) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (afterSetup PairedHashWord.halves setup p)}[
      OffPath pp z.2.1 ∧ z.1.1.2 ≤ q] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  have bound := prEvent_hit_afterSetup_and_cost (graph pp) PairedHashWord.halves (lowKeys pp)
    (fun _ => rfl) setup p paid q
  have card : (Nat.card ChainGraph.Word : ℝ≥0∞) = 2 ^ 128 := by
    rw [Nat.card_eq_fintype_card]
    norm_num [ChainGraph.Word, digestBits]
  rw [card] at bound
  exact (prEvent_mono _ _ _ fun z h => ⟨projected_of_offPath pp z.2.1 h.1, h.2⟩).trans bound

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
