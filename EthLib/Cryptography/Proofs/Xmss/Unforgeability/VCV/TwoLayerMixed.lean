module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerPaid
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Mixed

/-!
# Interleaved public and private queries in the two-layer graph

Only a public hash can add an ordinary cache entry.
The graph can derive private starts and read or touch its nodes between any two public calls.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open HashSig OracleComp OracleSpec Constants
open ChainGraph (Public Word)
open CanonicalGraph.PairedQueries
open scoped ENNReal

/-- An adaptive caller can interleave private start derivations, label operations and full hashes.
The bound uses its total recorded charge on the same execution as the bad event. -/
theorem prEvent_mixed_hash_graph_bad (pp : PublicParam) {α : Type}
    (cost : (Internal Start Row Word).Domain → Nat)
    (body : OracleComp (Mixed HashInput HashOutput Start Row Word) α) (q : Nat) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (runMixed PairedHashWord.halves cost body)}[
      ((graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1) ∧ z.1.1.2 ≤ q] ≤ (q : ℝ≥0∞) / 2 ^ 127 := by
  let setup := runMixed PairedHashWord.halves cost body
  have paid : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl setup).run ((∅, ∅), [])),
      (physicalInputs z.2.1.1).encard ≤ z.1.2 ∧ PairedPresence z.2.1 := by
    intro z hz
    constructor
    · have count := mixed_footprint (graph pp) PairedHashWord.halves cost body ((∅, ∅), []) z hz
      simpa [CanonicalGraph.PairedQueries.physicalInputs, physicalInputs] using count
    · exact mixed_present (graph pp) PairedHashWord.halves cost body ((∅, ∅), [])
        (by simp [PresentTogether]) (ready_pair pp) z hz
  have bound := prEvent_hash_graph_bad pp setup (fun a => pure a) paid q
  have tail : afterSetup PairedHashWord.halves setup (fun a => pure a) = setup := by
    simp [afterSetup, meteredCaller]
  rw [tail] at bound
  exact bound

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
