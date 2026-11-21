module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphTariff
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.MixedCap
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphRisk

/-!
# The selected physical cutoff on a normalized graph program

The program may touch cells, read nodes and request private starts without spending a public query.

A full public request, including a repeat, spends one unit before either row can run.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig OracleComp OracleSpec TwoLayerGraph CanonicalGraph.PairedQueries
open ChainGraph (Word Public)
open scoped ENNReal

/-- Expose the two-layer graph and keep the full public fee at the original request. -/
@[expose] noncomputable def guardedGraph {α : Type} (left : Nat)
    (p : OracleComp (Mixed HashInput HashOutput Start Row Word) α) :=
  simulateQ (expand PairedHashWord.halves)
    (WeightedCap.capCompOpt (mixedCost (H := Word) (F := HashOutput) (fun _ => 0)) left p)

/-- All three disjoint charges use one budget on the same potentially refused deferred run.

The pending list is arbitrary. -/
theorem normalized_path {α : Type} (pp : PublicParam) (left : Nat)
    (p : OracleComp (Mixed HashInput HashOutput Start Row Word) α) {z}
    (run : z ∈ support ((simulateQ (graph pp).deferredImpl (guardedGraph left p)).run ((∅, ∅),
      []))) :
    (addressedInputs pp z.2.1.1).encard + (messageInputs pp z.2.1.1).encard +
      (seedInputs z.2.1.1).encard ≤ left ∧
      PairedPresence z.2.1 := by
  have cost := capped_footprint (graph pp) PairedHashWord.halves (fun _ => 0) p left ((∅, ∅),
      []) run
  have both := capped_present (graph pp) PairedHashWord.halves (fun _ => 0) p left ((∅, ∅), [])
    (by simp [PresentTogether]) (ready_pair pp) run
  refine ⟨(joint_footprint pp z.2.1.1).trans ?_, both⟩
  simpa [CanonicalGraph.PairedQueries.physicalInputs, TwoLayerGraph.physicalInputs] using cost

/-- An additional terminal draw shares the bound with the graph's actual addressed footprint. -/
theorem normalized_joint {S α : Type} (pp : PublicParam) (left : Nat)
    (p : OracleComp (Mixed HashInput HashOutput Start Row Word) α) (ms : ProbComp S)
    (H : S → Footprint.State Row → Prop) (c : Public.QueryCache → ℝ≥0∞)
    (hc : ∀ st : Footprint.State Row, Pr{let s ← ms}[H s st] ≤ c st.1) (B : ℝ≥0∞) (finite : B ≠ ⊤) :
    Pr{let z ← (graph pp).deferredFillDraw ms (guardedGraph left p)}[
      ((graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1 ∨ H z.2.2 z.2.1) ∧
      2 * ((addressedInputs pp z.2.1.1).encard : ℝ≥0∞) / Nat.card Word + c z.2.1.1 ≤ B] ≤ B :=
  prEvent_addressed_joint pp ms H c hc _ (fun _ hz => (normalized_path pp left p hz).2) B finite

/-- Deferring the selected program charges the same conflict once, even on a refused path.

The caller may keep its signing history or its residual tables in the successful result. -/
theorem defer_selected {α : Type} (pp : PublicParam) (left : Nat)
    (p : OracleComp (Mixed HashInput HashOutput Start Row Word) α) (win : Option α → Prop) :
    Pr{let z ← (simulateQ (graph pp).eagerImpl (guardedGraph left p)).run (∅, ∅)}[
      win z.1 ∨ (graph pp).Conflict z.2] ≤
      Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left p)}[
        win z.1.1 ∨ (graph pp).Conflict z.2.1] := by
  have h := (graph pp).prEvent_eagerImpl_le_deferredImpl_empty (guardedGraph left p)
    (fun z => win z.1 ∨ (graph pp).Conflict z.2)
  simpa only [CanonicalGraph.deferredFillDraw, prEvent_norm, bind_pure_comp, Functor.map_map,
    or_assoc, or_self] using h

/-- Both graph hazards on normalized deferred paths, with no prior successful return required. -/
theorem normalized_graph_bad {α : Type} (pp : PublicParam) (left : Nat)
    (p : OracleComp (Mixed HashInput HashOutput Start Row Word) α) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left p)}[
      (graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1] ≤ (left : ℝ≥0∞) / 2 ^ 127 := by
  apply risk
  intro z hz
  have cost := capped_footprint (graph pp) PairedHashWord.halves (fun _ => 0) p left ((∅, ∅), []) hz
  refine ⟨?_, (normalized_path pp left p hz).2⟩
  simpa [CanonicalGraph.PairedQueries.physicalInputs, TwoLayerGraph.physicalInputs] using cost

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
