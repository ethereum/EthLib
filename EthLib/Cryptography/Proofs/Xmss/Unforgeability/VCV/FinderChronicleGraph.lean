module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChronicleGame

/-!
# Graph events on the same chronological execution as the signing searches

Both graph rows arise from one physical input.

The addressed-input budget covers a conflict or projected target collision after filling.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open Constants HashSig OracleSpec OracleComp CachedCodeword TrialGraphWatch TwoLayerGraph
open scoped ENNReal Classical

/-- Forget chronology while retaining all ordinary and labeled rows, including pending labels. -/
theorem project_graph (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp) :
    (fun z => (z.1, (counters z.2).1.1.1)) <$> chronicleGame pp A left r =
      (simulateQ (graph pp).deferredImpl (guardedGraph left ((mixedGame pp A).run r))).run
        ((∅,∅),[]) := by
  let p := WeightedCap.capCompOpt fee left ((game pp A).run r)
  have run := erase_run pp register (fun s b => (target pp s b).isSome) left
    (fun w => (digits w).isSome)
    p (counters initial)
  have view := project_counts pp left p initial
  unfold p at run view
  rw [erase_capped_game] at run
  rw [← view] at run
  simpa only [chronicleGame, guardedGraph, initial, counters, id_eq, Functor.map_map,
    Function.comp_def, Prod.map] using run

/-- The physical guard preserves the enriched caller's output and filled graph. -/
theorem project_graphFill (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp) :
    (fun z => ((z.1.1, (counters z.1.2).1.1.1), z.2, ())) <$> chronicleFill pp A left r =
      (graph pp).deferredFillDraw (pure ()) (guardedGraph left ((mixedGame pp A).run r)) := by
  have view := project_filled pp A left r register (fun s b => (target pp s b).isSome)
    left (fun w => (digits w).isSome) (fun _ => none)
  rw [← project_chronicleFill] at view
  simpa only [Functor.map_map, Function.comp_def] using view

private theorem raw_hazards {α : Type} (pp : PublicParam) (left : Nat)
    (p : OracleComp TrialGraphWatch.Raw α) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left p)}[
      (graph pp).Conflict z.2.1 ∨
      (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2.1)] ≤
      mean ((simulateQ (graph pp).deferredImpl (guardedGraph left p)).run ((∅, ∅), []))
        (fun z => (addressedInputs pp z.2.1.1).encard) / 2 ^ 127 := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans (raw_low_price pp left p)
  rintro z hz (hit | off)
  · obtain ⟨before, fill, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp hz
    have present := (normalized_path pp left p before).2
    have stable := RelabelState.fst_eq_of_mem_support_endFill fill
    have after : PairedPresence z.2.1 := by simpa only [PairedPresence, stable] using present
    exact Or.inl (lowConflict pp _ after hit)
  · exact Or.inr off

attribute [local irreducible] mixedGame graph guardedGraph simulateQ chronicleGame chronicleFill

/-- The final graph event charges the expected count of addressed chain, leaf and node inputs. -/
theorem chronological_graph_price (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp) :
    Pr{let z ← chronicleFill pp A left r}[(graph pp).Conflict z.2 ∨
      (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2)] ≤
      mean (chronicleGame pp A left r)
        (fun z => (addressedInputs pp (counters z.2).1.1.1.1.1).encard) / 2 ^ 127 := by
  have price := raw_hazards pp left ((mixedGame pp A).run r)
  rw [← project_graphFill, prEvent_map, ← project_graph] at price
  simpa only [mean, tsum_prEvent_map_mul] using price

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
