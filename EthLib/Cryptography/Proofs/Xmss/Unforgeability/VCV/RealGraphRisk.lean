module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphPresence
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphCap

/-!
# Conflict and off-path collisions along the current capped source

Refused outputs retain all ordinary inputs accumulated before refusal.

The same physical budget bounds the event on those paths and on paths returning a signature.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec HashSig SecretEncoding.Residual TwoLayerGraph
  CanonicalGraph.PairedQueries
open ChainGraph (Word Public)
open scoped Classical ENNReal

private abbrev rowEquality : DecidableEq Row := inferInstance

private theorem risk {α : Type} (pp : PublicParam) (limit : Nat)
    (body : OracleComp (Public.withLabels Start Row Word) α)
    (paid : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl body).run ((∅, ∅), [])),
      (TwoLayerGraph.physicalInputs z.2.1.1).encard ≤ limit ∧ PairedPresence z.2.1) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) body}[
      (graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1] ≤ (limit : ℝ≥0∞) / 2 ^ 127 := by
  let counted := (fun a => (a, limit)) <$> body
  have accounted : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl counted).run ((∅, ∅), [])),
      (TwoLayerGraph.physicalInputs z.2.1.1).encard ≤ z.1.2 ∧ PairedPresence z.2.1 := by
    rintro z hz
    simp only [counted, simulateQ_map, StateT.run_map, support_map] at hz
    obtain ⟨w, supported, rfl⟩ := hz
    exact paid w supported
  have hit := prEvent_hash_graph_bad pp counted (fun a => pure a) accounted limit
  have tail : afterSetup PairedHashWord.halves counted (fun a => pure a) = counted := by
    simp [afterSetup, meteredCaller]
  rw [tail] at hit
  simpa [counted, CanonicalGraph.deferredFillDraw, prEvent_norm] using hit

/-- The original capped caller after the parameter prefix, before the graph draws any pending cells.
-/
@[expose] noncomputable def cappedBranch (A : Adversary) (left : Nat) (w : HashOutput) :=
  let pp := parameterOfWord w
  liftComp (residualProgram pp (WeightedCap.capCompOpt paidFee left (continuation A pp))
    (localState _ _ (toKeyedState pp (afterWord w))))
    (Public.withLabels Start Row Word)

attribute [local irreducible] continuation

/-- The graph uses the sampled parameter.

Its collision bound charges each remaining physical call once, even on runs stopped by the cap.
-/
theorem prEvent_capped_graph_bad (A : Adversary) (left : Nat) (w : HashOutput) :
    let pp := parameterOfWord w
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (cappedBranch A left w)}[
      (graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1] ≤ (left : ℝ≥0∞) / 2 ^ 127 := by
  intro pp
  apply risk
  rintro ⟨⟨obs, extra⟩, st, pending⟩ reached
  let cold := localState _ _ (toKeyedState pp (afterWord w))
  let body := WeightedCap.capCompOpt paidFee left (continuation A pp)
  have dec : rowEquality = (fun a b => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  change ((obs, extra), st, pending) ∈ support ((simulateQ
    (@CanonicalGraph.deferredImpl _ _ _ _ _ (graph pp) _ _ rowEquality _ _)
    (liftComp (residualProgram pp body cold) (Public.withLabels Start Row Word))).run
      ((∅, ∅), [])) at reached
  rw [dec] at reached
  exact ⟨(Footprint.actual_deferred A left w obs extra st pending reached).2,
    Footprint.deferred_present pp body cold st pending obs extra reached⟩

/-- The unnormalized physical caller can read public halves and private starts, never a lazy touch.

Filling the resulting empty pending list therefore leaves the final eager state intact.
-/
private theorem filled_source {K α : Type} [dk : DecidableEq K]
    (g : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (body : OracleComp ChainWorld α) :
    g.deferredFillDraw (pure ()) (liftComp body
      (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits))) =
      (fun z => ((z.1, z.2, ([] : List (StartKey ⊕ K))), z.2, ())) <$>
      (simulateQ g.relabelImpl body).run (∅, ∅) := by
  have eq : dk = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dk
  rw [CanonicalGraph.deferredFillDraw, Footprint.deferred_lift]
  simp [bind_map_left, bind_pure_comp]

/-- The numerical bound applies directly to the same eager graph in the keyed-advantage reduction.

Both refused and returned paths are included.
-/
theorem prEvent_graphRun_bad (A : Adversary) (left : Nat) (w : HashOutput) :
    let pp := parameterOfWord w
    Pr{let z ← graphRun A left w}[(graph pp).Conflict z.2 ∨ OffPath pp z.2] ≤
      (left : ℝ≥0∞) / 2 ^ 127 := by
  intro pp
  let body := residualProgram pp (WeightedCap.capCompOpt paidFee left (continuation A pp))
    (localState _ _ (toKeyedState pp (afterWord w)))
  let world := Public.withLabels Start Row Word
  have riskBound : Pr{let z ← (graph pp).deferredFillDraw (pure ()) (liftComp body world)}[
      (graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1] ≤ _ := prEvent_capped_graph_bad A left w
  rw [filled_source (graph pp) body] at riskBound
  unfold graphRun runGraph evaluate
  have dec : rowEquality = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  change Pr{let z ← (simulateQ (@CanonicalGraph.eagerImpl _ _ _ _ _ (graph pp) _ _
    (fun a b => Classical.propDecidable (a = b)) _ _) (liftComp body world)).run (∅, ∅)}[
    (graph pp).Conflict z.2 ∨ OffPath pp z.2] ≤ _
  rw [← dec, (graph pp).simulateQ_eagerImpl_liftComp]
  simpa only [prEvent_norm, Functor.map_map] using riskBound

/-- It remains to bound accepted graph runs that avoid conflicts and off-path collisions. -/
theorem forge_le_clean (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (budget : HasHashQueryBound A (left + 2))
    (good : ∀ w : HashOutput, let pp := parameterOfWord w
      Pr{let z ← graphRun A left w}[accepted z.1.1 ∧
        ¬((graph pp).Conflict z.2 ∨ OffPath pp z.2)] ≤ bound) :
    forgeAdvantage A ≤ bound + (left : ℝ≥0∞) / 2 ^ 127 +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply forge_le_graph A left _ budget
  intro w
  let pp := parameterOfWord w
  let bad := fun z : GraphPrefix.GraphState => (graph pp).Conflict z ∨ OffPath pp z
  refine (prEvent_mono_of_support (graphRun A left w) _ (fun z =>
    (accepted z.1.1 ∧ ¬bad z.2) ∨ bad z.2) ?_).trans ?_
  · intro z _ h
    by_cases hb : bad z.2
    · exact Or.inr hb
    · exact Or.inl ⟨h.resolve_right (fun c => hb (Or.inl c)), hb⟩
  · exact (prEvent_or_le _ _ _).trans (add_le_add (good w) (prEvent_graphRun_bad A left w))

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
