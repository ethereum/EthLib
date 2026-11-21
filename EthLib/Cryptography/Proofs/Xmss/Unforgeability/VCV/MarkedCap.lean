module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSource
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphFootprint
public import VCVio.OracleComp.QueryTracking.WeightedCap.Domination

/-!
# A single comparison from the native physical cutoff to the marked cutoff

The native tariff charges the same full word once whether it is marked or unmarked.

The selected tariff charges only the marked port.

A conflict survives either cutoff, even when the two callers stop at different times.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec HashSig SecretEncoding.Residual
open scoped Classical ENNReal

/-- Forget which phase requested a full word. -/
@[expose] def physicalIndex : Marked.Domain → Source.Domain
  | .inl t => t
  | .inr b => .inl (.inr (.inl b))

abbrev tightFee (t : Marked.Domain) := paidFee (physicalIndex t)

@[expose] def selectedFee : Marked.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

theorem selected_le (t : Marked.Domain) : selectedFee t ≤ tightFee t := by
  rcases t with t | b
  · exact Nat.zero_le _
  · rfl

/-- Forgetting phase tags commutes with charging all original native operations. -/
theorem cap_erase {α : Type} (p : OracleComp Marked α) (q : Nat) :
    simulateQ eraseMark (WeightedCap.capCompOpt tightFee q p) =
      WeightedCap.capCompOpt paidFee q (simulateQ eraseMark p) := by
  let reply : ∀ t : Marked.Domain, Source.Range (physicalIndex t) → Marked.Range t :=
    fun t => match t with | .inl _ => id | .inr _ => id
  have same : (fun t => reply t <$> (liftM (Source.query (physicalIndex t)) :
      OracleComp Source (Source.Range (physicalIndex t)))) = eraseMark := by
    funext t
    rcases t with t | b <;> simp [reply, physicalIndex, eraseMark]
  have law := WeightedCap.simulateQ_capCompOpt_single_query tightFee paidFee physicalIndex reply
    (fun _ => rfl) p q
  rwa [same] at law

open Classical in
private theorem conflict_step {K : Type}
    (g : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (pp : PublicParam) :
    ((Footprint.step g pp) ∘ₛ eraseMark).PreservesInv (fun s => g.Conflict s.2) := by
  have physical : (Footprint.step g pp).PreservesInv (fun s => g.Conflict s.2) := by
    rintro t ⟨l, s⟩ bad z reached
    simp only [Footprint.step, StateT.run_mk, support_map] at reached
    obtain ⟨w, hw, rfl⟩ := reached
    exact simulateQ_run_preservesInv _ g.Conflict g.preservesInv_conflict_relabelImpl _ s bad w hw
  rintro (t | b) initial bad z reached
  · exact physical t initial bad z (by simpa [QueryImpl.compose, eraseMark] using reached)
  · exact physical (.inl (.inr (.inl b))) initial bad z
      (by simpa [QueryImpl.compose, eraseMark] using reached)

open Classical in
private theorem graph_event {K α : Type}
    (g : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (pp : PublicParam) (p : OracleComp Marked α) (extra : ResidualCache pp)
    (win : α → Prop) :
    Pr{let z ← evaluate pp g (simulateQ eraseMark p) extra (∅, ∅)}[win z.1.1 ∨ g.Conflict z.2] =
      Pr{let z ← (simulateQ (Footprint.step g pp ∘ₛ eraseMark) p).run (extra,
        ∅, ∅)}[win z.1 ∨ g.Conflict z.2.2] := by
  unfold evaluate
  rw [g.simulateQ_eagerImpl_liftComp, Footprint.source_eq, Footprint.run_step,
    QueryImpl.simulateQ_compose]
  simp only [prEvent_norm, Functor.map_map]

/-- The selected cutoff is applied to each full native query before row expansion. -/
@[expose] noncomputable def markedRun (A : Adversary) (left : Nat) (w : HashOutput) :=
  let pp := parameterOfWord w
  runGraph pp (TwoLayerGraph.graph pp)
    (simulateQ eraseMark (WeightedCap.capCompOpt selectedFee left (markedContinuation A pp)))
    (afterWord w)

attribute [local irreducible] continuation markedContinuation

/-- The real forge advantage is bounded by one graph event in the selected operational cutoff.

No independent native-conflict term is added in passing from the original stricter cap. -/
theorem forge_le_marked (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2))
    (each : ∀ w : HashOutput, let pp := parameterOfWord w
      Pr{let z ← markedRun A left w}[accepted z.1.1 ∨ (TwoLayerGraph.graph pp).Conflict z.2] ≤
        bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply forge_le_graph A left _ bounded
  intro w
  let pp := parameterOfWord w
  let g := TwoLayerGraph.graph pp
  let extra := localState _ _ (toKeyedState pp (afterWord w))
  let term := markedContinuation A pp
  let native := WeightedCap.capCompOpt tightFee left term
  let monitored := WeightedCap.capCompOpt selectedFee left term
  have erase : simulateQ eraseMark native =
      WeightedCap.capCompOpt paidFee left (continuation A pp) := by
    rw [cap_erase, erase_continuation]
  have dominant := WeightedCap.prEvent_cap_le_cap_of_preserves
    (Footprint.step g pp ∘ₛ eraseMark) tightFee selectedFee selected_le
    (fun s => g.Conflict s.2) (conflict_step g pp) (fun z _ => wins z = true) term left left le_rfl
    (extra, (∅, ∅))
  have accept : ∀ z : Option Outcome, z.elim False (fun k => wins k = true) = accepted z := by
    intro z; cases z <;> rfl
  simp only [accept] at dominant
  have compare := (graph_event g pp native extra accepted).le.trans (dominant.trans
    (graph_event g pp monitored extra accepted).symm.le)
  change Pr{let z ← (evaluate pp g (WeightedCap.capCompOpt paidFee left
    (continuation A pp)) extra (∅, ∅))}[accepted z.1.1 ∨ g.Conflict z.2] ≤ bound
  rw [← erase]
  exact compare.trans (each w)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
