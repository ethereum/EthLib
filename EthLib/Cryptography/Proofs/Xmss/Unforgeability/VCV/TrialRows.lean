module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSource
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedTariff
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Ordinary
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSource

/-!
# Physical message trials in the normalized graph

The tweakable hash uses distinct address types for a message, chain, leaf and node.

An ordinary message trial therefore returns a cached full word or an independent fresh full word.

Free graph touches may be pending in either case.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig OracleSpec OracleComp TwoLayerGraph CanonicalGraph.PairedQueries
open ChainGraph (Public Word)
open scoped OracleSpec.PrimitiveQuery

/-- Neither tagged half of an actual message trial can name a graph point of either layer. -/
theorem trial_ordinary (pp : PublicParam) (b : HashInput) (trial : IsTrial b) :
    OrdinaryAt (graph pp) b := by
  obtain ⟨other, l, e, msg, rho, eq⟩ := trial
  have absent : decode pp b = none := by
    rw [← eq]
    exact decode_otherType pp other .msg (by decide) (by decide) (by decide) _ _ _ _
  intro st
  have different (row : Row) (vs : List Word) (h : (graph pp).childVals st row = some vs) :
      input pp (row.elim id id) vs ≠ b := by
    have width := (graph pp).length_eq_of_childVals_eq_some h
    have arity : vs.length = LayerGraph.arity (row.elim id id).2 := by
      cases row <;> simpa [graph, children] using width
    intro bad
    have full := decode_input pp _ _ arity
    rw [bad, absent] at full
    contradiction
  constructor <;> rintro ⟨r, vs, h, same⟩ <;> apply different r vs h <;>
    cases r <;> exact congrArg (Sum.elim id id) same

/-- A new trial samples an independent 256-bit word before the signed or unsigned continuation. -/
theorem trial_fresh (pp : PublicParam) (b : HashInput) (trial : IsTrial b)
    (st : DeferredState HashInput Word Start Row)
    (low : st.1.1 (.inl b) = none) (high : st.1.1 (.inr b) = none) :
    (fun w => (w, recordWord PairedHashWord.halves b w st)) <$> ($ᵗ HashOutput) =ᵈ
      (simulateQ (graph pp).deferredImpl
        (expand (X := Start) (K := Row) PairedHashWord.halves (.inl (.inr b)))).run st :=
  ordinary_fresh (graph pp) PairedHashWord.halves b (trial_ordinary pp b trial) st low high

/-- The fresh acceptance event is measured on the same complete reply exposed to the continuation.
-/
theorem trial_rate (pp : PublicParam) (b : HashInput) (trial : IsTrial b)
    (st : DeferredState HashInput Word Start Row)
    (low : st.1.1 (.inl b) = none) (high : st.1.1 (.inr b) = none) (event : HashOutput → Prop) :
    Pr{let z ← (simulateQ (graph pp).deferredImpl
      (expand (X := Start) (K := Row) PairedHashWord.halves (.inl (.inr b)))).run st}[event z.1] =
      Pr{let w ← $ᵗ HashOutput}[event w] := by
  have eq := (trial_fresh pp b trial st low high).prEvent_eq (fun z => event z.1)
  refine eq.symm.trans ?_
  simp only [prEvent_norm]

/--
A complete cached reply, including both high and low halves, survives this physical message call.
-/
theorem trial_warm (pp : PublicParam) (b : HashInput) (trial : IsTrial b)
    (st : DeferredState HashInput Word Start Row) (w : HashOutput)
    (low : st.1.1 (.inl b) = some (PairedHashWord.halves w).1)
    (high : st.1.1 (.inr b) = some (PairedHashWord.halves w).2) :
    (simulateQ (graph pp).deferredImpl
      (expand (X := Start) (K := Row) PairedHashWord.halves (.inl (.inr b)))).run st =
        pure (w, st) :=
  ordinary_warm (graph pp) PairedHashWord.halves b (trial_ordinary pp b trial) st w low high

/-- After every normalized prefix from the empty table, both message rows are cold or both are warm.
-/
theorem trial_occupancy {α : Type} (pp : PublicParam) (b : HashInput) (trial : IsTrial b)
    (left : Nat) (p : OracleComp (Mixed HashInput HashOutput Start Row Word) α) {z}
    (reach : z ∈ support ((simulateQ (graph pp).deferredImpl (guardedGraph left p)).run
      ((∅, ∅), []))) :
    (z.2.1.1 (.inl b)).isSome = (z.2.1.1 (.inr b)).isSome :=
  ordinary_run_occupancy (graph pp) PairedHashWord.halves b (trial_ordinary pp b trial) _
    ((∅, ∅), []) (by rfl) reach

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
