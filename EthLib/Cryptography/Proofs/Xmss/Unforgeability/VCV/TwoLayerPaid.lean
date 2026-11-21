module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerConflict
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Presence

/-!
# Conflicts and off-path hits in the two-layer graph

A full leanXMSS hash asks for both halves at the same byte string.

A canonical low query already has a canonical high query at the same children.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
open HashSig OracleComp OracleSpec Constants
open ChainGraph (Word Public)
open CanonicalGraph.PairedQueries
open scoped ENNReal

/-- Both output rows at a leanXMSS hash depend on the same children in the same order. -/
theorem ready_pair (pp : PublicParam) (st : RelabelState Public Start Row Word) (b : HashInput)
    (h : Ready (graph pp) st (.inl b)) : Ready (graph pp) st (.inr b) := by
  obtain ⟨k | k, vs, children, key⟩ := h
  · have high : (graph pp).childVals st (.inr k) = some vs :=
      (graph pp).childVals_eq_some_iff.mpr
        (((graph pp).childVals_eq_some_iff (k := Sum.inl k)).mp children)
    exact ⟨.inr k, vs, high, congrArg Sum.inr (Sum.inl.inj key)⟩
  · contradiction

/-- A setup may populate secret labels and use public queries before the adaptive caller.

Every occupied public input is paid and each occupied high row has a low row. -/
theorem prEvent_hash_graph_bad (pp : PublicParam) {α β : Type}
    (setup : OracleComp (Public.withLabels Start Row Word) (β × Nat))
    (p : β → OracleComp XmssSecurity.OracleWorld α)
    (accounted : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl setup).run ((∅, ∅), [])),
      (physicalInputs z.2.1.1).encard ≤ z.1.2 ∧ PairedPresence z.2.1) (q : Nat) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (afterSetup PairedHashWord.halves setup p)}[
      ((graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1) ∧ z.1.1.2 ≤ q] ≤ (q : ℝ≥0∞) / 2 ^ 127 := by
  have bound := prEvent_conflict_or_offPath_and_cost pp setup p (fun z hz => (accounted z hz).1) q
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) (bound.trans_eq ?_)
  · rintro z hz ⟨hit, cost⟩
    rcases hit with conflict | off
    · obtain ⟨before, filled, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp hz
      have together : PairedPresence z.1.2.1 := by
        simp only [afterSetup, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, mem_support_pure_iff] at before
        obtain ⟨s, hs, t, ht, final⟩ := before
        rw [final]
        exact meteredCaller_present (graph pp) PairedHashWord.halves (p s.1.1) (ready_pair pp) s.2
          (accounted _ hs).2 t ht
      have stable := RelabelState.fst_eq_of_mem_support_endFill filled
      have present : PairedPresence z.2.1 := by simpa only [PairedPresence, stable] using together
      exact ⟨Or.inl ⟨present, conflict⟩, cost⟩
    · exact ⟨Or.inr off, cost⟩
  · rw [show (2 : ℝ≥0∞) ^ 128 = 2 * 2 ^ 127 by rw [pow_succ, mul_comm]]
    exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
