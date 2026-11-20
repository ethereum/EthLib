module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerBudget
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential.Subgraph

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open HashSig OracleComp OracleSpec Constants
open ChainGraph (Word Public)
open CanonicalGraph.PairedQueries
open scoped ENNReal

@[expose] def lowCell : Start ⊕ Role ↪ Cell where
  toFun := Sum.map id Sum.inl
  inj' := Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩

@[expose] def forgetHalf : Cell → Start ⊕ Role := Sum.map id (Sum.elim id id)

-- Each child's value is a private start or the low response from its predecessor.
theorem restore_children (r : Role) :
    ((children r).map forgetHalf).map lowCell = children r := by
  obtain ⟨layer, r⟩ := r
  cases r with
  | chain e i j =>
    simp [children, LayerGraph.children, LayerGraph.chainCell, apply_ite, inLayer, lowCell, forgetHalf]
  | leaf e =>
    simp [children, LayerGraph.children, inLayer, lowCell, forgetHalf, List.map_ofFn, Function.comp_def]
  | node level j =>
    simp [children, LayerGraph.children, inLayer, lowCell, forgetHalf]

/-- Only the low labels can occur as inputs to another public graph point. -/
@[expose] def lowGraph (pp : PublicParam) : CanonicalGraph Public Start Role Word where
  ch r := (children r).map forgetHalf
  pt r vs := .inl (input pp r vs)
  range_eq _ _ := rfl
  pt_inj := by
    intro r s vs ws hv hw same
    apply input_injective _ _ (Sum.inl.inj same)
    · simpa [children] using hv
    · simpa [children] using hw

@[expose] def subgraph (pp : PublicParam) : (lowGraph pp).Subgraph (graph pp) where
  cell := lowCell
  node := Sum.inl
  node_cell _ := rfl
  children r := (restore_children r).symm
  point _ _ := rfl

@[expose] noncomputable def keys (pp : PublicParam) : (lowGraph pp).NodeKeys where
  node := Sum.elim (decode pp) (fun _ => none)
  node_pt := by
    intro r vs len
    exact decode_input pp r vs (by simpa [lowGraph, children] using len)
  range_eq _ := rfl

/-- Each physically occupied high row also has its low row. -/
@[expose] def PairedPresence (st : RelabelState Public Start Row Word) : Prop :=
  ∀ b : HashInput, (st.1 (.inr b)).isSome → (st.1 (.inl b)).isSome

/-- A conflict at either half is a conflict at the single physical target. -/
theorem lowConflict (pp : PublicParam) (st : RelabelState Public Start Row Word)
    (paired : PairedPresence st) (conflict : (graph pp).Conflict st) :
    (lowGraph pp).Conflict ((subgraph pp).project st) := by
  obtain ⟨r | r, vs, ready, present⟩ := conflict
  · exact ⟨r, vs, ((subgraph pp).childVals st r).symm.trans ready, present⟩
  · have low : (graph pp).childVals st (.inl r) = some vs :=
      (graph pp).childVals_eq_some_iff.mpr (((graph pp).childVals_eq_some_iff (k := Sum.inr r)).mp ready)
    exact ⟨r, vs, ((subgraph pp).childVals st r).symm.trans low, paired _ present⟩

/-- An off-path hit uses an ordinary low query at a decoded low label. -/
theorem lowCollision (pp : PublicParam) (st : RelabelState Public Start Row Word)
    (hit : OffPath pp st) : (keys pp).TCHazard ((subgraph pp).project st) := by
  obtain ⟨b | b, k, l, v, named, label, entry, eqn⟩ := projected_of_offPath pp st hit
  · change (decode pp b).map Sum.inl = some k at named
    cases dec : decode pp b with
    | none => simp [dec] at named
    | some r =>
      simp only [dec, Option.map_some, Option.some.injEq] at named
      subst k
      change v = l at eqn
      subst v
      refine ⟨.inl b, r, l, dec, label, ?_⟩
      exact entry
  · contradiction

private theorem reduced_potential (pp : PublicParam) (st : RelabelState Public Start Row Word) :
    (keys pp).potential ((subgraph pp).project st) ≤
      2 * ((physicalInputs st.1).encard : ℝ≥0∞) / Nat.card Word := by
  have sub : (keys pp).keyEntries st.1 ⊆ Sum.inl '' physicalInputs st.1 := by
    rintro (b | b) ⟨present, named⟩
    · exact ⟨b, Or.inl present, rfl⟩
    · exact False.elim (Bool.false_ne_true named)
  apply ((keys pp).potential_le_two_mul _).trans
  gcongr
  exact (Set.encard_le_encard sub).trans (Set.encard_image_le _ _)

/-- Conflicts and off-path hits together cost at most two chances per physical hash input.
The presence condition is needed only to reflect conflicts at a high row. -/
theorem prEvent_conflict_or_offPath_and_cost (pp : PublicParam) {α β : Type}
    (setup : OracleComp (Public.withLabels Start Row Word) (β × Nat))
    (p : β → OracleComp XmssSecurity.OracleWorld α)
    (paid : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl setup).run ((∅, ∅), [])),
      (physicalInputs z.2.1.1).encard ≤ z.1.2) (q : Nat) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (afterSetup PairedHashWord.halves setup p)}[
      ((PairedPresence z.2.1 ∧ (graph pp).Conflict z.2.1) ∨ OffPath pp z.2.1) ∧ z.1.1.2 ≤ q] ≤
      2 * (q : ℝ≥0∞) / 2 ^ 128 := by
  classical
  let f := subgraph pp
  let nk := keys pp
  let bound (c : Public.QueryCache) := 2 * ((physicalInputs c).encard : ℝ≥0∞) / Nat.card Word
  have empty : ¬((lowGraph pp).Conflict (f.project (∅, ∅)) ∨ nk.TCHazard (f.project (∅, ∅))) := by
    have h : f.project (∅, ∅) = (∅, ∅) := rfl
    rw [h]
    exact not_or.mpr ⟨(lowGraph pp).not_conflict_empty, CanonicalGraph.NodeKeys.not_tcHazard_empty⟩
  have joint := (f.isCharged nk.isCharged).prEvent_deferredFillDraw_and_le empty bound
    (reduced_potential pp) (pure ()) (fun _ _ => False) (fun _ => 0) (fun _ => by simp)
    (afterSetup PairedHashWord.halves setup p) (2 * (q : ℝ≥0∞) / 2 ^ 128) (by finiteness)
  have card : (Nat.card Word : ℝ≥0∞) = 2 ^ 128 := by
    rw [Nat.card_eq_fintype_card]
    norm_num [Word, digestBits]
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) joint
  rintro z hz ⟨hit, cost⟩
  obtain ⟨before, filled, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp hz
  refine ⟨Or.inl (hit.elim (fun h => Or.inl (lowConflict pp _ h.1 h.2))
    (fun h => Or.inr (lowCollision pp _ h))), ?_⟩
  dsimp [bound]
  rw [add_zero, card, RelabelState.fst_eq_of_mem_support_endFill filled]
  gcongr
  exact_mod_cast (afterSetup_footprint (graph pp) PairedHashWord.halves setup p paid _ before).trans
    (Nat.cast_le.mpr cost)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
