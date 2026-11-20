module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraph

/-!
# One projected target for each public hash input across both leanXMSS layers

The leanXMSS draft, sections "Hashing and parameters" and "Trees", encodes the layer in each address.
This gives both layers one public oracle and one count of the distinct inputs queried there.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open Constants HashSig OracleSpec OracleComp
open ChainGraph (Public Word)
open scoped ENNReal

abbrev Role := Layer × LayerGraph.Role
abbrev Start := Layer × LayerGraph.Start
abbrev Row := Role ⊕ Role
abbrev Cell := Start ⊕ Row

/-- A child of a graph node belongs to its parent's layer. -/
def inLayer (l : Layer) : LayerGraph.Cell → Cell :=
  Sum.map (fun s => (l, s)) (Sum.map (fun r => (l, r)) (fun r => (l, r)))

def children (r : Role) : List Cell := (LayerGraph.children r.2).map (inLayer r.1)

def input (pp : PublicParam) (r : Role) (vs : List Word) : HashInput :=
  LayerGraph.input pp r.1 r.2 vs

private theorem layer_of_address {l l' : Layer} {a b : LayerGraph.Role}
    (h : LayerGraph.address l a = LayerGraph.address l' b) : l = l' := by
  cases a <;> cases b
  case chain.chain => exact (addrChain_inj.mp h).1
  case leaf.leaf => exact (addrLeaf_inj.mp h).1
  case node.node => exact (addrNode_inj.mp h).1
  all_goals exact False.elim (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide) h)

/-- The bytes identify the layer, role and ordered children of every valid query. -/
theorem input_injective {pp : PublicParam} {r s : Role} {vs ws : List Word}
    (hv : vs.length = LayerGraph.arity r.2) (hw : ws.length = LayerGraph.arity s.2)
    (h : input pp r vs = input pp s ws) : r = s ∧ vs = ws := by
  obtain ⟨l, a⟩ := r
  obtain ⟨m, b⟩ := s
  have layers : l = m := layer_of_address (thInput_inj (ByteArray.ext (Array.toList_inj.mp h))).2.1
  subst m
  obtain ⟨rfl, rfl⟩ := LayerGraph.input_injective hv hw h
  exact ⟨rfl, rfl⟩

/-- The two halves of a hash query refer to the same physical byte string. -/
def graph (pp : PublicParam) : CanonicalGraph Public Start Row Word where
  ch k := k.elim children children
  pt k vs := k.elim (fun r => .inl (input pp r vs)) (fun r => .inr (input pp r vs))
  range_eq _ _ := rfl
  pt_inj := by
    intro r s vs ws hv hw same
    cases r <;> cases s <;> simp [children] at same hv hw
    all_goals
      obtain ⟨rfl, rfl⟩ := input_injective hv hw same
      exact ⟨rfl, rfl⟩

/-- Every valid public input names a single target across both layers. -/
noncomputable def decode (pp : PublicParam) (b : HashInput) : Option Role := open Classical in
  if h : ∃ r, ∃ vs : List Word, vs.length = LayerGraph.arity r.2 ∧ input pp r vs = b
  then some h.choose else none

theorem decode_input (pp : PublicParam) (r : Role) (vs : List Word)
    (size : vs.length = LayerGraph.arity r.2) : decode pp (input pp r vs) = some r := by
  have h : ∃ s, ∃ ws : List Word, ws.length = LayerGraph.arity s.2 ∧ input pp s ws = input pp r vs :=
    ⟨r, vs, size, rfl⟩
  obtain ⟨ws, width, same⟩ := h.choose_spec
  exact (dite_eq_left h).trans (congrArg some (input_injective width size same).1)

noncomputable def lowKeys (pp : PublicParam) : (graph pp).ProjKeys where
  node := Sum.elim (fun b => (decode pp b).map Sum.inl) (fun _ => none)
  proj _ v := v
  prEvent_proj_le _ _ _ v := (SampleableType.prEvent_uniformSample_eq_singleton_natCard v).le

/-- The off-path input has the right role and arity but at least one different child.
Both its low hash and the genuine low hash yield the same output. -/
def OffPath (pp : PublicParam) (st : RelabelState Public Start Row Word) : Prop :=
  ∃ r : Role, ∃ vs ws : List Word, ∃ out : Word, (graph pp).childVals st (.inl r) = some vs ∧
    ws.length = LayerGraph.arity r.2 ∧ vs ≠ ws ∧
    (graph pp).merge st (.inl (input pp r vs)) = some out ∧
    (graph pp).merge st (.inl (input pp r ws)) = some out

theorem projected_of_offPath (pp : PublicParam) (st : RelabelState Public Start Row Word)
    (hit : OffPath pp st) : (lowKeys pp).ProjHazard st := by
  obtain ⟨r, vs, ws, out, ready, width, different, canonical, off⟩ := hit
  have source := (graph pp).merge_apply_pt ready
  change (graph pp).merge st (.inl (input pp r vs)) = _ at source
  have target : st.2 (.inr (.inl r)) = some out := by simpa using source.symm.trans canonical
  have ordinary : (graph pp).merge st (.inl (input pp r ws)) = st.1 (.inl (input pp r ws)) := by
    apply (graph pp).merge_apply_of_not_exists
    rintro ⟨k, us, enabled, same⟩
    have size : ws.length = ((graph pp).ch (.inl r)).length := by simpa [graph, children] using width
    obtain ⟨rfl, rfl⟩ := (graph pp).pt_inj ((graph pp).length_eq_of_childVals_eq_some enabled)
      (k' := Sum.inl r) (vs' := ws) size same
    exact different (Option.some.inj (ready.symm.trans enabled))
  refine ⟨.inl (input pp r ws), .inl r, out, out, ?_, target, ordinary.symm.trans off, rfl⟩
  change (decode pp (input pp r ws)).map Sum.inl = some (.inl r)
  rw [decode_input pp r ws width]
  rfl

/-- The ordinary cache may contain either or both halves at a physical input. -/
def physicalInputs (c : Public.QueryCache) : Set HashInput :=
  {b | (c (.inl b)).isSome ∨ (c (.inr b)).isSome}

private theorem potential_le (pp : PublicParam) (st : RelabelState Public Start Row Word) :
    (lowKeys pp).potential st ≤ ((physicalInputs st.1).encard : ℝ≥0∞) / Nat.card Word := by
  have sub : (lowKeys pp).keyEntries st.1 ⊆ Sum.inl '' physicalInputs st.1 := by
    rintro (b | b) ⟨present, key⟩
    · exact ⟨b, Or.inl present, rfl⟩
    · exact False.elim (Bool.false_ne_true key)
  apply ((lowKeys pp).potential_le st).trans
  gcongr
  exact (Set.encard_le_encard sub).trans (Set.encard_image_le _ _)

/-- A single physical-input budget covers an off-path hit in any role of either layer. -/
theorem prEvent_offPath (pp : PublicParam) {α : Type}
    (p : OracleComp (Public.withLabels Start Row Word) α) (q : Nat)
    (budget : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl p).run ((∅, ∅), [])),
      (physicalInputs z.2.1.1).encard ≤ q) :
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) p}[OffPath pp z.2.1] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  classical
  have card : (Nat.card Word : ℝ≥0∞) = 2 ^ 128 := by
    rw [Nat.card_eq_fintype_card]
    norm_num [Word, digestBits]
  let bound (c : Public.QueryCache) := ((physicalInputs c).encard : ℝ≥0∞) / Nat.card Word
  have charge := (lowKeys pp).isCharged.prEvent_deferredFillDraw_and_le
    (lowKeys pp).not_projHazard_empty bound (potential_le pp) (pure ())
    (fun _ _ => False) (fun _ => 0) (fun _ => by simp) p ((q : ℝ≥0∞) / 2 ^ 128) (by finiteness)
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) charge
  intro z supported hit
  obtain ⟨before, filled, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp supported
  refine ⟨Or.inl (projected_of_offPath pp z.2.1 hit), ?_⟩
  dsimp [bound]
  rw [add_zero, card, RelabelState.fst_eq_of_mem_support_endFill filled]
  gcongr
  exact_mod_cast budget _ before

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
