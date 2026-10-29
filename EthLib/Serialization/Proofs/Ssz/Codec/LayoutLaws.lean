import EthLib.Serialization.Proofs.Ssz.Codec.Layout
import EthLib.Serialization.Proofs.Ssz.Codec.Admits

/-! Nested leaves always carry types shallower than their enclosing type. -/

namespace EthLib.Serialization.Ssz

/-- A type in a list is nested no deeper than the deepest type in that list. -/
theorem nesting_le_deepest (shape : Desc) (fields : List Desc)
    (member : shape ∈ fields) : shape.nesting ≤ Desc.deepestNesting fields := by
  -- The maximum over fields bounds each individual field depth.
  induction fields <;> grind [Desc.deepestNesting]

private theorem sequenceLayout_depth (element : Desc) (values : List Value)
    (positions : Option Nat) (mixin : Option Bytes) (layout : MerkleLayout)
    (success : sequenceLayout element values positions mixin = .ok layout)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (value : Value) (member : some (child, value) ∈ slots) :
    child = element := by
  -- Basic elements are packed bytes, while each composite slot has the element type.
  unfold sequenceLayout at success
  split at success
  · cases h : serializeEach element values <;>
      simp [h, Bind.bind, Except.bind, pure, Except.pure] at success
    simp [← success, MerkleLayout.packing] at nested
  · simp_all [pure, Except.pure, MerkleLayout.nesting]
    grind

/-- Every present nested leaf has strictly smaller type depth than its enclosing value. -/
theorem merkleLayout_child_nesting (shape : Desc) (value : Value) (layout : MerkleLayout)
    (success : merkleLayout shape value = .ok layout)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (inner : Value) (member : some (child, inner) ∈ slots) :
    child.nesting < shape.nesting := by
  -- Each layout constructor either packs bytes or selects declared child types.
  cases shape <;> cases value <;>
    simp [merkleLayout, fixedLeaf, Bind.bind, Except.bind, Pure.pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at success
  all_goals try solve
    | split at success <;> simp only [Except.ok.injEq, reduceCtorEq] at success
      subst layout
      cases nested
    | subst layout
      cases nested
  -- Sequence positions all have the declared element type, one type level below the sequence.
  case vector.seq element _ elements | list.seq element _ elements
    | progressiveList.seq element _ elements =>
    (try split at success) <;> try simp only [reduceCtorEq] at success
    simp [sequenceLayout_depth _ _ _ _ _ success slots nested child inner member, Desc.nesting]
  -- Pairing preserves field membership, so the maximum declared depth bounds the child.
  case container.seq names fields elements =>
    split at success <;> simp only [reduceCtorEq, Except.ok.injEq] at success
    subst success
    simp only [MerkleLayout.nesting, Leaves.nested.injEq] at nested
    subst nested
    exact Nat.lt_succ_of_le
      (nesting_le_deepest child fields (List.of_mem_zip (by simpa using member)).1)
  case progressiveContainer.seq active names fields elements =>
    -- EIP-7495 gaps add positions but never introduce a new field type.
    cases hs : layoutSlots active fields elements <;> simp [hs] at success
    subst success
    simp only [MerkleLayout.nesting, Leaves.nested.injEq] at nested
    subst nested
    simp only [layoutSlots] at hs
    split at hs <;> try contradiction
    split at hs <;> try contradiction
    have paired : (child, inner) ∈ fields.zip elements := by
      rw [← placeSlots_fields hs]
      exact List.mem_filterMap.mpr ⟨some (child, inner), member, rfl⟩
    exact Nat.lt_succ_of_le (nesting_le_deepest child fields (List.of_mem_zip paired).1)
  case compatibleUnion.union selectors options selector data =>
    -- EIP-8016 selectors choose an existing option without changing its type.
    cases hl : lookupOption selectors options selector <;>
      cases hw : selectorWord selector <;> simp [hl, hw] at success
    subst success
    simp only [MerkleLayout.nesting, Leaves.nested.injEq] at nested
    subst nested
    simp only [List.mem_singleton, Option.some.injEq, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact Nat.lt_succ_of_le (nesting_le_deepest child options (lookupOption_mem _ _ _ _ hl))

end EthLib.Serialization.Ssz
