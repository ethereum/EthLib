import EthLib.Serialization.Proofs.Ssz.Codec.NestedProof

/-! Every readable branch node has a readable sibling and the expected parent hash. -/

namespace EthLib.Serialization.Ssz

/-- Reading a non-root node also exposes its sibling and their common parent. -/
def WalkerClosed (read : Nat → Except Err Bytes) : Prop :=
  ∀ index node, 2 ≤ index → read index = .ok node →
    ∃ parent sibling, read (index / 2) = .ok parent ∧
      read (gindexSibling index) = .ok sibling ∧
      parent = if index % 2 = 0 then combine node sibling else combine sibling node

private theorem boundedTreeNode_parent (chunks : Array Bytes) (height index depth start : Nat)
    (positive : 0 < depth) (inside : depth ≤ height) :
    boundedTreeNode chunks height (index / 2) (depth - 1) start =
      if index % 2 = 0 then
        combine (boundedTreeNode chunks height index depth start)
          (boundedTreeNode chunks height (gindexSibling index) depth start)
      else combine (boundedTreeNode chunks height (gindexSibling index) depth start)
        (boundedTreeNode chunks height index depth start) := by
  -- Parity identifies the current child and the other half of its parent's interval.
  have equation := boundedTreeNode_split chunks height (index / 2) (depth - 1) start (by omega)
  rw [show depth - 1 + 1 = depth by omega] at equation
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · obtain ⟨child, sibling⟩ := gindexSibling_even even
    rw [← sibling, ← child] at equation
    simpa only [ite_eq_left even] using equation
  · obtain ⟨child, sibling⟩ := gindexSibling_odd odd
    rw [← child, ← sibling] at equation
    simpa only [ite_eq_right (by omega : index % 2 ≠ 0)] using equation

/-- A successful bounded read has a sibling and parent whenever nested values do. -/
theorem boundedNode_closed (layout : MerkleLayout) (budget : Nat) (chunks : Array Bytes)
    (materialized : layoutChunksAt budget layout = .ok chunks)
    (children : ∀ slots, layout.leaves = .nested slots → ∀ child inner,
      some (child, inner) ∈ slots → child.nesting ≤ budget ∧ WalkerClosed (nodeRoot child inner))
    (index depth start capacity : Nat) (positive : 0 < depth)
    (node : Bytes) (read : boundedNode budget layout index depth start capacity = .ok node) :
    ∃ parent sibling,
      boundedNode budget layout (index / 2) (depth - 1) start capacity = .ok parent ∧
      boundedNode budget layout (gindexSibling index) depth start capacity = .ok sibling ∧
      parent = if index % 2 = 0 then combine node sibling else combine sibling node := by
  -- Above leaf depth, all three reads are materialized binary intervals.
  -- Every interval read uses the same fully materialized leaves as the original value root.
  have windows := layoutChunksAt_window budget layout chunks materialized
  by_cases inside : depth ≤ depthFor capacity
  · cases (boundedNode_window windows index depth start capacity inside).symm.trans read
    exact ⟨boundedTreeNode chunks (depthFor capacity) (index / 2) (depth - 1) start,
      boundedTreeNode chunks (depthFor capacity) (gindexSibling index) depth start,
      boundedNode_window windows _ _ _ _ (by omega), boundedNode_window windows _ _ _ _ inside,
      boundedTreeNode_parent chunks _ index depth start positive inside⟩
  · have deeper : depthFor capacity < depth := by omega
    -- Below leaf depth, success requires a filled composite slot.
    simp only [boundedNode, nextPow2, Nat.log2_two_pow, ite_eq_right inside] at read
    cases nested : layout.leaves with
    | packed data => simp [nested, throw, throwThe, MonadExceptOf.throw] at read
    | nested slots =>
      simp only [nested] at read
      split at read
      · rename_i child inner selected
        have member := List.mem_of_getElem? selected
        obtain ⟨enough, closed⟩ := children slots nested child inner member
        rw [nodeRootAt_eq_nodeRoot child inner _ budget enough] at read
        have belowPositive : 0 < depth - depthFor capacity := by omega
        -- Descending below an outer leaf leaves at least one turn inside its actual child tree.
        have rebasedPositive : 2 ≤ gindexRebase index (depth - depthFor capacity) := by
          unfold gindexRebase
          have power : 2 ≤ 2 ^ (depth - depthFor capacity) := Nat.le_self_pow (by omega) 2
          omega
        obtain ⟨parent, sibling, parentRead, siblingRead, equation⟩ :=
          closed _ node rebasedPositive read
        have remaining : depth - depthFor capacity = (depth - 1 - depthFor capacity) + 1 := by omega
        -- Removing the final nested turn leaves the same outer leaf-selection prefix.
        have parentShift : (index / 2) >>> (depth - 1 - depthFor capacity) =
            index >>> (depth - depthFor capacity) := by
          rw [remaining, Nat.add_comm _ 1, Nat.shiftRight_add]
          rfl
        -- Flipping the final nested turn also leaves the outer leaf-selection prefix unchanged.
        have siblingShift : (gindexSibling index) >>> (depth - depthFor capacity) =
            index >>> (depth - depthFor capacity) := by
          rw [remaining, Nat.add_comm _ 1, Nat.shiftRight_add, Nat.shiftRight_add]
          simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one, gindexSibling_half]
        have parentSelected : slots[start + gindexBelow
            ((index / 2) >>> (depth - 1 - depthFor capacity)) (depthFor capacity)]? =
            some (some (child, inner)) := by simpa only [parentShift] using selected
        have siblingSelected : slots[start + gindexBelow
            ((gindexSibling index) >>> (depth - depthFor capacity)) (depthFor capacity)]? =
            some (some (child, inner)) := by simpa only [siblingShift] using selected
        refine ⟨parent, sibling, ?_, ?_, ?_⟩
        · rw [boundedNode_nested_at layout budget slots nested child inner enough
            (index / 2) (depth - 1) start capacity (by omega) parentSelected]
          rwa [remaining, gindexRebase_parent] at parentRead
        · rw [boundedNode_nested_at layout budget slots nested child inner enough
            (gindexSibling index) depth start capacity (by omega) siblingSelected]
          rw [remaining, gindexRebase_sibling]
          simpa only [remaining] using siblingRead
        -- Rebasing retains the final left-or-right bit, so parent hashes keep the same child ordering.
        · have parity : gindexRebase index (depth - depthFor capacity) % 2 = index % 2 := by
            rw [remaining]
            rcases Nat.mod_two_eq_zero_or_one index with even | odd
            · rw [(gindexSibling_even even).1, (gindexRebase_children _ _).1]
              omega
            · rw [(gindexSibling_odd odd).1, (gindexRebase_children _ _).2]
              omega
          simpa only [parity] using equation
      · simp [throw, throwThe, MonadExceptOf.throw] at read

end EthLib.Serialization.Ssz
