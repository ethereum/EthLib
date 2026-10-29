import EthLib.Serialization.Proofs.Ssz.Codec.ProofBudget
import EthLib.Serialization.Proofs.Ssz.Codec.ProofTree

/-! Crossing a composite leaf preserves the nested value's root and branch turns. -/

namespace EthLib.Serialization.Ssz

/-- Below a filled composite leaf, the bounded walker is exactly the nested value's walker. -/
theorem boundedNode_nested (layout : MerkleLayout) (budget : Nat)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (inner : Value) (enough : child.nesting ≤ budget)
    (index depth start capacity : Nat) (deeper : depthFor capacity < depth)
    (selected : slots[start + gindexBelow (index >>> (depth - depthFor capacity))
      (depthFor capacity)]? = some (some (child, inner))) :
    boundedNode budget layout index depth start capacity =
      nodeRoot child inner (gindexRebase index (depth - depthFor capacity)) := by
  -- The outer tree consumes its height, leaving the remaining turns inside the child.
  simp only [boundedNode, nextPow2, Nat.log2_two_pow, ite_eq_right (Nat.not_le.mpr deeper), nested, selected]
  exact nodeRootAt_eq_nodeRoot child inner _ budget enough

/-- At a filled composite leaf, the outer tree commits to exactly the child's own root. -/
theorem boundedNode_nested_leaf (layout : MerkleLayout) (budget : Nat)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (inner : Value) (enough : child.nesting ≤ budget)
    (index start capacity : Nat)
    (selected : slots[start + gindexBelow index (depthFor capacity)]? =
      some (some (child, inner))) :
    boundedNode budget layout index (depthFor capacity) start capacity = hashTreeRoot child inner := by
  -- A leaf interval has width one, so merkleization adds no extra hash around the child's root.
  obtain ⟨inside, atLeaf⟩ := List.getElem?_eq_some_iff.mp selected
  -- A one-position interval materializes exactly the selected child root.
  have one := layoutChunksAt_singleton budget layout slots nested
    (start + gindexBelow index (depthFor capacity)) inside
  simp only [atLeaf] at one
  simp only [boundedNode, nextPow2, Nat.log2_two_pow, Nat.le_refl, ↓reduceIte,
    Nat.shiftRight_eq_div_pow, Nat.div_self (Nat.two_pow_pos _), Nat.mul_one]
  rw [one, hashTreeRootAt_eq_hashTreeRoot child inner budget enough]
  -- The enclosing leaf preserves both the child’s successful root and any child-rooting error.
  cases hashTreeRoot child inner <;>
    simp [merkleizeBoundedUnchecked, subtreeAt, depthFor, padded, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Removing an outer path prefix preserves each left or right child turn. -/
theorem gindexRebase_children (index depth : Nat) :
    gindexRebase (2 * index) (depth + 1) = 2 * gindexRebase index depth ∧
    gindexRebase (2 * index + 1) (depth + 1) = 2 * gindexRebase index depth + 1 := by
  -- The new leading one moves left alongside the retained low branch bits.
  obtain ⟨left, right⟩ := gindexBelow_children index depth
  simp only [gindexRebase, left, right, Nat.pow_succ, Nat.mul_add]
  constructor <;> omega

/-- At or below a filled leaf, the outer walk reads the nested value at the rebased index. -/
theorem boundedNode_nested_at (layout : MerkleLayout) (budget : Nat)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (inner : Value) (enough : child.nesting ≤ budget)
    (index depth start capacity : Nat) (reached : depthFor capacity ≤ depth)
    (selected : slots[start + gindexBelow (index >>> (depth - depthFor capacity))
      (depthFor capacity)]? = some (some (child, inner))) :
    boundedNode budget layout index depth start capacity =
      nodeRoot child inner (gindexRebase index (depth - depthFor capacity)) := by
  -- At the boundary the remaining path is empty, naming the child's root at index one.
  by_cases boundary : depth = depthFor capacity
  · subst depth
    simpa only [Nat.sub_self, gindexRebase, gindexBelow, Nat.pow_zero, Nat.mod_one,
      Nat.add_zero, nodeRoot_root] using
      boundedNode_nested_leaf layout budget slots nested child inner enough index start capacity
        (by simpa using selected)
  · exact boundedNode_nested layout budget slots nested child inner enough index depth start
      capacity (by omega) selected

/-- Rebasing commutes with moving one level upward while a nested branch still has turns. -/
theorem gindexRebase_parent (index depth : Nat) :
    gindexRebase index (depth + 1) / 2 = gindexRebase (index / 2) depth := by
  -- Every index is either its parent's left child or its parent's right child.
  obtain ⟨left, right⟩ := gindexRebase_children (index / 2) depth
  -- The lowest retained turn identifies which of the common parent’s children is being rebased.
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · rw [(congrArg (gindexRebase · (depth + 1)) (show index = 2 * (index / 2) by omega)).trans left]
    omega
  · rw [(congrArg (gindexRebase · (depth + 1)) (show index = 2 * (index / 2) + 1 by omega)).trans right]
    omega

/-- Rebasing preserves sibling positions until the outer leaf boundary is reached. -/
theorem gindexRebase_sibling (index depth : Nat) :
    gindexRebase (gindexSibling index) (depth + 1) =
      gindexSibling (gindexRebase index (depth + 1)) := by
  -- The sibling operation changes only the last retained turn.
  obtain ⟨left, right⟩ := gindexRebase_children (index / 2) depth
  -- The lowest retained turn identifies which of the common parent’s children is being rebased.
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · obtain ⟨child, sibling⟩ := gindexSibling_even even
    have rebased := (congrArg (gindexRebase · (depth + 1)) child).trans left
    rw [sibling, right, rebased]
    simpa using (gindexSibling_even (by omega : (2 * gindexRebase (index / 2) depth) % 2 = 0)).2.symm
  · obtain ⟨child, sibling⟩ := gindexSibling_odd odd
    have rebased := (congrArg (gindexRebase · (depth + 1)) child).trans right
    rw [sibling, left, rebased]
    have half : (2 * gindexRebase (index / 2) depth + 1) / 2 = gindexRebase (index / 2) depth := by omega
    simpa only [half] using
      (gindexSibling_odd (by omega : (2 * gindexRebase (index / 2) depth + 1) % 2 = 1)).2.symm

end EthLib.Serialization.Ssz
