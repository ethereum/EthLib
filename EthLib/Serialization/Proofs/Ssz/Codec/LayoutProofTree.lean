import EthLib.Serialization.Proofs.Ssz.Codec.ProgressiveProofTree
import EthLib.Serialization.Proofs.Ssz.Codec.ProofBudget

/-! A value's materialized leaves determine its top-level proof tree, including nested field roots. -/

namespace EthLib.Serialization.Ssz

/-- A bounded layout hashes its materialized leaves, then its optional mixing word. -/
theorem hashTreeRoot_bounded_layout {shape : Desc} {value : Value} {layout : MerkleLayout}
    {chunks : Array Bytes} {capacity : Nat}
    (laid : merkleLayout shape value = .ok layout)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (bounded : layout.limit = some capacity) (fits : chunks.size ≤ capacity) :
    hashTreeRoot shape value = .ok (match layout.mixin with
      | none => subtreeAt chunks (depthFor capacity) 0
      | some word => combine (subtreeAt chunks (depthFor capacity) 0) word) := by
  -- The type's positive nesting depth leaves one budget unit for its own layout.
  have positive := shape.nesting_pos
  unfold hashTreeRoot
  cases nesting : shape.nesting with
  | zero => omega
  | succ budget =>
    -- The enclosing type consumes one recursion level, matching the budget used for its materialized leaves.
    simp only [nesting, Nat.add_sub_cancel] at materialized
    simp [hashTreeRootAt, laid, materialized, bounded, merkleizeBoundedUnchecked, Nat.not_lt.mpr fits,
      mixIn, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

/-- Every top-level node in an unmixed bounded layout is its corresponding binary subtree. -/
theorem nodeRoot_bounded_layout {shape : Desc} {value : Value} {layout : MerkleLayout}
    {chunks : Array Bytes} {capacity : Nat}
    (laid : merkleLayout shape value = .ok layout)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (bounded : layout.limit = some capacity) (unmixed : layout.mixin = none)
    (fits : chunks.size ≤ capacity) (index : Nat) (named : 1 ≤ index)
    (inside : Nat.log2 index ≤ depthFor capacity) :
    nodeRoot shape value index = .ok (boundedReading chunks (depthFor capacity) index) := by
  -- A sufficient walk budget can be replaced by the exact budget used to materialize the leaves.
  by_cases root : index = 1
  · subst index
    rw [nodeRoot_root, hashTreeRoot_bounded_layout laid materialized bounded fits, unmixed,
      boundedReading_root]
  · have positive := shape.nesting_pos
    have below : 2 ≤ index := by omega
    have deep : Nat.log2 index ≠ 0 := by
      have recursion := levelOf_parent below
      change Nat.log2 index = _ at recursion
      omega
    rw [← nodeRootAt_eq_nodeRoot shape value index shape.nesting (Nat.le_refl _)]
    cases nesting : shape.nesting with
    | zero => omega
    | succ budget =>
      -- The enclosing type consumes one recursion level, matching the budget used for its materialized leaves.
      simp only [nesting, Nat.add_sub_cancel] at materialized
      simp only [nodeRootAt, Nat.not_lt.mpr named, ↓reduceIte, beq_iff_eq, root, bind, Except.bind, laid,
        gindexLength, gindexDepth, deep, unmixed, bounded, Option.isSome_none, Bool.false_eq_true]
      exact boundedNode_window (layoutChunksAt_window budget layout chunks materialized)
        index (Nat.log2 index) 0 capacity inside

/-- Every top-level node of a bounded mixed layout is its contents or its single mixing word. -/
theorem nodeRoot_mixed_layout {shape : Desc} {value : Value} {layout : MerkleLayout}
    {chunks : Array Bytes} {capacity : Nat} {word : Bytes}
    (laid : merkleLayout shape value = .ok layout)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (bounded : layout.limit = some capacity) (mixed : layout.mixin = some word)
    (fits : chunks.size ≤ capacity) (index : Nat)
    (readable : index = 1 ∨ index = 3 ∨
      (2 ≤ index ∧ gindexBit index (Nat.log2 index - 1) = false ∧
        Nat.log2 index - 1 ≤ depthFor capacity)) :
    nodeRoot shape value index = .ok (mixedReading chunks (depthFor capacity) word index) := by
  -- Mixed words end at depth one, while contents continue through their bounded intervals.
  rcases readable with root | wordIndex | ⟨named, leftSide, inside⟩
  · subst index
    rw [nodeRoot_root, hashTreeRoot_bounded_layout laid materialized bounded fits, mixed]
    simp [mixedReading]
  · subst index
    have depth : gindexLength 3 = .ok 1 := rfl
    simp [nodeRoot, nodeRootAt, laid, mixed, depth, gindexBit, mixedReading,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have positive := shape.nesting_pos
    have notRoot : index ≠ 1 := by omega
    -- The contents’ initial left turn excludes the right-hand word even at the same depth.
    have notWord : index ≠ 3 := by
      rintro rfl
      cases leftSide
    have deep : Nat.log2 index ≠ 0 := by
      have recursion := levelOf_parent named
      change Nat.log2 index = _ at recursion
      omega
    rw [← nodeRootAt_eq_nodeRoot shape value index shape.nesting (Nat.le_refl _)]
    cases nesting : shape.nesting with
    | zero => omega
    | succ budget =>
      -- The enclosing type consumes one recursion level, matching the budget used for its materialized leaves.
      simp only [nesting, Nat.add_sub_cancel] at materialized
      simp only [nodeRootAt, show ¬index < 1 by omega, ↓reduceIte, beq_iff_eq, notRoot, bind, Except.bind,
        laid, gindexLength, gindexDepth, deep, mixed, Option.isSome_some, leftSide, Bool.false_eq_true,
        bounded, mixedReading, notWord]
      exact boundedNode_window (layoutChunksAt_window budget layout chunks materialized)
        index (Nat.log2 index - 1) 0 capacity inside

/-- Reading the right child of any mixed layout returns its word. -/
theorem nodeRoot_mixin {shape : Desc} {value : Value} {layout : MerkleLayout} {word : Bytes}
    (laid : merkleLayout shape value = .ok layout) (mixed : layout.mixin = some word) :
    nodeRoot shape value 3 = .ok word := by
  -- The right child ends after the mixing turn, so its leaves and capacity are irrelevant.
  have depth : gindexLength 3 = .ok 1 := rfl
  simp [nodeRoot, nodeRootAt, laid, mixed, depth, gindexBit,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

end EthLib.Serialization.Ssz
