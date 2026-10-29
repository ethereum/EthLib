import EthLib.Consensus.Proofs.Ssz.Codec.LayoutProofTree
import EthLib.Consensus.Proofs.Ssz.Codec.NestedProof
import EthLib.Consensus.Proofs.Ssz.Type.PathLaws
import EthLib.Consensus.Proofs.Ssz.Codec.ProgressiveIndex

/-! Type paths select the same positions that the value walker reads. -/

namespace EthLib.Consensus.Ssz

/-- A reserved path step selects the right child carrying that type's mixed-in word. -/
theorem getGeneralizedIndex_mixin (shape : Desc) (step : PathStep)
    (supported : shape.mixesIn step = true) :
    getGeneralizedIndex shape [step] = .ok 3 := by
  -- Only length, active-field, and selector steps are supported by the matching type families.
  cases shape <;> cases step <;> simp only [Desc.mixesIn, Bool.false_eq_true] at supported
  all_goals with_unfolding_all rfl

/-- A reserved type path and the value walker agree on the mixed-in node. -/
theorem reserved_path_reads {shape : Desc} {value : Value} {layout : MerkleLayout}
    {step : PathStep} {word : Bytes} (supported : shape.mixesIn step = true)
    (laid : merkleLayout shape value = .ok layout) (mixed : layout.mixin = some word) :
    getGeneralizedIndex shape [step] = .ok 3 ∧ nodeRoot shape value 3 = .ok word := by
  -- The path names position three, and the executable walker returns exactly the layout's word.
  exact ⟨getGeneralizedIndex_mixin shape step supported, nodeRoot_mixin laid mixed⟩

/-- A field's generalized index has the bounded tree's leaf depth. -/
theorem bounded_leaf_depth {capacity ordinal : Nat} (selected : ordinal < capacity) :
    Nat.log2 (nextPow2 capacity + ordinal) = depthFor capacity := by
  -- Every leaf lies between the leading width bit and the next power of two.
  have room := le_two_pow_depthFor capacity
  have positive := Nat.two_pow_pos (depthFor capacity)
  apply (Nat.log2_eq_iff (by unfold nextPow2; omega)).mpr
  simp only [nextPow2, Nat.pow_succ]
  constructor <;> omega

/-- One mixed contents turn prefixes a bounded leaf without changing its ordinal. -/
theorem gindexConcat_mixed_leaf {capacity ordinal : Nat} (inside : ordinal < capacity) :
    gindexConcat 2 (nextPow2 capacity + ordinal) = .ok (2 * nextPow2 capacity + ordinal) := by
  -- The leaf's leading width bit is replaced by the mixed root's left-child prefix.
  have positive : 1 ≤ nextPow2 capacity + ordinal := by
    have := Nat.two_pow_pos (depthFor capacity); unfold nextPow2; omega
  rw [gindexConcat_eq (by decide) positive, bounded_leaf_depth inside]
  simp [nextPow2]

/-- The low turns of a field's index recover its ordinal. -/
theorem bounded_leaf_position {capacity ordinal : Nat} (selected : ordinal < capacity) :
    gindexBelow (nextPow2 capacity + ordinal) (depthFor capacity) = ordinal := by
  -- The leading width bit is removed by reduction modulo that width.
  have room := le_two_pow_depthFor capacity
  simp only [gindexBelow, nextPow2, Nat.add_mod, Nat.mod_self, Nat.zero_add]
  rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega : ordinal < 2 ^ depthFor capacity)]

/-- A bounded leaf reads the corresponding materialized chunk, including zero padding. -/
theorem nodeRoot_bounded_leaf {shape : Desc} {value : Value} {layout : MerkleLayout}
    {chunks : Array Bytes} {capacity ordinal : Nat}
    (laid : merkleLayout shape value = .ok layout)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (bounded : layout.limit = some capacity) (unmixed : layout.mixin = none)
    (fits : chunks.size ≤ capacity) (inside : ordinal < capacity) :
    nodeRoot shape value (nextPow2 capacity + ordinal) = .ok (padded zeroChunk chunks ordinal) := by
  -- At leaf depth the selected interval has one node, so no parent hash is added.
  have positive : 1 ≤ nextPow2 capacity + ordinal := Nat.le_add_right_of_le (Nat.two_pow_pos _)
  rw [nodeRoot_bounded_layout laid materialized bounded unmixed fits _ positive
    (by simp only [bounded_leaf_depth inside, Nat.le_refl])]
  simp [boundedReading, boundedTreeNode, bounded_leaf_depth inside,
    bounded_leaf_position inside, subtreeAt_eq_subtreeRoot, subtreeRoot]

/-- A bounded contents leaf adds one leading left turn before its ordinal. -/
theorem mixed_leaf_index {capacity ordinal : Nat} (inside : ordinal < capacity) :
    Nat.log2 (2 * nextPow2 capacity + ordinal) = depthFor capacity + 1 ∧
    gindexBit (2 * nextPow2 capacity + ordinal) (depthFor capacity) = false ∧
    gindexBelow (2 * nextPow2 capacity + ordinal) (depthFor capacity) = ordinal := by
  -- The quotient by the leaf width is two, whose low bit is the contents turn.
  have room := le_two_pow_depthFor capacity
  have power := Nat.two_pow_pos (depthFor capacity)
  have small : ordinal < 2 ^ depthFor capacity := by omega
  -- The high quotient is binary ten, recording the root bit followed by the contents’ left turn.
  have quotient : (2 * nextPow2 capacity + ordinal) / 2 ^ depthFor capacity = 2 := by
    rw [nextPow2, Nat.add_div (Nat.two_pow_pos _), Nat.mul_div_left _ power,
      Nat.div_eq_of_lt small]
    simp [Nat.mod_eq_of_lt small, small]
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.log2_eq_iff (by unfold nextPow2; omega)).mpr
    simp only [nextPow2, Nat.pow_succ]
    constructor <;> omega
  · simp [gindexBit, Nat.testBit_eq_decide_div_mod_eq, quotient]
  · simp [gindexBelow, nextPow2, Nat.add_mod, Nat.mod_eq_of_lt small]

/-- A bounded mixed leaf reads the same packed chunk beneath its length or selector. -/
theorem nodeRoot_mixed_leaf {shape : Desc} {value : Value} {layout : MerkleLayout}
    {chunks : Array Bytes} {capacity ordinal : Nat} {word : Bytes}
    (laid : merkleLayout shape value = .ok layout)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (bounded : layout.limit = some capacity) (mixed : layout.mixin = some word)
    (fits : chunks.size ≤ capacity) (inside : ordinal < capacity) :
    nodeRoot shape value (2 * nextPow2 capacity + ordinal) =
      .ok (padded zeroChunk chunks ordinal) := by
  -- The right-hand word does not change which chunk a left-hand leaf contains.
  obtain ⟨depth, turn, position⟩ := mixed_leaf_index inside
  have positive : 2 ≤ 2 * nextPow2 capacity + ordinal := by
    have := Nat.two_pow_pos (depthFor capacity); unfold nextPow2; omega
  -- A left-content leaf cannot be the right-hand mixing word at generalized index three.
  have notWord : 2 * nextPow2 capacity + ordinal ≠ 3 := by
    intro same
    rw [same, show Nat.log2 3 = 1 from rfl] at depth
    rw [same, show depthFor capacity = 0 by omega] at turn
    contradiction
  rw [nodeRoot_mixed_layout laid materialized bounded mixed fits _
    (Or.inr (Or.inr ⟨positive, by simpa [depth] using turn, by simp [depth]⟩))]
  simp [mixedReading, show 2 * nextPow2 capacity + ordinal ≠ 1 by omega, notWord,
    boundedTreeNode, depth, position, subtreeAt_eq_subtreeRoot, subtreeRoot]

/-- An occupied progressive chunk reads exactly its materialized leaf, without an extra hash. -/
theorem nodeRoot_progressive_leaf {shape : Desc} {value : Value} {layout : MerkleLayout}
    {chunks : Array Bytes} {word : Bytes} {ordinal : Nat}
    (laid : merkleLayout shape value = .ok layout)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (progressive : layout.limit = none) (mixed : layout.mixin = some word)
    (inside : ordinal < chunks.size) :
    nodeRoot shape value (progressiveChunkGindex ordinal) =
      .ok (padded zeroChunk chunks ordinal) := by
  -- The spine reaches an occupied segment, then the bounded walk ends at its selected leaf.
  have size := layoutChunksAt_size _ layout chunks materialized
  have present : ordinal < layout.leaves.count := by omega
  obtain ⟨stop, named, turn, walked, left, capacity, position, _⟩ :=
    progressiveChunkGindex_selection ordinal layout.leaves.count present
  -- The chosen progressive segment has a power-of-two capacity, giving its exact bounded-tree height.
  have height : depthFor stop.capacity = stop.depth := by rw [capacity, depthFor_pow]
  have depthPositive : Nat.log2 (progressiveChunkGindex ordinal) ≠ 0 := by
    have recursion := levelOf_parent named
    change Nat.log2 (progressiveChunkGindex ordinal) = _ at recursion
    omega
  have nesting := shape.nesting_pos
  rw [← nodeRootAt_eq_nodeRoot shape value _ shape.nesting (Nat.le_refl _)]
  cases depth : shape.nesting with
  | zero => omega
  | succ budget =>
    simp only [depth, Nat.add_sub_cancel] at materialized
    simp only [nodeRootAt, show ¬progressiveChunkGindex ordinal < 1 by omega, ↓reduceIte, beq_iff_eq,
      show progressiveChunkGindex ordinal ≠ 1 by omega, bind, Except.bind, laid, gindexLength, gindexDepth,
      depthPositive, mixed, Option.isSome_some, turn, Bool.false_eq_true, progressive, progressiveNode,
      walked, left]
    rw [boundedNode_window (layoutChunksAt_window budget layout chunks materialized)
      _ stop.depth stop.leavesFrom stop.capacity (by omega)]
    simp [boundedTreeNode, height, position, subtreeAt_eq_subtreeRoot, subtreeRoot]

end EthLib.Consensus.Ssz
