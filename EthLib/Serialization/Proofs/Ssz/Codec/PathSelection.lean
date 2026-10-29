import EthLib.Serialization.Proofs.Ssz.Codec.PathProof
import EthLib.Serialization.Proofs.Ssz.Codec.PathDescent
import EthLib.Serialization.Proofs.Ssz.Codec.PathSlots
import EthLib.Serialization.Proofs.Ssz.Type.PathSteps

/-! Paths through present values select mixing words, packed chunks, and nested Merkle nodes. -/

namespace EthLib.Serialization.Ssz

/--
A path's value-level meaning, using actual layout positions rather than assumed successful reads.

Packed elements select their containing chunk.
Composite descent requires a filled slot, so absent list elements and layout gaps have no child.
Progressive payload selection requires a present chunk, although the Merkle walker also reads padding.
-/
inductive PathSelects : Desc → Value → List PathStep → Bytes → Prop where
  /-- An empty path selects the value's own Merkle root. -/
  | root {shape value node} (rooted : hashTreeRoot shape value = .ok node) :
      PathSelects shape value [] node
  /-- A reserved terminal step selects its type's mixing word. -/
  | word {shape value layout step word}
      (supported : shape.mixesIn step = true)
      (laid : merkleLayout shape value = .ok layout) (mixed : layout.mixin = some word) :
      PathSelects shape value [step] word
  /-- A fixed packed sequence selects the chunk containing the addressed element. -/
  | packed {shape value layout chunks capacity ordinal step child}
      (laid : merkleLayout shape value = .ok layout)
      (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
      (packed : layout.leaves = .packed chunks)
      (bounded : layout.limit = some capacity) (unmixed : layout.mixin = none)
      (fits : chunks.size ≤ capacity) (inside : ordinal < capacity)
      (resolved : shape.resolveStep step = .ok (nextPow2 capacity + ordinal, some child)) :
      PathSelects shape value [step] (padded zeroChunk chunks ordinal)
  /-- A bounded packed list selects its containing chunk beneath the length word. -/
  | packedMixed {shape value layout chunks capacity ordinal step child word}
      (laid : merkleLayout shape value = .ok layout)
      (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
      (packed : layout.leaves = .packed chunks)
      (bounded : layout.limit = some capacity) (mixed : layout.mixin = some word)
      (fits : chunks.size ≤ capacity) (inside : ordinal < capacity)
      (resolved : shape.resolveStep step = .ok (2 * nextPow2 capacity + ordinal, some child)) :
      PathSelects shape value [step] (padded zeroChunk chunks ordinal)
  /-- A progressive packed sequence selects an occupied chunk along its spine. -/
  | packedProgressive {shape value layout chunks ordinal step child word}
      (laid : merkleLayout shape value = .ok layout)
      (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
      (packed : layout.leaves = .packed chunks)
      (progressive : layout.limit = none) (mixed : layout.mixin = some word)
      (inside : ordinal < chunks.size)
      (resolved : shape.resolveStep step = .ok (progressiveChunkGindex ordinal, some child)) :
      PathSelects shape value [step] (padded zeroChunk chunks ordinal)
  /-- A fixed composite leaf delegates the remaining path to its actual child value. -/
  | nested {shape value layout chunks capacity ordinal step child inner rest node slots}
      (laid : merkleLayout shape value = .ok layout)
      (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
      (bounded : layout.limit = some capacity) (unmixed : layout.mixin = none)
      (fits : chunks.size ≤ capacity) (inside : ordinal < capacity)
      (nested : layout.leaves = .nested slots)
      (selected : slots[ordinal]? = some (some (child, inner)))
      (resolved : shape.resolveStep step = .ok (nextPow2 capacity + ordinal, some child))
      (suffix : PathSelects child inner rest node) :
      PathSelects shape value (step :: rest) node
  /-- A bounded mixed composite leaf delegates beneath the separate mixing word. -/
  | nestedMixed {shape value layout capacity ordinal step child inner rest node slots word}
      (laid : merkleLayout shape value = .ok layout)
      (bounded : layout.limit = some capacity) (mixed : layout.mixin = some word)
      (inside : ordinal < capacity) (nested : layout.leaves = .nested slots)
      (selected : slots[ordinal]? = some (some (child, inner)))
      (resolved : shape.resolveStep step = .ok (2 * nextPow2 capacity + ordinal, some child))
      (suffix : PathSelects child inner rest node) :
      PathSelects shape value (step :: rest) node
  /-- A progressive composite leaf delegates from its occupied position on the spine. -/
  | nestedProgressive {shape value layout ordinal step child inner rest node slots word}
      (laid : merkleLayout shape value = .ok layout)
      (progressive : layout.limit = none) (mixed : layout.mixin = some word)
      (nested : layout.leaves = .nested slots)
      (selected : slots[ordinal]? = some (some (child, inner)))
      (resolved : shape.resolveStep step = .ok (progressiveChunkGindex ordinal, some child))
      (suffix : PathSelects child inner rest node) :
      PathSelects shape value (step :: rest) node

private theorem leaf_named (capacity ordinal : Nat) : 1 ≤ nextPow2 capacity + ordinal := by
  -- Every leaf retains the leading bit of its bounded tree's width.
  have := Nat.two_pow_pos (depthFor capacity)
  unfold nextPow2
  omega

private theorem leaf_named_of_lt {capacity ordinal : Nat} (_inside : ordinal < capacity) :
    1 ≤ nextPow2 capacity + ordinal := leaf_named capacity ordinal

private theorem mixed_leaf_named (capacity ordinal : Nat) : 2 ≤ 2 * nextPow2 capacity + ordinal := by
  -- The extra leading left turn keeps every contents leaf below the root.
  have := Nat.two_pow_pos (depthFor capacity)
  unfold nextPow2
  omega

private theorem mixed_leaf_named_of_lt {capacity ordinal : Nat} (_inside : ordinal < capacity) :
    2 ≤ 2 * nextPow2 capacity + ordinal := mixed_leaf_named capacity ordinal

/-- Every semantically selected path resolves to exactly the node returned by the executable walker. -/
theorem PathSelects.reads {shape : Desc} {value : Value} {path : List PathStep} {node : Bytes}
    (selected : PathSelects shape value path node) :
    ∃ index, getGeneralizedIndex shape path = .ok index ∧ nodeRoot shape value index = .ok node := by
  -- A composite step splices the child's path, while a packed or mixing step ends at one node.
  induction selected with
  | root rooted => exact ⟨1, rfl, by simpa [nodeRoot_root] using rooted⟩
  | word supported laid mixed => exact ⟨3, reserved_path_reads supported laid mixed⟩
  | packed laid materialized packed bounded unmixed fits inside resolved =>
    refine ⟨_, getGeneralizedIndex_step resolved rfl (gindexConcat_root_right (leaf_named _ _)), ?_⟩
    exact nodeRoot_bounded_leaf laid materialized bounded unmixed fits inside
  | packedMixed laid materialized packed bounded mixed fits inside resolved =>
    refine ⟨_, getGeneralizedIndex_step resolved rfl
      (gindexConcat_root_right (Nat.le_trans (by decide : 1 ≤ 2) (mixed_leaf_named _ _))), ?_⟩
    exact nodeRoot_mixed_leaf laid materialized bounded mixed fits inside
  | packedProgressive laid materialized packed progressive mixed inside resolved =>
    -- Materialization preserves the chunk count needed to locate the occupied progressive segment.
    have count := layoutChunksAt_size _ _ _ materialized
    obtain ⟨_, positive, _⟩ := progressiveChunkGindex_selection _ _ (by omega : _ < _)
    refine ⟨_, getGeneralizedIndex_step resolved rfl (gindexConcat_root_right (by omega)), ?_⟩
    exact nodeRoot_progressive_leaf laid materialized progressive mixed inside
  | nested laid materialized bounded unmixed fits inside nested chosen resolved suffix ih =>
    -- The suffix already selects a definite node inside the actual child value.
    obtain ⟨innerIndex, typed, read⟩ := ih
    have positive := getGeneralizedIndex_positive _ _ _ typed
    -- Joining the outer leaf path retains every turn of the child’s remaining path.
    have joined := gindexConcat_eq (leaf_named_of_lt inside) positive
    refine ⟨_, getGeneralizedIndex_step resolved typed joined, ?_⟩
    rw [nodeRoot_bounded_splice _ _ _ laid _ materialized _ bounded unmixed fits _ nested
      _ _ _ _ _ (leaf_named _ _) positive joined (bounded_leaf_depth inside)
      (by simpa [bounded_leaf_position inside] using chosen)]
    exact read
  | nestedMixed laid bounded mixed inside nested chosen resolved suffix ih =>
    -- The suffix already selects a definite node inside the actual child value.
    obtain ⟨innerIndex, typed, read⟩ := ih
    have positive := getGeneralizedIndex_positive _ _ _ typed
    have outerNamed := mixed_leaf_named_of_lt inside
    -- Joining the outer leaf path retains every turn of the child’s remaining path.
    have joined := gindexConcat_eq (Nat.le_trans (by decide : 1 ≤ 2) outerNamed) positive
    obtain ⟨depth, turn, position⟩ := mixed_leaf_index inside
    refine ⟨_, getGeneralizedIndex_step resolved typed joined, ?_⟩
    rw [nodeRoot_mixed_bounded_splice _ _ _ laid _ bounded _ mixed _ nested _ _ _ _ _
      outerNamed positive joined (by simpa [depth] using turn) (by simp [depth])
      (by simpa [position] using chosen)]
    exact read
  | nestedProgressive laid progressive mixed nested chosen resolved suffix ih =>
    -- The suffix already selects a definite node inside the actual child value.
    obtain ⟨innerIndex, typed, read⟩ := ih
    have positive := getGeneralizedIndex_positive _ _ _ typed
    have inside := (List.getElem?_eq_some_iff.mp chosen).1
    obtain ⟨stop, outerNamed, turn, walked, left, capacity, position, _⟩ :=
      progressiveChunkGindex_selection _ _ (by simpa [nested, Leaves.count] using inside)
    -- Joining the outer leaf path retains every turn of the child’s remaining path.
    have joined := gindexConcat_eq (Nat.le_trans (by decide : 1 ≤ 2) outerNamed) positive
    -- At the selected progressive leaf, the remaining turns equal the segment’s complete binary-tree height.
    have height : stop.depth = depthFor stop.capacity := by rw [capacity, depthFor_pow]
    refine ⟨_, getGeneralizedIndex_step resolved typed joined, ?_⟩
    rw [nodeRoot_progressive_splice _ _ _ laid progressive _ nested _ _ _ _ _ outerNamed
      positive joined (by intro _ _; exact turn) stop
      (by simpa [mixed, nested, Leaves.count] using walked) left height
      (by simpa [← height, position] using chosen)]
    exact read

end EthLib.Serialization.Ssz
