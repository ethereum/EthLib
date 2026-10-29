import EthLib.Serialization.Proofs.Ssz.Codec.NestedProof
import EthLib.Serialization.Proofs.Ssz.Type.PathLaws
import EthLib.Serialization.Proofs.Ssz.Codec.LayoutProofTree

/-! A path spliced below a composite leaf reads the same node inside that value. -/

namespace EthLib.Serialization.Ssz

/-- Dropping the appended turns recovers the outer generalized index. -/
theorem gindexSplice_prefix (outer inner : Nat) (named : 1 ≤ inner) :
    (outer * 2 ^ Nat.log2 inner + (inner - 2 ^ Nat.log2 inner)) >>> Nat.log2 inner = outer := by
  -- The removed inner leading bit leaves a remainder strictly smaller than its binary width.
  obtain ⟨lower, upper⟩ := gindexDepth_bounds named
  -- The appended suffix cannot carry into the outer path because its width excludes the removed leading bit.
  have remainder : inner - 2 ^ Nat.log2 inner < 2 ^ Nat.log2 inner := by
    rw [Nat.pow_succ] at upper
    omega
  rw [Nat.shiftRight_eq_div_pow, Nat.add_div (Nat.two_pow_pos _)]
  simp [Nat.div_eq_of_lt remainder, Nat.mod_eq_of_lt remainder, remainder, Nat.two_pow_pos]

/-- Splicing a path beneath a filled bounded leaf agrees with reading that nested value directly. -/
theorem boundedNode_splice (layout : MerkleLayout) (budget : Nat)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (value : Value) (enough : child.nesting ≤ budget)
    (outer inner start capacity : Nat) (named : 1 ≤ inner)
    (selected : slots[start + gindexBelow outer (depthFor capacity)]? = some (some (child, value))) :
    boundedNode budget layout
      (outer * 2 ^ Nat.log2 inner + (inner - 2 ^ Nat.log2 inner))
      (depthFor capacity + Nat.log2 inner) start capacity = nodeRoot child value inner := by
  -- The outer leaf consumes its bounded height, leaving precisely the appended inner path.
  have remaining : depthFor capacity + Nat.log2 inner - depthFor capacity = Nat.log2 inner := by omega
  rw [boundedNode_nested_at layout budget slots nested child value enough _ _ start capacity
    (by omega) (by simpa only [remaining, gindexSplice_prefix outer inner named] using selected)]
  rw [remaining, gindexRebase_splice outer inner named]

/-- A successful generalized-index splice has the same nested-value reading. -/
theorem boundedNode_concat (layout : MerkleLayout) (budget : Nat)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (value : Value) (enough : child.nesting ≤ budget)
    (outer inner index start capacity : Nat) (outerNamed : 1 ≤ outer) (innerNamed : 1 ≤ inner)
    (joined : gindexConcat outer inner = .ok index)
    (selected : slots[start + gindexBelow outer (depthFor capacity)]? = some (some (child, value))) :
    boundedNode budget layout index (depthFor capacity + Nat.log2 inner) start capacity =
      nodeRoot child value inner := by
  -- The executable concatenation is the same leading-bit splice used by the leaf-descent law.
  rw [gindexConcat_eq outerNamed innerNamed] at joined
  cases joined
  exact boundedNode_splice layout budget slots nested child value enough outer inner start capacity
    innerNamed selected

/-- Appending low turns leaves every earlier turn of the path unchanged. -/
theorem gindexBit_append (outer combined extra position : Nat)
    (shifted : combined >>> extra = outer) :
    gindexBit combined (position + extra) = gindexBit outer position := by
  -- Shifting away the appended suffix exposes the original bit positions.
  rw [← shifted]
  simp [gindexBit, Nat.testBit_shiftRight, Nat.add_comm]

/-- Appended turns stay inside the same progressive level after its left turn has been taken. -/
theorem spineWalk_append_left (count outer combined extra : Nat)
    (shifted : combined >>> extra = outer) :
    ∀ depth start capacity stop,
      spineWalk count outer depth start capacity = .ok stop → stop.turnedLeft = true →
      spineWalk count combined (depth + extra) start capacity =
        .ok ⟨stop.depth + extra, stop.leavesFrom, stop.capacity, true⟩ := by
  -- Right turns follow the unchanged spine prefix until the same left turn enters a level.
  intro depth
  induction depth with
  | zero =>
    intro start capacity stop walked left
    simp [spineWalk] at walked
    simp [← walked] at left
  | succ depth ih =>
    intro start capacity stop walked left
    have bit := gindexBit_append outer combined extra depth shifted
    -- Appending low turns extends the remaining depth without changing the next spine decision.
    have extended : depth + 1 + extra = depth + extra + 1 := by omega
    rw [extended, spineWalk]
    simp only [spineWalk] at walked
    by_cases empty : start ≥ count
    · simp [empty, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at walked
    · simp only [ite_eq_right empty] at walked ⊢
      rw [bit]
      -- The preserved turn either exits at the same bounded segment or continues along the same spine prefix.
      cases turn : gindexBit outer depth with
      | false =>
        simp [turn, Pure.pure, Except.pure] at walked
        simp [← walked, Pure.pure, Except.pure]
      | true =>
        simp only [turn, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at walked ⊢
        exact ih _ _ _ walked left

/-- A suffix appended beneath a progressive composite leaf reads that nested value directly. -/
theorem progressiveNode_splice (layout : MerkleLayout) (budget : Nat)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (value : Value) (enough : child.nesting ≤ budget)
    (outer inner depth start capacity : Nat) (named : 1 ≤ inner) (stop : SpineStop)
    (walked : spineWalk layout.leaves.count outer depth start capacity = .ok stop)
    (left : stop.turnedLeft = true) (atLeaf : stop.depth = depthFor stop.capacity)
    (selected : slots[stop.leavesFrom + gindexBelow outer (depthFor stop.capacity)]? =
      some (some (child, value))) :
    progressiveNode budget layout
      (outer * 2 ^ Nat.log2 inner + (inner - 2 ^ Nat.log2 inner))
      (depth + Nat.log2 inner) start capacity = nodeRoot child value inner := by
  -- The spine keeps the outer prefix, then the bounded level consumes only its own height.
  -- Appending low turns extends the remaining depth without changing the next spine decision.
  have extended := spineWalk_append_left layout.leaves.count outer
    (outer * 2 ^ Nat.log2 inner + (inner - 2 ^ Nat.log2 inner)) (Nat.log2 inner)
    (gindexSplice_prefix outer inner named) depth start capacity stop walked left
  simp only [progressiveNode, extended, Bind.bind, Except.bind, ↓reduceIte, atLeaf]
  exact boundedNode_splice layout budget slots nested child value enough outer inner
    stop.leavesFrom stop.capacity named selected

/-- A non-root path entering the contents uses the canonical bounded or progressive walker. -/
theorem nodeRoot_left_contents (shape : Desc) (value : Value) (layout : MerkleLayout)
    (laid : merkleLayout shape value = .ok layout) (index : Nat) (named : 2 ≤ index)
    (left : ∀ word, layout.mixin = some word →
      gindexBit index (Nat.log2 index - 1) = false) :
    nodeRoot shape value index =
      (let turns := if layout.mixin.isSome then Nat.log2 index - 1 else Nat.log2 index
       match layout.limit with
       | some capacity => boundedNode (shape.nesting - 1) layout index turns 0 capacity
       | none => progressiveNode (shape.nesting - 1) layout index turns 0 1) := by
  -- A left mixing turn, when present, leaves the rest of the path inside the contents tree.
  have positive : 0 < shape.nesting := shape.nesting_pos
  have depthPositive : Nat.log2 index ≠ 0 := by
    have := levelOf_parent named; simp only [levelOf] at this; omega
  rw [← nodeRootAt_eq_nodeRoot shape value index shape.nesting (Nat.le_refl _)]
  cases depth : shape.nesting with
  | zero => omega
  | succ budget =>
    simp only [Nat.add_sub_cancel]
    simp only [nodeRootAt, show ¬index < 1 by omega, ↓reduceIte, beq_iff_eq, show index ≠ 1 by omega, bind,
      Except.bind, laid, gindexLength, gindexDepth, depthPositive, bne_iff_ne, ne_eq, ite_not]
    cases mixed : layout.mixin with
    | none => simp; cases layout.limit <;> rfl
    | some word => simp [left word mixed]; cases layout.limit <;> rfl

private theorem nodeRoot_bounded_unmixed (shape : Desc) (value : Value) (layout : MerkleLayout)
    (laid : merkleLayout shape value = .ok layout) (chunks : Array Bytes)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (capacity : Nat) (bounded : layout.limit = some capacity) (unmixed : layout.mixin = none)
    (fits : chunks.size ≤ capacity) (index : Nat) (named : 1 ≤ index) :
    nodeRoot shape value index =
      boundedNode (shape.nesting - 1) layout index (Nat.log2 index) 0 capacity := by
  -- The root uses the full materialized tree, and every lower node uses the same bounded walk.
  by_cases atRoot : index = 1
  · subst index
    rw [nodeRoot_root, hashTreeRoot_bounded_layout laid materialized bounded fits, unmixed]
    have read := boundedNode_window
      (layoutChunksAt_window (shape.nesting - 1) layout chunks materialized) 1 0 0 capacity (by omega)
    simpa [boundedTreeNode, gindexBelow, show Nat.log2 1 = 0 from rfl] using read.symm
  · rw [nodeRoot_left_contents shape value layout laid index (by omega)
      (by intro word same; rw [unmixed] at same; cases same)]
    simp [bounded, unmixed]

/-- Concatenating a path beneath an unmixed bounded composite leaf reads the nested value. -/
theorem nodeRoot_bounded_splice (shape : Desc) (value : Value) (layout : MerkleLayout)
    (laid : merkleLayout shape value = .ok layout) (chunks : Array Bytes)
    (materialized : layoutChunksAt (shape.nesting - 1) layout = .ok chunks)
    (capacity : Nat) (bounded : layout.limit = some capacity) (unmixed : layout.mixin = none)
    (fits : chunks.size ≤ capacity)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (innerValue : Value) (outer inner index : Nat)
    (outerNamed : 1 ≤ outer) (innerNamed : 1 ≤ inner)
    (joined : gindexConcat outer inner = .ok index) (leafDepth : Nat.log2 outer = depthFor capacity)
    (selected : slots[gindexBelow outer (depthFor capacity)]? = some (some (child, innerValue))) :
    nodeRoot shape value index = nodeRoot child innerValue inner := by
  -- The full path has the bounded leaf depth followed by the inner suffix depth.
  -- The selected child is strictly shallower than its enclosing declaration, so the remaining budget covers it.
  have smaller := merkleLayout_child_nesting shape value layout laid slots nested child innerValue
    (List.mem_of_getElem? selected)
  have enough : child.nesting ≤ shape.nesting - 1 := by omega
  rw [nodeRoot_bounded_unmixed shape value layout laid chunks materialized capacity bounded unmixed
    fits index (gindexConcat_positive joined), gindexConcat_depth joined, leafDepth]
  exact boundedNode_concat layout (shape.nesting - 1) slots nested child innerValue enough
    outer inner index 0 capacity outerNamed innerNamed joined (by simpa using selected)

private theorem concat_left_turn (outer inner index : Nat) (named : 2 ≤ outer)
    (joined : gindexConcat outer inner = .ok index)
    (left : gindexBit outer (Nat.log2 outer - 1) = false) :
    2 ≤ index ∧ gindexBit index (Nat.log2 index - 1) = false ∧
      Nat.log2 index - 1 = (Nat.log2 outer - 1) + Nat.log2 inner := by
  -- Appending turns preserves the leading left choice and adds only lower path depth.
  obtain ⟨_, innerNamed, value⟩ := gindexConcat_facts joined
  -- Removing the appended suffix recovers the original outer address.
  have shifted : index >>> Nat.log2 inner = outer := by
    rw [value]; exact gindexSplice_prefix outer inner innerNamed
  have outerDepth : 0 < Nat.log2 outer := by
    have := levelOf_parent named; simp only [levelOf] at this; omega
  have depth := gindexConcat_depth joined
  have remaining : Nat.log2 index - 1 = (Nat.log2 outer - 1) + Nat.log2 inner := by omega
  refine ⟨?_, ?_, remaining⟩
  · have := shifted ▸ shiftRight_le index (Nat.log2 inner); omega
  · rw [remaining, gindexBit_append outer index (Nat.log2 inner) (Nat.log2 outer - 1) shifted, left]

/-- Concatenating a path beneath mixed bounded contents reads the selected nested value. -/
theorem nodeRoot_mixed_bounded_splice (shape : Desc) (value : Value) (layout : MerkleLayout)
    (laid : merkleLayout shape value = .ok layout) (capacity : Nat)
    (bounded : layout.limit = some capacity) (word : Bytes) (mixed : layout.mixin = some word)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (innerValue : Value) (outer inner index : Nat)
    (outerNamed : 2 ≤ outer) (innerNamed : 1 ≤ inner)
    (joined : gindexConcat outer inner = .ok index)
    (left : gindexBit outer (Nat.log2 outer - 1) = false)
    (leafDepth : Nat.log2 outer - 1 = depthFor capacity)
    (selected : slots[gindexBelow outer (depthFor capacity)]? = some (some (child, innerValue))) :
    nodeRoot shape value index = nodeRoot child innerValue inner := by
  -- The mixing turn is retained, followed by the same bounded leaf and appended nested path.
  obtain ⟨indexNamed, indexLeft, depth⟩ := concat_left_turn outer inner index outerNamed joined left
  -- The selected child is strictly shallower than its enclosing declaration, so the remaining budget covers it.
  have smaller := merkleLayout_child_nesting shape value layout laid slots nested child innerValue
    (List.mem_of_getElem? selected)
  rw [nodeRoot_left_contents shape value layout laid index indexNamed (by intro _ _; exact indexLeft)]
  simp only [mixed, Option.isSome_some, ↓reduceIte, bounded, depth, leafDepth]
  exact boundedNode_concat layout (shape.nesting - 1) slots nested child innerValue (by omega)
    outer inner index 0 capacity (by omega) innerNamed joined (by simpa using selected)

/-- A path appended beneath a progressive leaf reads the nested value across the same spine prefix. -/
theorem nodeRoot_progressive_splice (shape : Desc) (value : Value) (layout : MerkleLayout)
    (laid : merkleLayout shape value = .ok layout) (progressive : layout.limit = none)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (innerValue : Value) (outer inner index : Nat)
    (outerNamed : 2 ≤ outer) (innerNamed : 1 ≤ inner)
    (joined : gindexConcat outer inner = .ok index)
    (left : ∀ word, layout.mixin = some word → gindexBit outer (Nat.log2 outer - 1) = false)
    (stop : SpineStop)
    (walked : spineWalk layout.leaves.count outer
      (if layout.mixin.isSome then Nat.log2 outer - 1 else Nat.log2 outer) 0 1 = .ok stop)
    (turned : stop.turnedLeft = true) (atLeaf : stop.depth = depthFor stop.capacity)
    (selected : slots[stop.leavesFrom + gindexBelow outer (depthFor stop.capacity)]? =
      some (some (child, innerValue))) :
    nodeRoot shape value index = nodeRoot child innerValue inner := by
  -- The spine stop identifies the containing level before any appended turns are consumed.
  obtain ⟨_, _, combined⟩ := gindexConcat_facts joined
  -- The selected child is strictly shallower than its enclosing declaration, so the remaining budget covers it.
  have smaller := merkleLayout_child_nesting shape value layout laid slots nested child innerValue
    (List.mem_of_getElem? selected)
  have enough : child.nesting ≤ shape.nesting - 1 := by omega
  -- Removing the appended suffix recovers the original outer address.
  have shifted : index >>> Nat.log2 inner = outer := by
    rw [combined]; exact gindexSplice_prefix outer inner innerNamed
  have indexNamed : 2 ≤ index := by
    have := shifted ▸ shiftRight_le index (Nat.log2 inner); omega
  -- Appending a child path preserves the initial left turn past a mixing word.
  have indexLeft : ∀ word, layout.mixin = some word → gindexBit index (Nat.log2 index - 1) = false :=
    fun word mixed => (concat_left_turn outer inner index outerNamed joined (left word mixed)).2.1
  rw [nodeRoot_left_contents shape value layout laid index indexNamed indexLeft]
  have descend := progressiveNode_splice layout (shape.nesting - 1) slots nested child innerValue
    enough outer inner _ 0 1 innerNamed stop walked turned atLeaf selected
  cases mixed : layout.mixin with
  | none =>
    simpa only [progressive, mixed, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      gindexConcat_depth joined, ← combined] using descend
  | some word =>
    have depth := (concat_left_turn outer inner index outerNamed joined (left word mixed)).2.2
    simpa only [progressive, mixed, Option.isSome_some, ↓reduceIte, depth, ← combined] using descend

end EthLib.Serialization.Ssz
