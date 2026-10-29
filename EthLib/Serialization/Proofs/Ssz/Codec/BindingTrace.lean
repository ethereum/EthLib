import EthLib.Serialization.Proofs.Ssz.Merkle.CommitmentTree
import EthLib.Serialization.Ssz.Codec.Layout

/-! The expanded finite hash computation of an SSZ value, including its nested values. -/

namespace EthLib.Serialization.Ssz.CommitmentTree

/-- A perfect tree whose bottom positions may themselves contain nested computations. -/
def perfectTrees : Nat → (Nat → CommitmentTree) → CommitmentTree
  -- At depth zero, the selected child computation already supplies the whole subtree.
  | 0, leaves => leaves 0
  -- Each extra level combines equal-width halves, shifting the right half past the left.
  | depth + 1, leaves => .fork (perfectTrees depth leaves)
      (perfectTrees depth fun i => leaves (i + 2 ^ depth))

/-- Executing the expanded perfect tree agrees with folding its child roots. -/
@[simp] theorem perfectTrees_root (depth : Nat) (leaves : Nat → CommitmentTree) :
    (perfectTrees depth leaves).root = subtreeRoot combine depth (fun i => (leaves i).root) := by
  -- Each binary fork performs the same hash as the perfect-tree fold.
  induction depth generalizing leaves with
  | zero => rfl
  | succ depth ih => simp [perfectTrees, root, subtreeRoot, ih]

/-- Padding consists of plain zero nodes, as in the SSZ root computation. -/
def paddedTrees (trees : Array CommitmentTree) (i : Nat) : CommitmentTree :=
  -- Only positions beyond the supplied computations become plain zero leaves.
  trees[i]?.getD (.leaf zeroChunk)

/-- Padding a computation and padding its resulting root give the same node. -/
@[simp] theorem paddedTrees_root (trees : Array CommitmentTree) (i : Nat) :
    (paddedTrees trees i).root = padded zeroChunk (trees.map root) i := by
  -- Present positions keep their child roots, while absent positions read as 32 zero bytes.
  simp only [paddedTrees, padded, Array.getElem?_map]
  cases trees[i]? <;> rfl

/-- The perfect tree with its implicit zero padding expanded. -/
def bounded (trees : Array CommitmentTree) (capacity : Nat) : CommitmentTree :=
  -- The least sufficient perfect-tree depth includes the declared capacity.
  perfectTrees (depthFor capacity) (paddedTrees trees)

/-- Expanding a bounded tree preserves the executable subtree root. -/
@[simp] theorem bounded_root (trees : Array CommitmentTree) (capacity : Nat) :
    (bounded trees capacity).root = subtreeAt (trees.map root) (depthFor capacity) 0 := by
  -- The chosen depth and zero-padded leaf supply are the same on both sides.
  simp only [bounded, perfectTrees_root, paddedTrees_root, subtreeAt_zero_eq]

/-- The progressive spine of EIP-7916, retaining the nested computations at each position. -/
def progressive (trees : List CommitmentTree) (level : Nat := 0) : CommitmentTree :=
  -- An empty suffix ends the progressive spine with one zero node.
  if trees.isEmpty then .leaf zeroChunk
  -- The left subtree holds this level's prefix, with capacities 1, 4, 16, and so on.
  else .fork (bounded (trees.take (4 ^ level)).toArray (4 ^ level))
    -- The remaining positions continue on the right at four times the capacity.
    (progressive (trees.drop (4 ^ level)) (level + 1))
termination_by trees.length
decreasing_by
  -- Every nonempty level consumes at least one position, so the suffix strictly shortens.
  have positive : 0 < 4 ^ level := Nat.pos_of_neZero _
  have nonempty : 0 < trees.length := by cases trees <;> simp_all
  simp only [List.length_drop]
  omega

/-- Executing the expanded progressive spine preserves the executable root. -/
@[simp] theorem progressive_root (trees : List CommitmentTree) (level : Nat) :
    (progressive trees level).root = merkleizeProgressiveUnchecked (trees.map root) level := by
  -- Both computations consume the same prefix before continuing down the right spine.
  induction trees, level using progressive.induct with
  | case1 trees level empty => simp [progressive, merkleizeProgressiveUnchecked, empty, root]
  | case2 trees level nonempty ih =>
    -- The current level separates into a bounded prefix and the remaining progressive suffix.
    -- The suffix has the same root by recursion, and taking prefixes commutes with reading child roots.
    rw [progressive, ite_eq_right nonempty, merkleizeProgressiveUnchecked]
    simp only [List.isEmpty_map, nonempty, Bool.false_eq_true, ite_false, root,
      bounded_root, ih, List.map_toArray, List.map_take, List.map_drop]

/-- The bounded or progressive contents of one layout. -/
def content (trees : Array CommitmentTree) : Option Nat → CommitmentTree
  -- Progressive layouts have no fixed capacity and grow along the right spine.
  | none => progressive trees.toList
  -- A declared capacity selects a perfect tree with implicit zero padding.
  | some capacity => bounded trees capacity

/-- Attach the length, selector, or active-fields word, where the layout requires it. -/
def withMixin (tree : CommitmentTree) : Option Bytes → CommitmentTree
  -- Types without a mixing word commit directly to their contents tree.
  | none => tree
  -- Length, selector, or active-field information occupies the right child of the final hash.
  | some word => .fork tree (.leaf word)

/-- Attaching a mixing word preserves the executable final hash. -/
@[simp] theorem withMixin_root (tree : CommitmentTree) (mixin : Option Bytes) :
    (tree.withMixin mixin).root = match mixin with
      | none => tree.root
      | some word => mixIn tree.root word := by
  -- An absent word leaves the contents root alone.
  -- A present word becomes its right sibling.
  cases mixin <;> rfl

end EthLib.Serialization.Ssz.CommitmentTree

namespace EthLib.Serialization.Ssz

mutual

/--
The expanded Merkle computation, with intermediate hash inputs retained for proofs.
Zero padding is expanded instead of represented by cached subtree roots.
-/
def valueTreeAt : Nat → Desc → Value → Except Err CommitmentTree
  -- A depleted budget cannot descend into another value.
  | 0, _, _ => .error .proofIncomplete
  | budget + 1, shape, value => do
    -- The layout determines packing, nested positions, capacity, and optional metadata.
    let layout ← merkleLayout shape value
    -- Packed nodes become leaves, while nested values retain their own computations.
    let trees ← layoutTreesAt budget layout
    -- The presence of a capacity chooses a bounded tree or a progressive spine.
    let tree ← match layout.limit with
      | none => .ok (CommitmentTree.progressive trees.toList)
      | some capacity => do
        -- Reject a capacity that would omit supplied positions from the commitment.
        if capacity < trees.size then throw (.merkleizeLimit trees.size capacity)
        pure (CommitmentTree.bounded trees capacity)
    -- Metadata is authenticated only after the complete contents tree is formed.
    pure (tree.withMixin layout.mixin)

/-- Materialize the selected leaves while retaining each nested hash computation. -/
def layoutTreesAt (budget : Nat) (layout : MerkleLayout) : Except Err (Array CommitmentTree) :=
  match layout.leaves with
  -- Packed data is already divided into complete nodes and needs no recursive rooting.
  | .packed chunks => .ok (chunks.map CommitmentTree.leaf)
  | .nested slots => do
    -- Occupied positions recurse into their values, while layout gaps contribute zero nodes.
    let trees ← slots.mapM fun slot => match slot with
      | none => pure (.leaf zeroChunk)
      | some (shape, value) => valueTreeAt budget shape value
    -- Materialization preserves the order and number of layout positions.
    pure trees.toArray

end

/-- The entire computation selected by the type's own recursion budget. -/
def valueTree (shape : Desc) (value : Value) : Except Err CommitmentTree :=
  -- The type depth supplies enough recursion steps for every nested value.
  valueTreeAt shape.nesting shape value

end EthLib.Serialization.Ssz
