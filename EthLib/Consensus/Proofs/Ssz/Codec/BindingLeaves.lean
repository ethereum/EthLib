import EthLib.Consensus.Proofs.Ssz.Codec.BindingLeafShape
import EthLib.Consensus.Proofs.Ssz.Codec.BindingTraceLaws
import EthLib.Consensus.Proofs.Ssz.Codec.BindingCongruence

/-! Aligned layout computations authenticate their packed nodes and nested values. -/

namespace EthLib.Consensus.Ssz

/-- Materializing computations preserves the layout's number of leaf positions. -/
theorem layoutTreesAt_size {budget : Nat} {layout : MerkleLayout}
    {trees : Array CommitmentTree} (success : layoutTreesAt budget layout = .ok trees) :
    trees.size = layout.leaves.count := by
  -- Packed nodes are copied once each, and nested slots each produce one child computation.
  cases leaves : layout.leaves with
  | packed chunks =>
    simp only [layoutTreesAt, leaves, Except.ok.injEq] at success
    simp [← success, Leaves.count]
  | nested slots =>
    simpa only [leaves, Leaves.count] using
      layoutTreesAt_nested_size budget layout slots leaves trees success

/-- Recursive binding is needed only for present children at the two supplied layouts. -/
def LayoutChildrenBind (budget : Nat) (left right : MerkleLayout) : Prop :=
  -- Only children present in the two actual layouts participate in the recursive binding obligation.
  ∀ slotsLeft slotsRight child first second traceLeft traceRight,
    left.leaves = .nested slotsLeft → right.leaves = .nested slotsRight →
    some (child, first) ∈ slotsLeft → some (child, second) ∈ slotsRight →
    valueTreeAt budget child first = .ok traceLeft →
    valueTreeAt budget child second = .ok traceRight →
    traceLeft.root = traceRight.root →
    CommitmentTree.NoCollision traceLeft traceRight → first = second

/-- Equal collision-free layout roots preserve every aligned packed or nested leaf. -/
theorem layout_leaves_eq_of_noCollision {budget : Nat} {left right : MerkleLayout}
    {a b : Array CommitmentTree}
    (shaped : left.leaves.shapes = right.leaves.shapes)
    (limits : left.limit = right.limit)
    (tracedA : layoutTreesAt budget left = .ok a)
    (tracedB : layoutTreesAt budget right = .ok b)
    (roomA : ∀ cap, left.limit = some cap → a.size ≤ cap)
    (roomB : ∀ cap, right.limit = some cap → b.size ≤ cap)
    (completeA : (CommitmentTree.content a left.limit).Complete)
    (completeB : (CommitmentTree.content b right.limit).Complete)
    (clean : CommitmentTree.NoCollision
      (CommitmentTree.content a left.limit) (CommitmentTree.content b right.limit))
    (same : (CommitmentTree.content a left.limit).root =
      (CommitmentTree.content b right.limit).root)
    (children : LayoutChildrenBind budget left right) : left.leaves = right.leaves := by
  -- Matching leaf shapes imply the same number of positions in both materialized trees.
  have counts : a.size = b.size := by
    rw [layoutTreesAt_size tracedA, layoutTreesAt_size tracedB]
    exact Leaves.count_of_shapes shaped
  -- Equal collision-free contents roots authenticate every aligned child root.
  have roots := CommitmentTree.content_roots a b left.limit counts roomA completeA
    (limits.symm ▸ completeB) (limits.symm ▸ clean) (limits.symm ▸ same)
  cases l : left.leaves with
  | packed chunks =>
    cases r : right.leaves with
    | nested slots => simp [l, r, Leaves.shapes] at shaped
    -- A packed position is already its own root, so equality holds directly for its bytes.
    | packed other =>
      simp only [layoutTreesAt, l, Except.ok.injEq] at tracedA
      simp only [layoutTreesAt, r, Except.ok.injEq] at tracedB
      subst a b
      apply congrArg Leaves.packed
      -- Recover the packed arrays by their common count and equal node at each position.
      refine Array.ext (by simpa using counts) fun i hi _ => ?_
      have equal := roots i (by simpa using hi)
      simpa only [Array.getElem_map, CommitmentTree.root] using equal
  | nested slots =>
    cases r : right.leaves with
    | packed chunks => simp [l, r, Leaves.shapes] at shaped
    -- Nested positions instead require recovering the value behind each authenticated root.
    | nested others =>
      have aSize := layoutTreesAt_nested_size budget left slots l a tracedA
      have bSize := layoutTreesAt_nested_size budget right others r b tracedB
      have lengths : slots.length = others.length := by omega
      simp only [l, r, Leaves.shapes, Sum.inr.injEq] at shaped
      apply congrArg Leaves.nested
      apply List.ext_getElem lengths
      intro i hi hj
      -- The shape projection distinguishes gaps from occupied positions and identifies each child type.
      have types : (slots[i]).map Prod.fst = (others[i]).map Prod.fst := by
        have atIndex := congrArg (fun xs : List (Option Desc) => xs[i]!) shaped
        simpa only [getElem!_pos, List.length_map, hi, hj, List.getElem_map] using atIndex
      cases first : slots[i] <;> cases second : others[i] <;>
        simp only [first, second, Option.map, reduceCtorEq, Option.some.injEq] at types
      · rfl
      rename_i firstPair secondPair
      obtain ⟨child, firstValue⟩ := firstPair
      obtain ⟨otherChild, secondValue⟩ := secondPair
      subst types
      have boundA : i < a.size := by omega
      have boundB : i < b.size := by omega
      -- At each occupied position, materialization identifies the exact child computation.
      have firstTrace := layoutTreesAt_nested_getElem budget left slots l a tracedA
        i hi child firstValue first
      have secondTrace := layoutTreesAt_nested_getElem budget right others r b tracedB
        i hj child secondValue second
      -- Every child hash input also occurs in the enclosing contents tree.
      have includedA := CommitmentTree.content_included a left.limit roomA i boundA
      have includedB := CommitmentTree.content_included b right.limit roomB i boundB
      -- The enclosing collision-free assumption therefore restricts to these two child computations.
      have childClean := clean.restrict includedA includedB
      -- The recursive binding obligation recovers equal child values from their authenticated roots.
      have equal := children slots others child firstValue secondValue a[i] b[i] l r
        (first ▸ List.getElem_mem hi) (second ▸ List.getElem_mem hj)
        firstTrace secondTrace (roots i boundA) childClean
      exact congrArg (fun value => some (child, value)) equal

end EthLib.Consensus.Ssz
