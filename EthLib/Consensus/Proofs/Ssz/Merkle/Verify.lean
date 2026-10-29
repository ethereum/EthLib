import EthLib.Consensus.Ssz.Merkle.Verify
import EthLib.Consensus.Proofs.Ssz.Merkle.Gindex
import EthLib.Consensus.Proofs.Ssz.Merkle.Tree

/-! Laws of branch verification: what climbing a branch folds, and when it rebuilds a root. -/

namespace EthLib.Consensus.Ssz

/-- A node and its sibling combine to the node above them, in whichever order they sit. -/
theorem combine_sibling {node : Nat → Bytes} (tree : MerkleTree node) (index : Nat)
    (named : 1 ≤ index / 2) :
    (if index % 2 = 1 then combine (node (gindexSibling index)) (node index)
      else combine (node index) (node (gindexSibling index))) = node (index / 2) := by
  rw [tree _ named]
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · -- An even node is the left child, so the sibling joins on the right.
    obtain ⟨whole, pair⟩ := gindexSibling_even even
    rw [ite_eq_right (by omega), ← pair, ← whole]
  · -- An odd node is the right child, so the sibling joins on the left.
    obtain ⟨whole, pair⟩ := gindexSibling_odd odd
    rw [ite_eq_left odd, ← whole, ← pair]

/-- One level of the climb joins a node with its sibling, giving the node above them. -/
theorem climbBranch_step {node : Nat → Bytes} (tree : MerkleTree node) (index level : Nat)
    (named : 1 ≤ index >>> (level + 1)) :
    (if gindexBit index level then combine (node (gindexSibling (index >>> level)))
        (node (index >>> level))
      else combine (node (index >>> level)) (node (gindexSibling (index >>> level))))
      = node (index >>> (level + 1)) := by
  -- Climbing one level is halving, and the turn taken is the parity of what is halved.
  rw [shiftRight_succ] at named ⊢
  rw [gindexBit_parity]
  simp only [decide_eq_true_eq]
  exact combine_sibling tree (index >>> level) named

/-- A node shifted further up is no larger than the same node shifted less. -/
theorem shiftRight_le (index level : Nat) : index >>> level ≤ index := by
  -- Shifting is dividing by a power of two, which never grows a number.
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self index (2 ^ level)

/--
Climbing a branch of a Merkle tree arrives at the node above every level it climbed.

The branch is read as the tree's own siblings, one per level, from the leaf upward.
-/
theorem climbBranch_folds {node : Nat → Bytes} (tree : MerkleTree node) :
    ∀ (count index level : Nat), 1 ≤ index >>> (level + count) →
      climbBranch index level (node (index >>> level))
          ((List.range count).map fun step => node (gindexSibling (index >>> (level + step))))
        = node (index >>> (level + count)) := by
  intro count
  induction count with
  | zero =>
    -- Nothing to climb, so the node reached is the one the walk opened on.
    intro index level _
    simp [climbBranch]
  | succ count ih =>
    intro index level reaches
    -- The first sibling is the one at this level, and the rest belong one level up.
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero, climbBranch]
    -- The remaining climb still has to reach the root, which is what it opened able to do.
    have onward : 1 ≤ index >>> (level + 1 + count) := by
      rwa [Nat.add_assoc, Nat.add_comm 1]
    -- One level of the climb is a node joined with its sibling, which is the node above.
    have above : 1 ≤ index >>> (level + 1) :=
      Nat.le_trans onward (by rw [Nat.shiftRight_add]; exact shiftRight_le _ _)
    rw [climbBranch_step tree index level above]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih index (level + 1) onward

/-- Reading an index that names a node gives its depth, which is at least one level. -/
theorem gindexLength_ok {index depth : Nat} (measured : gindexLength index = .ok depth) :
    depth = Nat.log2 index ∧ 1 ≤ index ∧ depth ≠ 0 := by
  -- A number naming no node is refused, and so is the root, which sits on no branch.
  unfold gindexLength gindexDepth at measured
  split at measured
  · cases measured
  · simp only [Bind.bind, Except.bind] at measured
    split at measured
    · cases measured
    · cases measured
      simp_all
      omega

/-- The branch of an index is the tree's siblings, one per level below the root. -/
theorem getBranchIndices_eq {index : Nat} {branch : List Nat}
    (built : getBranchIndices index = .ok branch) :
    branch = (List.range (Nat.log2 index)).map (fun step => gindexSibling (index >>> step))
      ∧ 1 ≤ index ∧ Nat.log2 index ≠ 0 := by
  -- The walk upward names one ancestor per level, and the branch is what sits beside them.
  unfold getBranchIndices getPathIndices at built
  cases measured : gindexLength index <;>
    simp [measured, Bind.bind, Except.bind, pure, Except.pure, List.map_map, Function.comp_def] at built
  obtain ⟨rfl, positive, deep⟩ := gindexLength_ok measured
  exact ⟨built.symm, positive, deep⟩

/-- A climb reaches its last ancestor when each step agrees with its parent. -/
theorem climbBranch_folds_on_path (node : Nat → Bytes) (index : Nat) :
    ∀ count level,
      (∀ step, level ≤ step → step < level + count →
        (if gindexBit index step then
          combine (node (gindexSibling (index >>> step))) (node (index >>> step))
        else combine (node (index >>> step)) (node (gindexSibling (index >>> step))))
          = node (index >>> (step + 1))) →
      climbBranch index level (node (index >>> level))
        ((List.range count).map fun step => node (gindexSibling (index >>> (level + step))))
        = node (index >>> (level + count)) := by
  intro count
  induction count with
  | zero =>
    -- An empty branch leaves the current node unchanged.
    intro level _
    simp [climbBranch]
  | succ count ih =>
    intro level parents
    -- Peel off the first sibling, then start the remaining climb one level higher.
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero, climbBranch]
    rw [parents level (by omega) (by omega)]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (level + 1) (fun step lower upper => parents step (by omega) (by omega))

/-- A branch rebuilds the root using only the parent equations along that branch. -/
theorem branch_rebuilds_root_on_path {node : Nat → Bytes} {index : Nat}
    (parents : BranchConsistent node index) {branch : List Nat}
    (built : getBranchIndices index = .ok branch) :
    calculateMerkleRootUnchecked (node index) (branch.map node) index = .ok (node 1) := by
  -- The index determines both the branch length and the sibling order.
  obtain ⟨spelled, named, deep⟩ := getBranchIndices_eq built
  subst spelled
  have notZero : index ≠ 0 := by omega
  have measured : gindexLength index = .ok (Nat.log2 index) := by
    simp [gindexLength, gindexDepth, Bind.bind, Except.bind, notZero, deep]
  -- No equation is needed below the claimed node or on an unrelated branch.
  have climbed := climbBranch_folds_on_path node index (Nat.log2 index) 0
    (fun step _ upper => parents step (by omega))
  simp only [Nat.zero_add, Nat.shiftRight_zero] at climbed
  rw [shiftRight_depth named] at climbed
  simp [calculateMerkleRootUnchecked, measured, Bind.bind, Except.bind, List.map_map,
    Function.comp_def, climbed, pure, Except.pure]

/--
Every branch this library builds rebuilds the root of the tree it was read from.

Nothing about the leaves is assumed, only that each node is the two below it combined.
-/
theorem branch_rebuilds_root {node : Nat → Bytes} (tree : MerkleTree node) {index : Nat}
    {branch : List Nat} (built : getBranchIndices index = .ok branch) :
    calculateMerkleRootUnchecked (node index) (branch.map node) index = .ok (node 1) := by
  obtain ⟨spelled, named, deep⟩ := getBranchIndices_eq built
  subst spelled
  -- The branch is as long as the index is deep, so the verifier accepts its length.
  have notZero : ¬ index = 0 := by omega
  have measured : gindexLength index = .ok (Nat.log2 index) := by
    simp [gindexLength, gindexDepth, Bind.bind, Except.bind, notZero, deep]
  -- Climbing every level the index carries arrives at the root, which is where it stops.
  have climbed := climbBranch_folds tree (Nat.log2 index) index 0
  simp only [Nat.zero_add, Nat.shiftRight_zero] at climbed
  rw [shiftRight_depth named] at climbed
  simp [calculateMerkleRootUnchecked, measured, Bind.bind, Except.bind, List.map_map, Function.comp_def,
    climbed, pure, Except.pure]

end EthLib.Consensus.Ssz
