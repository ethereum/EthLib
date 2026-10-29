import EthLib.Serialization.Proofs.Ssz.Merkle.MultiproofAcceptance

/-! Each multiproof claim read from a finite tree has a corresponding single-branch opening. -/

namespace EthLib.Serialization.Ssz

/-- Finite parent equations supply exactly the equations on a bounded branch. -/
theorem ParentsAgree.branchConsistent {tree : Nat → Bytes} {height index : Nat}
    (parents : ParentsAgree tree height) (named : 1 ≤ index)
    (bounded : levelOf index ≤ height) : BranchConsistent tree index := by
  -- Every branch step stays inside the finite height where parent equations are assumed.
  intro step below
  have positive := path_shift_positive named below
  have low : 2 ≤ index >>> step := positive
  have bound : levelOf (index >>> step) ≤ height :=
    Nat.le_trans (levelOf_mono (by omega) (shiftRight_le index step)) bounded
  rw [shiftRight_succ, gindexBit_parity]
  simp only [decide_eq_true_eq]
  -- Parity decides whether this path node is the left or right child of its parent.
  rcases Nat.mod_two_eq_zero_or_one (index >>> step) with even | odd
  · have adjacent : gindexSibling (index >>> step) = (index >>> step) + 1 := by
      have := gindexSibling_even even
      omega
    rw [ite_eq_right (by omega), adjacent]
    exact parents _ low bound even
  · rw [ite_eq_left odd]
    obtain ⟨-, sibling⟩ := gindexSibling_odd odd
    have side : 2 ≤ gindexSibling (index >>> step) := by omega
    have level : levelOf (gindexSibling (index >>> step)) ≤ height :=
      by rw [levelOf_sibling low]; exact bound
    have parity : gindexSibling (index >>> step) % 2 = 0 := by omega
    have adjacent : gindexSibling (index >>> step) + 1 = index >>> step := by omega
    have parent := parents _ side level parity
    rw [adjacent] at parent
    simpa [gindexParent, gindexSibling_half] using parent

/-- A claim read from a finite tree also has a valid single-branch opening. -/
theorem multiproof_claim_verifies {tree : Nat → Bytes}
    {leaves proof : List Bytes} {indices helpers : List Nat} {root : Bytes}
    (helperIndices : getHelperIndices indices = .ok helpers)
    (leafValues : NodesAgree tree (indices.zip leaves))
    (proofValues : NodesAgree tree (helpers.zip proof))
    (parents : ParentsAgree tree
      (((indices.zip leaves ++ helpers.zip proof).map fun pair => levelOf pair.1).foldl max 0))
    (widths : ∀ index, (tree index).size = bytesPerChunk)
    (accepted : verifyMerkleMultiproof leaves proof indices root = .ok true)
    {index : Nat} (claimed : index ∈ indices) :
    ∃ branch, getBranchIndices index = .ok branch ∧
      verifyMerkleProof (tree index) (branch.map tree) index root = .ok true := by
  -- The accepted multiproof fixes the root, while the selected path supplies its single-branch opening.
  have valid := (getHelperIndices_frontier helperIndices).2.1 index claimed
  have depth : Nat.log2 index ≠ 0 := by
    intro zero
    have := Nat.lt_log2_self (n := index)
    simp only [zero, Nat.zero_add, Nat.pow_one] at this
    omega
  -- Take one sibling at each depth, ordered from the claimed node toward the root.
  let branch := (List.range (Nat.log2 index)).map fun step => gindexSibling (index >>> step)
  have built : getBranchIndices index = .ok branch := by
    simp [getBranchIndices, getPathIndices, gindexLength, gindexDepth,
      show ¬index < 1 by omega, depth, Bind.bind, Except.bind, Pure.pure, Except.pure,
      List.map_map, Function.comp_def, branch]
  -- Agreement of the supplied nodes with the finite tree identifies the accepted root.
  have sameRoot := verifyMerkleMultiproof_agrees helperIndices leafValues proofValues parents accepted
  have checks := (verifyMerkleMultiproof_eq_true_iff ..).mp accepted
  have count : leaves.length = indices.length := by
    unfold calculateMultiMerkleRootUnchecked at checks
    split at checks
    · simp [throw, Bind.bind, Except.bind] at checks
    · next count => simpa using count
  -- The claim is retained in the initial node set because its value count was validated.
  have zipped : index ∈ (indices.zip leaves).map Prod.fst := by
    simpa [List.map_fst_zip, count] using claimed
  have inside : levelOf index ∈
      (indices.zip leaves ++ helpers.zip proof).map (fun pair => levelOf pair.1) := by
    obtain ⟨pair, member, same⟩ := List.mem_map.mp zipped
    exact List.mem_map.mpr ⟨pair, List.mem_append_left _ member, by simp [same]⟩
  -- The selected branch never needs a parent equation above the supplied finite height.
  have bound := member_le_foldl_max inside 0
  have consistent := parents.branchConsistent (index := index) (by omega) bound
  have reconstructed := branch_rebuilds_root_on_path consistent built
  refine ⟨branch, built, (verifyMerkleProof_eq_true_iff ..).mpr ?_⟩
  rw [sameRoot]
  exact ⟨widths index,
    fun node member => by obtain ⟨i, _, rfl⟩ := List.mem_map.mp member; exact widths i,
    reconstructed⟩

end EthLib.Serialization.Ssz
