import EthLib.Serialization.Proofs.Ssz.Codec.WalkerLaws
import EthLib.Serialization.Proofs.Ssz.Codec.BranchConstruction
import EthLib.Serialization.Proofs.Ssz.Codec.NodeWidths
import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain

/-! Constructed branches authenticate readable nodes of a successfully rooted SSZ value. -/

namespace EthLib.Serialization.Ssz

/-- A constructed branch for any readable node rebuilds the value's own root. -/
theorem buildProof_rebuilds_value_root (shape : Desc) (value : Value) (root : Bytes)
    (rooted : hashTreeRoot shape value = .ok root) (index : Nat) (leaf : Bytes)
    (readLeaf : nodeRoot shape value index = .ok leaf) (indices : List Nat)
    (indexed : getBranchIndices index = .ok indices) :
    ∃ branch, buildProof shape value index = .ok branch ∧
      calculateMerkleRootUnchecked leaf branch index = .ok root := by
  -- Closure supplies all siblings, including transitions between nested value trees.
  obtain ⟨branch, rebuilt, built, readRoot, correct⟩ :=
    closed_branch_rebuilds_root (nodeRoot_closed shape value root rooted) indexed readLeaf
  -- The final ancestor is the value’s own root, not merely an unrelated readable node.
  rw [nodeRoot_root, rooted] at readRoot
  cases readRoot
  exact ⟨branch, by simpa only [buildProof, indexed, Bind.bind, Except.bind] using built, correct⟩

private theorem mapM_node_width (read : Nat → Except Err Bytes)
    (widths : ∀ index node, read index = .ok node → node.size = bytesPerChunk)
    (indices : List Nat) (nodes : List Bytes) (built : indices.mapM read = .ok nodes) :
    ∀ node ∈ nodes, node.size = bytesPerChunk := by
  -- Every output node comes from one successful read, so its width follows individually.
  induction indices generalizing nodes with
  | nil => simp_all [Pure.pure, Except.pure]
  | cons index rest ih =>
    cases head : read index <;> cases tail : rest.mapM read <;>
      simp [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
    subst nodes
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact widths index _ head
    · exact ih _ tail value member

/-- Every constructed branch for a readable node passes verification against the value's root. -/
theorem buildProof_verifies (shape : Desc) (value : Value) (root : Bytes)
    (rooted : hashTreeRoot shape value = .ok root)
    (index : Nat) (leaf : Bytes) (readLeaf : nodeRoot shape value index = .ok leaf)
    (indices : List Nat) (indexed : getBranchIndices index = .ok indices) :
    ∃ branch, buildProof shape value index = .ok branch ∧
      verifyMerkleProof leaf branch index root = .ok true := by
  -- Rebuilding supplies the root equality, while successful node reads supply all operand widths.
  have widths := nodeRoot_size shape value
  obtain ⟨branch, built, rebuilt⟩ :=
    buildProof_rebuilds_value_root shape value root rooted index leaf readLeaf indices indexed
  refine ⟨branch, built, (verifyMerkleProof_eq_true_iff leaf branch index root).mpr
    ⟨widths index leaf readLeaf, ?_, rebuilt⟩⟩
  -- Every generated sibling inherits its width from a successful node read.
  apply mapM_node_width (nodeRoot shape value) widths indices branch
  simpa only [buildProof, indexed, Bind.bind, Except.bind] using built

/-- An admissible value has a root and a verified branch for every readable non-root node. -/
theorem buildProof_fits_verifies (shape : Desc) (value : Value)
    (sound : shape.wellFormed = .ok ()) (fitted : Fits shape value)
    (index : Nat) (leaf : Bytes) (readLeaf : nodeRoot shape value index = .ok leaf)
    (indices : List Nat) (indexed : getBranchIndices index = .ok indices) :
    ∃ root branch, hashTreeRoot shape value = .ok root ∧
      buildProof shape value index = .ok branch ∧ verifyMerkleProof leaf branch index root = .ok true := by
  -- Admissibility supplies the root, and walker closure supplies the complete authenticated branch.
  obtain ⟨root, rooted, _⟩ := hashTreeRoot_total shape value sound fitted
  obtain ⟨branch, built, verified⟩ :=
    buildProof_verifies shape value root rooted index leaf readLeaf indices indexed
  exact ⟨root, branch, rooted, built, verified⟩

end EthLib.Serialization.Ssz
