module

public import EthLib.Serialization.Ssz.Typed.Gindex
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
public import EthLib.Serialization.Proofs.Ssz.Merkle.Branch
public import EthLib.Serialization.Proofs.Ssz.Codec.ProofCorrectness

/-!
# Proofs: branches of typed SSZ values

A branch built for a readable node of a typed value is a valid branch by depth and index.

Its depth and index come from the generalized index of the node.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType

/-- Nodes that are all 32 bytes wide are the bytes of some 32-byte vectors. -/
theorem exists_map_toArray : ∀ {nodes : List Bytes}, (∀ node ∈ nodes, node.size = 32) →
    ∃ chunks : List (Vector UInt8 32), chunks.map Vector.toArray = nodes
  | [], _ => ⟨[], rfl⟩
  | node :: rest, widths => by
    obtain ⟨chunks, mapped⟩ := exists_map_toArray fun other member =>
      widths other (List.mem_cons_of_mem _ member)
    exact ⟨⟨node, widths node List.mem_cons_self⟩ :: chunks, by simp [mapped]⟩

/-- An index of at least two names a node with a branch. -/
theorem getBranchIndices_ok {gindex : Nat} (named : 2 ≤ gindex) :
    ∃ indices, getBranchIndices gindex = .ok indices := by
  -- An index of at least two has its leading bit above bit zero.
  have positive : Nat.log2 gindex ≠ 0 := Nat.ne_of_gt (log2_pos named)
  have measured : gindexLength gindex = .ok (Nat.log2 gindex) := by
    have indexed : ¬gindex < 1 := by omega
    simp [gindexLength, gindexDepth, indexed, positive, bind, Except.bind]
  simp [getBranchIndices, getPathIndices, measured, bind, Except.bind, pure, Except.pure]

namespace SszType

variable {α : Type} [SszType α] [LawfulSszType α]

/--
A branch built for a readable node of a value is valid against the root of the value.

A node at generalized index `g` sits at depth `log2 g`, at index `g % 2^(log2 g)` of its level.
-/
theorem buildProof_isValidMerkleBranch (a : α) {gindex : Nat} (named : 2 ≤ gindex)
    {leaf : Vector UInt8 32} (read : nodeRoot (desc α) (toValue a) gindex = .ok leaf.toArray) :
    ∃ root branch, hashTreeRoot a = .ok root ∧
      buildProof (desc α) (toValue a) gindex = .ok (branch.map Vector.toArray) ∧
      isValidMerkleBranch leaf branch (Nat.log2 gindex) (gindex % 2 ^ Nat.log2 gindex) root =
        true := by
  obtain ⟨indices, indexed⟩ := getBranchIndices_ok named
  obtain ⟨root, nodes, rooted, built, verified⟩ := buildProof_fits_verifies (desc α) (toValue a)
    LawfulSszType.wellFormed (LawfulSszType.fits a) gindex _ read indices indexed
  obtain ⟨_, widths, rebuilt⟩ := (verifyMerkleProof_eq_true_iff ..).mp verified
  -- The branch nodes and the root are 32 bytes wide, so they are vectors.
  obtain ⟨branch, rfl⟩ := exists_map_toArray widths
  obtain ⟨vectorRoot, typedRoot⟩ := hashTreeRoot_total a
  have same : root = vectorRoot.toArray :=
    Except.ok.inj (rooted.symm.trans (hashTreeRoot_ok_iff.mp typedRoot))
  subst same
  refine ⟨vectorRoot, branch, typedRoot, built, ?_⟩
  -- The generalized index is its leading bit plus its index within its level.
  rw [isValidMerkleBranch_iff_verifyMerkleProof (log2_pos named)
    (Nat.mod_lt _ (Nat.two_pow_pos _)), two_pow_log2_add_mod (by omega)]
  exact verified

end SszType

end EthLib.Serialization.Ssz
