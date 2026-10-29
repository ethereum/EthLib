import EthLib.Consensus.Proofs.Ssz.Merkle.MultiproofAcceptance
import EthLib.Consensus.Proofs.Ssz.Merkle.HelperAntichain

/-! Conflicting multiproof claims expose collisions in the hashes actually used to verify them. -/

namespace EthLib.Consensus.Ssz

private def suppliedNodes (leaves proof : List Bytes) (indices helpers : List Nat) :
    List (Nat × Bytes) :=
  -- Claims precede helpers, and equal validated lengths ensure neither zip drops a supplied value.
  indices.zip leaves ++ helpers.zip proof

/-- The validation facts needed to compare one accepted reconstruction with another. -/
private structure Reconstruction (leaves proof : List Bytes) (indices helpers : List Nat)
    (root : Bytes) : Prop where
  helperIndices : getHelperIndices indices = .ok helpers
  leafCount : leaves.length = indices.length
  proofCount : proof.length = helpers.length
  leafWidths : ∀ node ∈ leaves, node.size = bytesPerChunk
  proofWidths : ∀ node ∈ proof, node.size = bytesPerChunk
  folded : foldToRoot (multiproofHeight indices helpers)
    (suppliedNodes leaves proof indices helpers) = .ok root

private theorem reconstruction_of_accepted {leaves proof : List Bytes} {indices : List Nat}
    {root : Bytes} (accepted : verifyMerkleMultiproof leaves proof indices root = .ok true) :
    ∃ helpers, Reconstruction leaves proof indices helpers root := by
  -- Validation supplies the widths, while reconstruction supplies the canonical helper layout.
  obtain ⟨leafWidths, proofWidths, built⟩ := (verifyMerkleMultiproof_eq_true_iff ..).mp accepted
  obtain ⟨helpers, helperIndices, leafCount, proofCount, folded⟩ := calculateMultiMerkleRootUnchecked_shape built
  exact ⟨helpers, ⟨helperIndices, leafCount, proofCount, leafWidths, proofWidths, folded⟩⟩

namespace Reconstruction

variable {leaves proof : List Bytes} {indices helpers : List Nat} {root : Bytes}

private theorem positions (valid : Reconstruction leaves proof indices helpers root) :
    (suppliedNodes leaves proof indices helpers).map Prod.fst = indices ++ helpers := by
  -- Equal lengths prevent zip from dropping a claim or helper position.
  simp [suppliedNodes, List.map_fst_zip, valid.leafCount, valid.proofCount]

private theorem separated (valid : Reconstruction leaves proof indices helpers root) :
    ProofAntichain (suppliedNodes leaves proof indices helpers) := by
  -- Rejection of related claims extends to the canonical helper frontier.
  simpa only [ProofAntichain, valid.positions] using getHelperIndices_antichain valid.helperIndices

private theorem unique (valid : Reconstruction leaves proof indices helpers root) :
    ((suppliedNodes leaves proof indices helpers).map Prod.fst).Nodup := by
  -- Each supplied position has exactly one value, so lookup cannot hide another claim.
  exact valid.positions ▸ getHelperIndices_all_nodup valid.helperIndices

private theorem widths (valid : Reconstruction leaves proof indices helpers root) :
    ∀ index value, (index, value) ∈ suppliedNodes leaves proof indices helpers →
      value.size = bytesPerChunk := by
  -- Both halves of the frontier were validated before any hash was attempted.
  intro index value member
  rcases List.mem_append.mp member with leaf | helper
  · exact valid.leafWidths value (List.of_mem_zip leaf).2
  · exact valid.proofWidths value (List.of_mem_zip helper).2

private theorem rebuilt (valid : Reconstruction leaves proof indices helpers root) :
    (proofTree (suppliedNodes leaves proof indices helpers) (multiproofHeight indices helpers) 1).root = root := by
  -- The executable fold and the explicit finite tree perform the same reconstruction.
  exact (foldToRoot_eq_proofTree valid.separated valid.unique valid.folded).symm

private theorem claim (valid : Reconstruction leaves proof indices helpers root)
    {index : Nat} {value : Bytes} (member : (index, value) ∈ indices.zip leaves) :
    nodeAt (suppliedNodes leaves proof indices helpers) index = some value ∧
      1 ≤ index ∧ levelOf index ≤ multiproofHeight indices helpers := by
  -- A supplied claim is uniquely located and lies within the reconstruction height.
  have claimed := (List.of_mem_zip member).1
  have positive := (getHelperIndices_frontier valid.helperIndices).2.1 index claimed
  exact ⟨nodeAt_of_unique valid.unique (List.mem_append_left _ member), by omega,
    member_le_foldl_max (List.mem_map.mpr ⟨_, List.mem_append_left _ claimed, rfl⟩) 0⟩

private theorem message (valid : Reconstruction leaves proof indices helpers root)
    {input : Bytes} (hashed : input ∈
      (proofTree (suppliedNodes leaves proof indices helpers) (multiproofHeight indices helpers) 1).messages) :
    input ∈ verifiedMultiproofMessages leaves proof indices ∧ input.size = 64 := by
  -- Every tree hash occurs in the actual fold, and every operand is a complete node.
  have executed := proofTree_messages_executed valid.separated valid.unique valid.folded input hashed
  exact ⟨by simpa [verifiedMultiproofMessages, valid.helperIndices, suppliedNodes] using executed,
    CommitmentTree.messages_size _ (proofTree_complete valid.widths _ _) input hashed⟩

end Reconstruction

/--
Accepted requests for the same root cannot disagree at an overlapping claimed position without exposing a collision among the 64-byte inputs hashed by those requests.
-/
theorem verifyMerkleMultiproof_overlap_binding
    {leftLeaves leftProof rightLeaves rightProof : List Bytes}
    {leftIndices rightIndices : List Nat} {root firstValue secondValue : Bytes} {index : Nat}
    (leftAccepted : verifyMerkleMultiproof leftLeaves leftProof leftIndices root = .ok true)
    (rightAccepted : verifyMerkleMultiproof rightLeaves rightProof rightIndices root = .ok true)
    (leftClaim : (index, firstValue) ∈ leftIndices.zip leftLeaves)
    (rightClaim : (index, secondValue) ∈ rightIndices.zip rightLeaves) :
    firstValue = secondValue ∨
      ∃ first ∈ verifiedMultiproofMessages leftLeaves leftProof leftIndices,
      ∃ second ∈ verifiedMultiproofMessages rightLeaves rightProof rightIndices,
        first.size = 64 ∧ second.size = 64 ∧ first ≠ second ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk first) = Cryptography.Hash.Sha256.hash (ByteArray.mk second) := by
  -- Each accepted proof determines a complete finite reconstruction and locates the shared claim.
  obtain ⟨leftHelpers, left⟩ := reconstruction_of_accepted leftAccepted
  obtain ⟨rightHelpers, right⟩ := reconstruction_of_accepted rightAccepted
  obtain ⟨leftFound, positive, leftBound⟩ := left.claim leftClaim
  obtain ⟨rightFound, _, rightBound⟩ := right.claim rightClaim
  -- Compare only the common path.
  -- The sibling subtrees may have different shapes and heights.
  have binding := proofTree_opening_binding left.separated right.separated left.widths right.widths
    leftFound rightFound (Nat.log2 index) (multiproofHeight leftIndices leftHelpers)
    (multiproofHeight rightIndices rightHelpers) 1 leftBound rightBound (by decide)
    (shiftRight_depth positive) (left.rebuilt.trans right.rebuilt.symm)
  -- Locate both distinct compression inputs in the actual verifier executions.
  exact binding.imp id fun ⟨first, firstMember, second, secondMember, distinct, hashed⟩ =>
    ⟨first, (left.message firstMember).1, second, (right.message secondMember).1,
      (left.message firstMember).2, (right.message secondMember).2, distinct, hashed⟩

/--
Two accepted multiproofs for the same positions bind every claimed value.
A disagreement exposes distinct 64-byte inputs hashed by their actual reconstruction folds.
-/
theorem verifyMerkleMultiproof_binding {leftLeaves leftProof rightLeaves rightProof : List Bytes}
    {indices : List Nat} {root : Bytes}
    (leftAccepted : verifyMerkleMultiproof leftLeaves leftProof indices root = .ok true)
    (rightAccepted : verifyMerkleMultiproof rightLeaves rightProof indices root = .ok true) :
    leftLeaves = rightLeaves ∨
      ∃ first ∈ verifiedMultiproofMessages leftLeaves leftProof indices,
      ∃ second ∈ verifiedMultiproofMessages rightLeaves rightProof indices,
        first.size = 64 ∧ second.size = 64 ∧ first ≠ second ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk first) = Cryptography.Hash.Sha256.hash (ByteArray.mk second) := by
  -- Equal request positions give equal list lengths, so unequal claims differ at some position.
  obtain ⟨_, left⟩ := reconstruction_of_accepted leftAccepted
  obtain ⟨_, right⟩ := reconstruction_of_accepted rightAccepted
  have leftCount := left.leafCount
  have rightCount := right.leafCount
  by_cases collision : ∃ first ∈ verifiedMultiproofMessages leftLeaves leftProof indices,
      ∃ second ∈ verifiedMultiproofMessages rightLeaves rightProof indices,
        first.size = 64 ∧ second.size = 64 ∧ first ≠ second ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk first) = Cryptography.Hash.Sha256.hash (ByteArray.mk second)
  · exact .inr collision
  · refine .inl (List.ext_getElem (by omega) fun position leftBound rightBound => ?_)
    have indexBound : position < indices.length := by omega
    -- Every shared position is bound by the theorem for overlapping requests.
    have first : (indices[position], leftLeaves[position]) ∈ indices.zip leftLeaves :=
      List.mem_iff_getElem.mpr ⟨position, by simp; omega, by simp⟩
    have second : (indices[position], rightLeaves[position]) ∈ indices.zip rightLeaves :=
      List.mem_iff_getElem.mpr ⟨position, by simp; omega, by simp⟩
    exact (verifyMerkleMultiproof_overlap_binding leftAccepted rightAccepted first second).resolve_right collision

end EthLib.Consensus.Ssz
