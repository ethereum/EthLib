import EthLib.Serialization.Proofs.Ssz.Merkle.MultiproofTrace

/-! Accepted multiproofs have complete nodes and precisely the canonical reconstruction shape. -/

namespace EthLib.Serialization.Ssz

/-- Acceptance validates every node width and reconstructs exactly the expected root. -/
theorem verifyMerkleMultiproof_eq_true_iff (leaves proof : List Bytes)
    (indices : List Nat) (root : Bytes) :
    verifyMerkleMultiproof leaves proof indices root = .ok true ↔
      (∀ node ∈ leaves, node.size = bytesPerChunk) ∧
      (∀ node ∈ proof, node.size = bytesPerChunk) ∧
      calculateMultiMerkleRootUnchecked leaves proof indices = .ok root := by
  -- Reconstruction runs first, then the claimed and helper widths, then the comparison.
  simp only [verifyMerkleMultiproof, calculateMultiMerkleRoot, ← checkChunks_ok_iff]
  cases calculateMultiMerkleRootUnchecked leaves proof indices <;> cases checkChunks leaves <;>
    cases checkChunks proof <;>
    simp_all [Bind.bind, Except.bind, pure, Except.pure]

/-- Successful reconstruction fixes the counts, helper indices, and exact level fold. -/
theorem calculateMultiMerkleRootUnchecked_shape {leaves proof : List Bytes} {indices : List Nat}
    {root : Bytes} (built : calculateMultiMerkleRootUnchecked leaves proof indices = .ok root) :
    ∃ helpers, getHelperIndices indices = .ok helpers ∧ leaves.length = indices.length ∧
      proof.length = helpers.length ∧
      foldToRoot (multiproofHeight indices helpers)
        (indices.zip leaves ++ helpers.zip proof) = .ok root := by
  -- Accepted counts make both zipped sequences retain every position in the canonical frontier.
  unfold calculateMultiMerkleRootUnchecked at built
  split at built
  · simp [throw, Bind.bind, Except.bind] at built
  · rename_i lengths
    have lengths : leaves.length = indices.length := by simpa using lengths
    cases helperIndices : getHelperIndices indices <;>
      simp only [helperIndices, Bind.bind, Except.bind, reduceCtorEq] at built
    rename_i helpers
    split at built
    · simp [throw] at built
    · rename_i proofLengths
      have proofLengths : proof.length = helpers.length := by simpa using proofLengths
      refine ⟨helpers, rfl, lengths, proofLengths, ?_⟩
      -- The validated counts make index projection recover the entire claim-plus-helper sequence.
      have positions : (indices.zip leaves ++ helpers.zip proof).map Prod.fst = indices ++ helpers := by
        simp [List.map_fst_zip, lengths, proofLengths]
      -- The initial maximum depth then depends only on those positions, not on the node bytes.
      have height := congrArg (fun xs => (xs.map levelOf).foldl max 0) positions
      simp only [List.map_map, Function.comp_def] at height
      simpa only [height, multiproofHeight] using built

end EthLib.Serialization.Ssz
