module

public import EthLib.Serialization.Proofs.Ssz.Merkle.Multiproof
public import EthLib.Serialization.Proofs.Ssz.Merkle.CommitmentTree

/-! Accepted multiproofs have complete nodes and precisely the canonical reconstruction shape. -/

@[expose] public section

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

end EthLib.Serialization.Ssz
