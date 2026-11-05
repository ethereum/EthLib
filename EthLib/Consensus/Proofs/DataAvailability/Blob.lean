module

public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container
public import EthLib.Serialization.Proofs.Ssz.Merkle.Branch

/-!
# Proofs: the blob sidecar containers are lawful

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it.

Two sidecars whose branches verify for one blob of one block carry one commitment root.

Otherwise the two climbs to the body root hash two different messages to one SHA-256 output.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

instance : NeZero Cryptography.Kzg.Constants.BYTES_PER_BLOB := ⟨by decide⟩

instance {preset : Preset} [NeZero preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat] :
    LawfulSszType (BlobSidecar preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BlobIdentifier := .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- Two sidecars that verify for one blob index and one body root have one commitment root.

Otherwise the two climbs hash two different messages to one SHA-256 output. -/
theorem verifyBlobSidecarInclusionProof_binding {preset : Preset} {fork : Fork}
    {first second : BlobSidecar preset} (sameIndex : first.index = second.index)
    (sameRoot :
      first.signedBlockHeader.message.bodyRoot = second.signedBlockHeader.message.bodyRoot)
    (firstValid : verifyBlobSidecarInclusionProof preset fork first = true)
    (secondValid : verifyBlobSidecarInclusionProof preset fork second = true) :
    ∃ leaf other index, SszType.hashTreeRoot first.kzgCommitment = .ok leaf ∧
      SszType.hashTreeRoot second.kzgCommitment = .ok other ∧
      (leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray
          (first.kzgCommitmentInclusionProof.toList.map Vector.toArray),
        ∃ b ∈ branchMessages index 0 other.toArray
          (second.kzgCommitmentInclusionProof.toList.map Vector.toArray),
          a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
          Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
            Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  unfold verifyBlobSidecarInclusionProof at firstValid secondValid
  rw [← sameIndex] at secondValid
  cases gindex : blobKzgCommitmentGindex preset fork first.index.toNat with
  | error fault => simp [gindex] at firstValid
  | ok g =>
    cases leafRoot : SszType.hashTreeRoot first.kzgCommitment with
    | error fault => simp [gindex, leafRoot] at firstValid
    | ok leaf =>
      cases otherRoot : SszType.hashTreeRoot second.kzgCommitment with
      | error fault => simp [gindex, otherRoot] at secondValid
      | ok other =>
        cases subtree : getSubtreeIndex g with
        | error fault => simp [gindex, leafRoot, subtree] at firstValid
        | ok index =>
          simp only [gindex, leafRoot, subtree] at firstValid
          simp only [gindex, otherRoot, subtree, ← sameRoot] at secondValid
          exact ⟨leaf, other, index, rfl, rfl, isValidMerkleBranch_binding firstValid secondValid⟩

end EthLib.Consensus
