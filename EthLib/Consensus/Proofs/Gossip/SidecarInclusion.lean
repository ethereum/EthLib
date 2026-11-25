module

public import EthLib.Consensus.Proofs.DataAvailability.Column
public import EthLib.Consensus.Proofs.Gossip.Sidecar

/-!
# Proofs: the commitment roots that a valid sidecar binds to the block of its header

A sidecar travels without its block, so its commitments come with a branch.

The branch climbs from the commitments to the body root of the signed header.

Take a body whose root is the body root of the header, and the branch that a full node builds.

Suppose the body and the sidecar have different roots of commitments.

Then a search over the two climbs names two different 64-byte messages with one hash.

So the theorems take no assumption on the hash.

Blob sidecars come from [EIP-4844], and column sidecars from [EIP-7594].

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#consensus-layer-validation
[EIP-7594]: https://eips.ethereum.org/EIPS/eip-7594#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Kzg Networking.Gossip Networking.Gossip.ValidationResult Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {setup : TrustedSetup} {seen : Seen} {store : Store preset fork}
  {currentTimeMs subnetId : UInt64}
  [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- A valid blob sidecar carries the root of the commitment at its index in a matching body.

This holds at Deneb and Electra.

The full node builds the branch at both presets. -/
theorem validateBlobSidecar_accept_body {blobs : .dencun ≤ fork ∧ fork < .fusaka}
    {sidecar : BlobSidecar preset}
    (accepted : validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs
      subnetId = .ok accept)
    {body : BeaconBlockBody preset fork}
    -- Take a body whose root is the body root of the header.
    (rooted : SszType.hashTreeRoot body = .ok sidecar.signedBlockHeader.message.bodyRoot)
    {commitment : KZGCommitment}
    -- The body has a commitment at the index of the sidecar.
    (chosen : (body.blobKzgCommitments ⟨blobs.1, Nat.lt_trans blobs.2 (by decide)⟩).data[
      sidecar.index.toNat]? = some commitment)
    {branch : Vector Bytes32 preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat}
    -- Take the branch that the full node builds for that commitment.
    (built : blobKzgCommitmentInclusionProof body sidecar.index.toNat = .ok branch) :
    ∃ (gindex : Nat) (leaf other : Bytes32),
      blobKzgCommitmentGindex preset fork sidecar.index.toNat = .ok gindex ∧
      SszType.hashTreeRoot sidecar.kzgCommitment = .ok leaf ∧
      SszType.hashTreeRoot commitment = .ok other ∧
      -- That commitment has the root of the sidecar's commitment.
      --
      -- Otherwise the two climbs name two different 64-byte messages with one hash.
      (leaf = other ∨ ∃ a b, findBranchCollision gindex 0 ⟨leaf.toArray⟩ ⟨other.toArray⟩
          (sidecar.kzgCommitmentInclusionProof.toList.map fun node => ⟨node.toArray⟩)
          (branch.toList.map fun node => ⟨node.toArray⟩) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash a = Cryptography.Hash.Sha256.hash b) :=
  verifyBlobSidecarInclusionProof_body _ (validateBlobSidecar_accept accepted).2.2.1 rooted chosen
    built

/-- A valid column sidecar carries the root of the commitments of a matching body.

This holds at Fulu and the BPO forks.

The full node builds the branch at both presets. -/
theorem validateDataColumnSidecar_accept_body {columns : .fusaka ≤ fork ∧ fork < .glamsterdam}
    {sidecar : DataColumnSidecar preset fork}
    (accepted : validateDataColumnSidecar config checks setup seen store columns sidecar
      currentTimeMs subnetId = .ok accept)
    {body : BeaconBlockBody preset fork}
    -- Take a body whose root is the body root of the header.
    (rooted : SszType.hashTreeRoot body =
      .ok (sidecar.signedBlockHeader columns.2).message.bodyRoot)
    {branch : Vector Bytes32 preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat}
    -- Take the branch that the full node builds for the list of commitments of that body.
    (built : blobKzgCommitmentsInclusionProof body = .ok branch) :
    ∃ (leaf other : Bytes32),
      SszType.hashTreeRoot (sidecar.kzgCommitments columns.2) = .ok leaf ∧
      SszType.hashTreeRoot (body.blobKzgCommitments ⟨Nat.le_trans (by decide) columns.1,
        columns.2⟩) = .ok other ∧
      -- That list has the root of the sidecar's list.
      --
      -- Otherwise the two climbs name two different 64-byte messages with one hash.
      (leaf = other ∨ ∃ a b, findBranchCollision 27 0 ⟨leaf.toArray⟩ ⟨other.toArray⟩
          ((sidecar.kzgCommitmentsInclusionProof columns.2).toList.map fun node => ⟨node.toArray⟩)
          (branch.toList.map fun node => ⟨node.toArray⟩) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash a = Cryptography.Hash.Sha256.hash b) :=
  verifyDataColumnSidecarInclusionProof_body columns.1 columns.2
    (validateDataColumnSidecar_accept accepted).2.2.1 rooted built

end EthLib.Consensus
