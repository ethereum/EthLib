module

public import EthLib.Consensus.Proofs.DataAvailability.Column
public import EthLib.Consensus.Proofs.Gossip.Sidecar

/-!
# Proofs: what a valid sidecar proves about the block of its header

A sidecar travels without its block, so its commitments come with a branch.

The branch climbs from the commitments to the body root of the signed header.

Take a valid sidecar and any block body whose root is that body root.

A blob sidecar then carries the root of the commitment at its index in that body.

A column sidecar carries the root of the list of commitments of that body.

Otherwise the two climbs hash two different messages to one SHA-256 output.

So the theorems take no assumption on the hash.

They hold for the mainnet and minimal presets, whose proof depths are those of the body type.

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

/-- A valid blob sidecar carries the commitment of its index in the block of its header.

Take any body whose root is the body root of the header, with a commitment at that index.

That commitment has the root of the sidecar's one, or two climbs give a SHA-256 collision.

This holds for both presets. -/
theorem validateBlobSidecar_accept_body {blobs : .dencun ≤ fork ∧ fork < .fusaka}
    {sidecar : BlobSidecar preset} (named : preset = .mainnet ∨ preset = .minimal)
    (accepted : validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs
      subnetId = .ok accept)
    {body : BeaconBlockBody preset fork}
    (rooted : SszType.hashTreeRoot body = .ok sidecar.signedBlockHeader.message.bodyRoot)
    {commitment : KZGCommitment}
    (chosen : (body.blobKzgCommitments ⟨blobs.1, Nat.lt_trans blobs.2 (by decide)⟩).data[
      sidecar.index.toNat]? = some commitment) :
    ∃ (leaf other : Bytes32) (index : Nat) (nodes : List Bytes32),
      SszType.hashTreeRoot sidecar.kzgCommitment = .ok leaf ∧
      SszType.hashTreeRoot commitment = .ok other ∧
      (leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray
          (sidecar.kzgCommitmentInclusionProof.toList.map Vector.toArray),
        ∃ b ∈ branchMessages index 0 other.toArray (nodes.map Vector.toArray),
          a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
          Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
            Cryptography.Hash.Sha256.hash (ByteArray.mk b)) :=
  verifyBlobSidecarInclusionProof_body named _ (validateBlobSidecar_accept accepted).2.2.1
    rooted chosen

/-- A valid column sidecar carries the commitments of the block of its header.

Take any body whose root is the body root of the header.

Its list of commitments has the root of the sidecar's list, or two climbs give a SHA-256 collision.

This holds for both presets. -/
theorem validateDataColumnSidecar_accept_body {columns : .fusaka ≤ fork ∧ fork < .glamsterdam}
    {sidecar : DataColumnSidecar preset fork} (named : preset = .mainnet ∨ preset = .minimal)
    (accepted : validateDataColumnSidecar config checks setup seen store columns sidecar
      currentTimeMs subnetId = .ok accept)
    {body : BeaconBlockBody preset fork}
    (rooted : SszType.hashTreeRoot body =
      .ok (sidecar.signedBlockHeader columns.2).message.bodyRoot) :
    ∃ (leaf other : Bytes32) (index : Nat) (nodes : List Bytes32),
      SszType.hashTreeRoot (sidecar.kzgCommitments columns.2) = .ok leaf ∧
      SszType.hashTreeRoot (body.blobKzgCommitments ⟨Nat.le_trans (by decide) columns.1,
        columns.2⟩) = .ok other ∧
      (leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray
          ((sidecar.kzgCommitmentsInclusionProof columns.2).toList.map Vector.toArray),
        ∃ b ∈ branchMessages index 0 other.toArray (nodes.map Vector.toArray),
          a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
          Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
            Cryptography.Hash.Sha256.hash (ByteArray.mk b)) :=
  verifyDataColumnSidecarInclusionProof_body named columns.1 columns.2
    (validateDataColumnSidecar_accept accepted).2.2.1 rooted

end EthLib.Consensus
