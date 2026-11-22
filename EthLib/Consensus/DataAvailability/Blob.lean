module

public import EthLib.Consensus.Config
public import EthLib.Consensus.Containers.Block
public import EthLib.Serialization.Ssz.Codec.Proof
public import EthLib.Serialization.Ssz.Merkle.Branch
public import EthLib.Serialization.Ssz.Typed.Gindex

/-!
# `Consensus.DataAvailability.Blob`

From Deneb: the blob sidecars, which carry the blobs of a block apart from the block.

From Fulu, data column sidecars carry the blobs instead.

A sidecar holds one blob, its KZG commitment and proof, and the signed header of its block.

A Merkle branch shows that the commitment is in the body that the header names.

[EIP-4844] specifies blobs, and the sidecars that carry them on the network.

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#networking
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Cryptography.Kzg Serialization.Ssz

/-- A blob of a block, with its commitment, its proof, and a branch up to the block. -/
structure BlobSidecar (preset : Preset) where
  /-- The position of the blob among the blobs of the block. -/
  index : BlobIndex
  /-- The blob. -/
  blob : Blob
  /-- The commitment to the blob. -/
  kzgCommitment : KZGCommitment
  /-- The proof that the blob matches the commitment. -/
  kzgProof : KZGProof
  /-- The header of the block, signed by its proposer. -/
  signedBlockHeader : SignedBeaconBlockHeader
  /-- The branch from the commitment up to the root of the body, nearest node first. -/
  kzgCommitmentInclusionProof : Vector Bytes32 preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat
  deriving DecidableEq

instance {preset : Preset} : SszType (BlobSidecar preset) :=
  .container ["index", "blob", "kzg_commitment", "kzg_proof", "signed_block_header",
      "kzg_commitment_inclusion_proof"]
    (fun s => (s.index, s.blob, s.kzgCommitment, s.kzgProof, s.signedBlockHeader,
      s.kzgCommitmentInclusionProof))
    (fun (index, blob, kzgCommitment, kzgProof, signedBlockHeader, kzgCommitmentInclusionProof) =>
      ⟨index, blob, kzgCommitment, kzgProof, signedBlockHeader, kzgCommitmentInclusionProof⟩)

/-- The name of one blob sidecar: the root of its block and the index of its blob. -/
structure BlobIdentifier where
  /-- The root of the block. -/
  blockRoot : Root
  /-- The index of the blob in the block. -/
  index : BlobIndex
  deriving DecidableEq, Repr

instance : SszType BlobIdentifier :=
  .container ["block_root", "index"] (fun i => (i.blockRoot, i.index))
    (fun (blockRoot, index) => ⟨blockRoot, index⟩)

/-- The generalized index of the commitment at an index, in the tree of a block body. -/
def blobKzgCommitmentGindex (preset : Preset) (fork : Fork) (index : Nat) : Except Err Nat :=
  -- The path through the body: its field of blob commitments, then the position in that list.
  SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
    [.position ((BeaconBlockBody.names fork).idxOf "blob_kzg_commitments"), .position index]

/-- Whether the branch of a sidecar climbs from its commitment to the body root of its header. -/
def verifyBlobSidecarInclusionProof (preset : Preset) (fork : Fork)
    (sidecar : BlobSidecar preset) : Bool :=
  -- The leaf is the root of commitment `i`, for the index `i` of the sidecar.
  --
  -- Its place is the generalized index of commitment `i` in the body.
  match blobKzgCommitmentGindex preset fork sidecar.index.toNat,
      SszType.hashTreeRoot sidecar.kzgCommitment with
  | .ok gindex, .ok leaf =>
    -- Its position is that index among the nodes of its level.
    match getSubtreeIndex gindex with
    | .ok index =>
      -- The branch climbs `KZG_COMMITMENT_INCLUSION_PROOF_DEPTH` levels from the leaf.
      --
      -- It ends at the body root of the header.
      isValidMerkleBranch leaf sidecar.kzgCommitmentInclusionProof.toList
        preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat index
        sidecar.signedBlockHeader.message.bodyRoot
    -- An index that names no node fails the check.
    | .error _ => false
  -- A generalized index or a root that cannot be computed fails the check.
  | _, _ => false

/-- The most blob sidecars of one block: Electra raises the limit of Deneb, as [EIP-7691] says.

From Fulu blocks carry no blob sidecars, so the Electra limit stays.

The limits of gossip and of requests for blob sidecars both use it.

[EIP-7691]: https://eips.ethereum.org/EIPS/eip-7691#parameters -/
def blobSidecarLimit (config : Config) (fork : Fork) : UInt64 :=
  -- From Electra `MAX_BLOBS_PER_BLOCK_ELECTRA`, and before it `MAX_BLOBS_PER_BLOCK`.
  if .pectra ≤ fork then config.MAX_BLOBS_PER_BLOCK_ELECTRA else config.MAX_BLOBS_PER_BLOCK

/-- The largest number of blob sidecars in one request: the most blobs of the most blocks. -/
def computeMaxRequestBlobSidecars (config : Config) (fork : Fork) : UInt64 :=
  -- `MAX_REQUEST_BLOCKS_DENEB` times the blob limit of the fork.
  config.MAX_REQUEST_BLOCKS_DENEB * blobSidecarLimit config fork

/-- The header of a signed block, with the signature of the block. -/
def SignedBeaconBlock.signedHeader {preset : Preset} {fork : Fork}
    (signed : SignedBeaconBlock preset fork) : Except Err SignedBeaconBlockHeader := do
  -- The body gives way to its root.
  let bodyRoot ← SszType.hashTreeRoot signed.message.body
  -- The slot, the proposer index, the parent root and the state root stay, with the signature.
  return ⟨⟨signed.message.slot, signed.message.proposerIndex, signed.message.parentRoot,
    signed.message.stateRoot, bodyRoot⟩, signed.signature⟩

/-- The inclusion proof of the commitment at an index of a body, nearest node first. -/
def blobKzgCommitmentInclusionProof {preset : Preset} {fork : Fork}
    (body : BeaconBlockBody preset fork) (index : Nat) :
    Except Err (Vector Bytes32 preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat) := do
  -- The generalized index of the commitment at the index.
  let gindex ← blobKzgCommitmentGindex preset fork index
  -- The sibling of each node on the path from that index up to the body root, bottom up.
  let nodes ← buildProof (SszType.desc (BeaconBlockBody preset fork)) (SszType.toValue body) gindex
  -- Each sibling is one 32-byte chunk.
  let nodes ← nodes.mapM toChunk
  -- Any count of siblings other than `KZG_COMMITMENT_INCLUSION_PROOF_DEPTH` is an error.
  Base.exactArray preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat nodes.toArray
    (.count preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat)

/-- The sidecars of the blobs of a signed block, from Deneb until Gloas, whose body has no blobs.
-/
def getBlobSidecars {preset : Preset} {fork : Fork} (deneb : .dencun ≤ fork ∧ fork < .glamsterdam)
    (signed : SignedBeaconBlock preset fork) (blobs : List Blob) (proofs : List KZGProof) :
    Except Err (List (BlobSidecar preset)) := do
  -- The signed header of the block, which every sidecar carries.
  let header ← signed.signedHeader
  let commitments := (signed.message.body.blobKzgCommitments deneb).data
  -- Blob `i` takes commitment `i` of the body and proof `i`.
  (blobs.zipIdx).mapM fun (blob, index) => do
    -- A missing commitment or proof is an error.
    let some commitment := commitments[index]? | throw (.count blobs.length commitments.size)
    let some proof := proofs[index]? | throw (.count blobs.length proofs.length)
    -- The branch from commitment `i` up to the body root.
    let branch ← blobKzgCommitmentInclusionProof signed.message.body index
    -- The sidecar has the index `i`.
    return ⟨index.toUInt64, blob, commitment, proof, header, branch⟩

end EthLib.Consensus
