module

public import EthLib.Consensus.Gossip.Attestation
public import EthLib.Consensus.Gossip.Block

/-!
# `Consensus.Gossip.Sidecar`

Gossip validation of the sidecars that carry the data of a block.

At Deneb and Electra a blob sidecar carries one blob.

From Fulu a column sidecar carries one column of the extended blobs.

A sidecar must be the first valid one of its proposer, its slot and its index.

It must have a valid shape and travel on the subnet of its index.

Its signed header then passes the checks of a block, in the same order.

So the header must not be early, and must build on a known valid parent after the finalized slot.

Its proposer must have signed it, and must be the proposer that the parent state expects.

Before that last check, the sidecar must prove its data.

Its branch must climb from its commitments to the body root of its header.

Its KZG proofs must match its commitments.

A proof that the KZG checks cannot read is an error, since the rule raises there.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Networking.Gossip Cryptography.Kzg

variable {preset : Preset} {fork : Fork}

/-- The checks of the signed header of a sidecar, from the clock to the expected proposer.

The noun names the sidecar in the reasons, and the signed noun names its header there.

The proofs of the data run after the finalized ancestor and before the expected proposer. -/
def validateSidecarHeader (config : Config) (checks : SignatureChecks) (store : Store preset fork)
    (noun signedNoun : String) (signed : SignedBeaconBlockHeader) (currentTimeMs : UInt64)
    (proofs : Unit → Except ForkChoiceError ValidationResult) :
    Except ForkChoiceError ValidationResult := do
  let header := signed.message
  let future ← store.isFutureSlot config header.slot currentTimeMs
  (ignoreUnless (!future) s!"{noun} is from a future slot").andThenM fun _ => do
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot < header.slot)
    s!"{noun} is not from a slot greater than the latest finalized slot").andThenM fun _ => do
  match store.blocks[header.parentRoot]? with
  | none => return .ignore s!"{noun}'s parent has not been seen"
  | some parent => do
  match store.blockStates[header.parentRoot]? with
  | none => return .reject s!"{noun}'s parent failed validation"
  | some parentState => do
  let state ← store.headState config
  match state.validators.data[header.proposerIndex.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer => do
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER header.slot header
    proposer.pubkey signed.signature
  (rejectUnless valid s!"invalid proposer signature on {signedNoun}").andThenM fun _ =>
  (rejectUnless (parent.slot < header.slot)
    s!"{noun} is not from a higher slot than its parent").andThenM fun _ => do
  let finalizedBlock ← store.getCheckpointBlock header.parentRoot store.finalizedCheckpoint.epoch
  (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
    s!"finalized checkpoint is not an ancestor of {noun}'s block").andThenM fun _ => do
  (← proofs ()).andThenM fun _ => do
  let expected ← expectedProposer config checks parentState header.slot
  return rejectUnless (header.proposerIndex == expected)
    s!"{noun} proposer_index does not match expected proposer"

/-- The key of a blob sidecar among the keys seen: its slot, its proposer and its index. -/
def blobSidecarKey (sidecar : BlobSidecar preset) : Slot × ValidatorIndex × BlobIndex :=
  (sidecar.signedBlockHeader.message.slot, sidecar.signedBlockHeader.message.proposerIndex,
    sidecar.index)

/-- The number of blobs that a block may carry: Electra raises the limit of Deneb. -/
def blobSidecarLimit (config : Config) (fork : Fork) : UInt64 :=
  if .pectra ≤ fork then config.MAX_BLOBS_PER_BLOCK_ELECTRA else config.MAX_BLOBS_PER_BLOCK

/-- The proofs of a blob sidecar: its branch to the body root, then its KZG proof. -/
def blobSidecarProofs (setup : TrustedSetup) (fork : Fork) (sidecar : BlobSidecar preset) :
    Except ForkChoiceError ValidationResult :=
  (rejectUnless (verifyBlobSidecarInclusionProof preset fork sidecar)
    "invalid blob sidecar inclusion proof").andThenM fun _ => do
  let valid ← (verifyBlobKzgProof setup sidecar.blob sidecar.kzgCommitment
    sidecar.kzgProof).mapError .kzg
  return rejectUnless valid "invalid blob kzg proof"

/-- At Deneb and Electra: the checks of a blob sidecar on a subnet, at a time in milliseconds.

The index must name a blob within the limit of the fork. -/
def validateBlobSidecar (config : Config) (checks : SignatureChecks) (setup : TrustedSetup)
    (seen : Seen) (store : Store preset fork) (_blobs : .dencun ≤ fork ∧ fork < .fusaka)
    (sidecar : BlobSidecar preset) (currentTimeMs subnetId : UInt64) :
    Except ForkChoiceError ValidationResult :=
  (ignoreUnless (!seen.blobSidecarTuples.contains (blobSidecarKey sidecar))
    "already seen blob sidecar from this proposer for this slot and index").andThenM fun _ =>
  (rejectUnless (sidecar.index < blobSidecarLimit config fork)
    "blob index out of range").andThenM fun _ => do
  let subnet ← (computeSubnetForBlobSidecar config fork sidecar.index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "blob sidecar is for wrong subnet").andThenM fun _ =>
  validateSidecarHeader config checks store "blob sidecar" "blob sidecar block header"
    sidecar.signedBlockHeader currentTimeMs fun _ => blobSidecarProofs setup fork sidecar

/-- The keys after a valid blob sidecar: its slot, its proposer and its index. -/
def Seen.recordBlobSidecar (seen : Seen) (sidecar : BlobSidecar preset) : Seen :=
  { seen with blobSidecarTuples := blobSidecarKey sidecar :: seen.blobSidecarTuples }

/-- Before Gloas a column carries its commitments, so the bid of its block is never read. -/
def noBidBeforeGloas (before : fork < .glamsterdam) :
    Since .glamsterdam fork (BlobKZGCommitments preset fork) :=
  fun gloas => absurd gloas (not_glamsterdam_le before)

/-- From Fulu, before Gloas: the key of a column sidecar, its slot, its proposer and its index. -/
def dataColumnSidecarKey (before : fork < .glamsterdam) (sidecar : DataColumnSidecar preset fork) :
    Slot × ValidatorIndex × DataAvailability.ColumnIndex :=
  ((sidecar.signedBlockHeader before).message.slot,
    (sidecar.signedBlockHeader before).message.proposerIndex, sidecar.index)

/-- Before Gloas: the proofs of a column sidecar, its branch then its KZG proofs. -/
def dataColumnSidecarProofs (setup : TrustedSetup) (before : fork < .glamsterdam)
    (sidecar : DataColumnSidecar preset fork) : Except ForkChoiceError ValidationResult :=
  (rejectUnless (verifyDataColumnSidecarInclusionProof preset before sidecar)
    "invalid sidecar inclusion proof").andThenM fun _ => do
  let valid ← (verifyDataColumnSidecarKzgProofs setup sidecar (noBidBeforeGloas before)).mapError
    .kzg
  return rejectUnless valid "invalid sidecar kzg proofs"

/-- From Fulu, before Gloas: the checks of a column sidecar on a subnet, at a time in milliseconds.

The column must have a valid shape, with no more commitments than the blob schedule allows. -/
def validateDataColumnSidecar (config : Config) (checks : SignatureChecks) (setup : TrustedSetup)
    (seen : Seen) (store : Store preset fork) (columns : .fusaka ≤ fork ∧ fork < .glamsterdam)
    (sidecar : DataColumnSidecar preset fork) (currentTimeMs subnetId : UInt64) :
    Except ForkChoiceError ValidationResult :=
  (ignoreUnless (!seen.dataColumnSidecarTuples.contains (dataColumnSidecarKey columns.2 sidecar))
    "already seen sidecar from this proposer for this slot and index").andThenM fun _ =>
  (rejectUnless (verifyDataColumnSidecar preset config sidecar (noBidBeforeGloas columns.2))
    "invalid sidecar").andThenM fun _ => do
  let subnet ← (computeSubnetForDataColumnSidecar config sidecar.index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "sidecar is for wrong subnet").andThenM fun _ =>
  validateSidecarHeader config checks store "sidecar" "sidecar block header"
    (sidecar.signedBlockHeader columns.2) currentTimeMs fun _ =>
  dataColumnSidecarProofs setup columns.2 sidecar

/-- From Fulu, before Gloas: the keys after a valid column sidecar. -/
def Seen.recordDataColumnSidecar (seen : Seen) (before : fork < .glamsterdam)
    (sidecar : DataColumnSidecar preset fork) : Seen :=
  { seen with
    dataColumnSidecarTuples := dataColumnSidecarKey before sidecar :: seen.dataColumnSidecarTuples }

end EthLib.Consensus
