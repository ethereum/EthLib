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

From Gloas a column sidecar names its block by its root, and has no header.

Its commitments are those of the bid of that block, which must be known and valid.

A proof that the KZG checks cannot read is an error, since the rule raises there.

At Fulu a partial column sidecar carries some cells of a column, its header, or both.

Its header passes the same checks once, and the node records it for its block.

Later cells of that block are checked against the recorded header.

From Gloas a partial sidecar has no header, and its group names the slot of its block.

Its cells are checked against the commitments of the bid of that block, which must be valid.
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
  -- Let `s` be the slot of the header, and `t` the time in milliseconds.
  let header := signed.message
  -- Ignore it when `t + MAXIMUM_GOSSIP_CLOCK_DISPARITY` is before the start of `s`.
  let future ← store.isFutureSlot config header.slot currentTimeMs
  (ignoreUnless (!future) s!"{noun} is from a future slot").andThenM fun _ => do
  -- Ignore it unless `f * SLOTS_PER_EPOCH < s`, for the finalized epoch `f`.
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot < header.slot)
    s!"{noun} is not from a slot greater than the latest finalized slot").andThenM fun _ => do
  -- Ignore it unless the parent block is known.
  match store.blocks[header.parentRoot]? with
  | none => return .ignore s!"{noun}'s parent has not been seen"
  | some parent => do
  -- Reject it unless the parent passed validation: the store holds the state of the parent.
  match store.blockStates[header.parentRoot]? with
  | none => return .reject s!"{noun}'s parent failed validation"
  | some parentState => do
  -- The signature checks read the state of the head.
  let state ← store.headState config
  -- Reject it unless the proposer index names a validator of that state.
  match state.validators.data[header.proposerIndex.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer => do
  -- Reject it unless the proposer signed the header, under the proposer domain at the epoch of `s`.
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER header.slot header
    proposer.pubkey signed.signature
  (rejectUnless valid s!"invalid proposer signature on {signedNoun}").andThenM fun _ =>
  -- Reject it unless `s` is above the slot of the parent.
  (rejectUnless (parent.slot < header.slot)
    s!"{noun} is not from a higher slot than its parent").andThenM fun _ => do
  -- Reject it unless the finalized checkpoint is an ancestor of the block.
  --
  -- The ancestor of the parent at the first slot of the finalized epoch is the finalized root.
  let finalizedBlock ← store.getCheckpointBlock header.parentRoot store.finalizedCheckpoint.epoch
  (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
    s!"finalized checkpoint is not an ancestor of {noun}'s block").andThenM fun _ => do
  -- The proofs of the data, which reject the message when they fail.
  (← proofs ()).andThenM fun _ => do
  -- Reject it unless the proposer index is that of the proposer of `s`.
  --
  -- That proposer comes from the parent state, advanced to `s`.
  let expected ← expectedProposer config checks parentState header.slot
  return rejectUnless (header.proposerIndex == expected)
    s!"{noun} proposer_index does not match expected proposer"

/-- The key of a blob sidecar among the keys seen: its slot, its proposer and its index. -/
def blobSidecarKey (sidecar : BlobSidecar preset) : Slot × ValidatorIndex × BlobIndex :=
  (sidecar.signedBlockHeader.message.slot, sidecar.signedBlockHeader.message.proposerIndex,
    sidecar.index)

/-- The checks of the proofs of a blob sidecar. -/
def blobSidecarProofs (setup : TrustedSetup) (fork : Fork) (sidecar : BlobSidecar preset) :
    Except ForkChoiceError ValidationResult :=
  -- Reject it unless its branch climbs from its commitment to the body root of its header.
  (rejectUnless (verifyBlobSidecarInclusionProof preset fork sidecar)
    "invalid blob sidecar inclusion proof").andThenM fun _ => do
  -- Reject it unless its KZG proof shows that its blob matches its commitment.
  --
  -- An input that the KZG check cannot read is an error.
  let valid ← (verifyBlobKzgProof setup sidecar.blob sidecar.kzgCommitment.bytes
    sidecar.kzgProof.bytes).mapError .kzg
  return rejectUnless valid "invalid blob kzg proof"

/-- At Deneb and Electra: the checks of a blob sidecar on a subnet, at a time in milliseconds. -/
def validateBlobSidecar (config : Config) (checks : SignatureChecks) (setup : TrustedSetup)
    (seen : Seen) (store : Store preset fork) (_blobs : .dencun ≤ fork ∧ fork < .fusaka)
    (sidecar : BlobSidecar preset) (currentTimeMs subnetId : UInt64) :
    Except ForkChoiceError ValidationResult :=
  -- Ignore it unless it is the first valid sidecar of its slot, its proposer and its index `i`.
  (ignoreUnless (!seen.blobSidecarTuples.contains (blobSidecarKey sidecar))
    "already seen blob sidecar from this proposer for this slot and index").andThenM fun _ =>
  -- Reject it unless `i < MAX_BLOBS_PER_BLOCK`, or `i < MAX_BLOBS_PER_BLOCK_ELECTRA` from Electra.
  (rejectUnless (sidecar.index < blobSidecarLimit config fork)
    "blob index out of range").andThenM fun _ => do
  -- Reject it unless it is on subnet `i mod n`, for the number `n` of blob sidecar subnets.
  let subnet ← (computeSubnetForBlobSidecar config fork sidecar.index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "blob sidecar is for wrong subnet").andThenM fun _ =>
  -- The checks of its signed header, with its proofs before the expected proposer.
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

/-- Before Gloas: the checks of the proofs of a column sidecar. -/
def dataColumnSidecarProofs (setup : TrustedSetup) (before : fork < .glamsterdam)
    (sidecar : DataColumnSidecar preset fork) : Except ForkChoiceError ValidationResult :=
  -- Reject it unless its branch climbs from the root of its commitments to its body root.
  (rejectUnless (verifyDataColumnSidecarInclusionProof preset before sidecar)
    "invalid sidecar inclusion proof").andThenM fun _ => do
  -- Reject it unless its KZG proofs show that each cell matches the commitment of its blob.
  --
  -- Each cell sits at the index of the column in its extended blob.
  let valid ← (verifyDataColumnSidecarKzgProofs setup sidecar (noBidBeforeGloas before)).mapError
    .kzg
  return rejectUnless valid "invalid sidecar kzg proofs"

/-- From Fulu, before Gloas: the checks of a column sidecar on a subnet, at a time in milliseconds.
-/
def validateDataColumnSidecar (config : Config) (checks : SignatureChecks) (setup : TrustedSetup)
    (seen : Seen) (store : Store preset fork) (columns : .fusaka ≤ fork ∧ fork < .glamsterdam)
    (sidecar : DataColumnSidecar preset fork) (currentTimeMs subnetId : UInt64) :
    Except ForkChoiceError ValidationResult :=
  -- Ignore it unless it is the first valid sidecar of its slot, its proposer and its column `j`.
  (ignoreUnless (!seen.dataColumnSidecarTuples.contains (dataColumnSidecarKey columns.2 sidecar))
    "already seen sidecar from this proposer for this slot and index").andThenM fun _ =>
  -- Reject it unless `j < NUMBER_OF_COLUMNS`, and it carries at least one commitment.
  --
  -- Let `b` be the blob limit of the epoch of its slot.
  --
  -- Reject it unless it carries at most `b` commitments.
  --
  -- That limit is the most blobs per block that the blob schedule gives at that epoch.
  --
  -- Reject it unless it carries one cell and one proof per commitment.
  (rejectUnless (verifyDataColumnSidecar preset config sidecar (noBidBeforeGloas columns.2))
    "invalid sidecar").andThenM fun _ => do
  -- Reject it unless it is on subnet `j mod DATA_COLUMN_SIDECAR_SUBNET_COUNT`.
  let subnet ← (computeSubnetForDataColumnSidecar config sidecar.index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "sidecar is for wrong subnet").andThenM fun _ =>
  -- The checks of its signed header, with its proofs before the expected proposer.
  validateSidecarHeader config checks store "sidecar" "sidecar block header"
    (sidecar.signedBlockHeader columns.2) currentTimeMs fun _ =>
  dataColumnSidecarProofs setup columns.2 sidecar

/-- From Fulu, before Gloas: the keys after a valid column sidecar. -/
def Seen.recordDataColumnSidecar (seen : Seen) (before : fork < .glamsterdam)
    (sidecar : DataColumnSidecar preset fork) : Seen :=
  { seen with
    dataColumnSidecarTuples := dataColumnSidecarKey before sidecar :: seen.dataColumnSidecarTuples }

/-- From Gloas: the checks of a column sidecar on a subnet, at a time in milliseconds.

The sidecar is checked against the commitments of the bid of its block, as [EIP-7732] specifies.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#p2p-changes
-/
def validateGloasDataColumnSidecar (config : Config) (setup : TrustedSetup) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (sidecar : DataColumnSidecar preset fork) (currentTimeMs subnetId : UInt64) :
    Except ForkChoiceError ValidationResult :=
  -- Let `r` be the block root that the sidecar names, and `j` its column.
  let root := sidecar.beaconBlockRoot gloas
  -- Ignore it unless it is the first valid sidecar of `r` and `j`.
  (ignoreUnless (!seen.dataColumnSidecarRoots.contains (root, sidecar.index))
    "already seen sidecar for this block root and index").andThenM fun _ => do
  -- Reject it unless it is on subnet `j mod DATA_COLUMN_SIDECAR_SUBNET_COUNT`.
  let subnet ← (computeSubnetForDataColumnSidecar config sidecar.index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "sidecar is for wrong subnet").andThenM fun _ => do
  -- Let `s` be the slot of the sidecar, and `t` the time in milliseconds.
  --
  -- Ignore it when `t + MAXIMUM_GOSSIP_CLOCK_DISPARITY` is before the start of `s`.
  let future ← store.isFutureSlot config (sidecar.slot gloas) currentTimeMs
  (ignoreUnless (!future) "sidecar is from a future slot").andThenM fun _ =>
  -- Ignore it unless the block `r` is known.
  match store.blocks[root]? with
  | none => return .ignore "block for sidecar's beacon block root has not been seen"
  | some block =>
  -- Reject it unless that block passed validation: the store holds its state.
  match store.blockStates[root]? with
  | none => return .reject "block for sidecar's beacon block root failed validation"
  | some _ =>
  -- Reject it unless `s` is the slot of the block.
  (rejectUnless (sidecar.slot gloas == block.slot)
    "sidecar's slot does not match block's slot").andThenM fun _ =>
  -- Let `C` be the commitments of the bid of the block.
  --
  -- Reject it unless `j < NUMBER_OF_COLUMNS`, with one cell and one proof per element of `C`.
  --
  -- Reject it unless `C` is nonempty.
  (rejectUnless (verifyDataColumnSidecar preset config sidecar block.bidCommitments)
    "invalid sidecar").andThenM fun _ => do
  -- Reject it unless its KZG proofs show that each cell matches its element of `C`.
  let valid ← (verifyDataColumnSidecarKzgProofs setup sidecar block.bidCommitments).mapError .kzg
  return rejectUnless valid "invalid sidecar kzg proofs"

/-- From Gloas: the keys after a valid column sidecar, its block root and its column. -/
def Seen.recordGloasDataColumnSidecar (seen : Seen) (gloas : .glamsterdam ≤ fork)
    (sidecar : DataColumnSidecar preset fork) : Seen :=
  { seen with
    dataColumnSidecarRoots :=
      (sidecar.beaconBlockRoot gloas, sidecar.index) :: seen.dataColumnSidecarRoots }

/-- At Fulu: the partial headers that passed their checks, each with the root of its block.

The header type depends on the preset and the fork, so these keys stay apart from the others. -/
abbrev PartialHeaders (preset : Preset) (fork : Fork) :=
  List (Root × PartialDataColumnHeader preset fork)

/-- The header recorded for the block with a root, if any. -/
def PartialHeaders.find? (headers : PartialHeaders preset fork) (root : Root) :
    Option (PartialDataColumnHeader preset fork) :=
  (List.find? (·.1 == root) headers).map (·.2)

/-- The headers after a valid header of the block with a root: it replaces any earlier one. -/
def PartialHeaders.record (headers : PartialHeaders preset fork) (root : Root)
    (header : PartialDataColumnHeader preset fork) : PartialHeaders preset fork :=
  (root, header) :: headers.filter (·.1 != root)

/-- The checks of the header of a partial sidecar, for the block with a root. -/
def partialHeaderOutcome (config : Config) (checks : SignatureChecks)
    (headers : PartialHeaders preset fork) (store : Store preset fork) (root : Root)
    (header : PartialDataColumnHeader preset fork) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  -- Let `r` be the root of the block.
  --
  -- Reject it unless it equals the header recorded for `r`, if there is one.
  (rejectUnless ((headers.find? root).all (· == header))
    "header differs from previously validated header").andThenM fun _ => do
  -- Reject it unless the hash tree root of its block header is `r`.
  let blockRoot ←
    (Serialization.Ssz.SszType.hashTreeRoot header.signedBlockHeader.message).mapError .ssz
  (rejectUnless (blockRoot == root)
    "header's block root does not match group id's block root").andThenM fun _ =>
  -- Reject it unless it carries at least one commitment.
  (rejectUnless (header.kzgCommitments.data.size != 0)
    "header's kzg_commitments is empty").andThenM fun _ =>
  -- Let `b` be the blob limit of the epoch of its slot.
  --
  -- Reject it unless it carries at most `b` commitments.
  --
  -- That limit is the most blobs per block that the blob schedule gives at that epoch.
  (rejectUnless (header.kzgCommitments.data.size ≤ (config.getBlobParameters
      (computeEpochAtSlot preset header.signedBlockHeader.message.slot)).maxBlobsPerBlock.toNat)
    "header's kzg_commitments is too long").andThenM fun _ =>
  -- The checks of its signed header, with its branch before the expected proposer.
  validateSidecarHeader config checks store "header" "header" header.signedBlockHeader
    currentTimeMs fun _ =>
  -- Reject it unless its branch climbs from the root of its commitments to its body root.
  pure (rejectUnless (verifyPartialDataColumnHeaderInclusionProof preset header)
    "invalid header inclusion proof")

/-- The checks of the cells of a partial sidecar, against the header recorded for their block. -/
def partialCellsOutcome (config : Config) (setup : TrustedSetup)
    (headers : PartialHeaders preset fork) (store : Store preset fork) (root : Root)
    (sidecar : PartialDataColumnSidecar preset fork) (currentTimeMs : UInt64)
    (columnIndex : DataAvailability.ColumnIndex) : Except ForkChoiceError ValidationResult :=
  -- Ignore it unless a valid header is recorded for the root of the block.
  match headers.find? root with
  | none => return .ignore "valid corresponding header has not been seen"
  | some header => do
  -- Let `s` be the slot of that header, and `t` the time in milliseconds.
  let slot := header.signedBlockHeader.message.slot
  -- Ignore it when `t + MAXIMUM_GOSSIP_CLOCK_DISPARITY` is before the start of `s`.
  let future ← store.isFutureSlot config slot currentTimeMs
  (ignoreUnless (!future) "corresponding header is from a future slot").andThenM fun _ => do
  -- Ignore it unless `f * SLOTS_PER_EPOCH < s`, for the finalized epoch `f`.
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  (ignoreUnless (finalizedSlot < slot)
    "corresponding header is not from a slot greater than the latest finalized slot").andThenM
    fun _ =>
  -- Reject it unless its bitmap has one bit per commitment of the header.
  (rejectUnless (sidecar.cellsPresentBitmap.bits.size == header.kzgCommitments.data.size)
    "bitmap length does not match commitments length").andThenM fun _ => do
  -- Reject it unless its KZG proofs show that each cell matches the commitment of its set bit.
  --
  -- Each cell sits at the index of the column in its extended blob.
  let valid ← (verifyPartialDataColumnSidecarKzgProofs setup sidecar header.kzgCommitments
    columnIndex).mapError .kzg
  return rejectUnless valid "invalid sidecar kzg proofs"

/-- The checks of the counts of a partial sidecar, which read nothing else. -/
def partialCountsOutcome (sidecar : PartialDataColumnSidecar preset fork) : ValidationResult :=
  -- Let `n` be the number of set bits of the bitmap.
  let count := sidecar.cellsPresentBitmap.bits.count true
  -- Reject it unless it carries a header, or `0 < n`.
  --
  -- From Gloas a partial sidecar has no header, so this asks for `0 < n`.
  (rejectUnless (sidecar.headers.size == 1 || count != 0)
    "partial message is semantically empty").andThen fun _ =>
  -- Reject it unless it carries `n` cells.
  (rejectUnless (sidecar.partialColumn.data.size == count)
    "number of cells does not match number of set bits").andThen fun _ =>
  -- Reject it unless it carries `n` proofs.
  rejectUnless (sidecar.kzgProofs.data.size == count)
    "number of proofs does not match number of set bits"

/-- At Fulu: the checks of a partial sidecar of a group and a column, at a time in milliseconds.

The outcome comes with the headers after the message.

A valid header is recorded before its cells are checked, so it stays recorded when they fail. -/
def validatePartialDataColumnSidecar (config : Config) (checks : SignatureChecks)
    (setup : TrustedSetup) (headers : PartialHeaders preset fork) (store : Store preset fork)
    (_fulu : .fusaka ≤ fork ∧ fork < .glamsterdam) (sidecar : PartialDataColumnSidecar preset fork)
    (currentTimeMs : UInt64) (group : PartialDataColumnGroupID fork)
    (columnIndex : DataAvailability.ColumnIndex) :
    Except ForkChoiceError (ValidationResult × PartialHeaders preset fork) := do
  -- Let `r` be the block root of the group.
  let root := group.beaconBlockRoot
  -- The counts come first.
  match partialCountsOutcome sidecar with
  | .accept =>
    -- A header, if any, passes its checks for `r`, and a valid one is recorded for `r`.
    let (outcome, headers) ← match sidecar.headers[0]? with
      | none => pure (ValidationResult.accept, headers)
      | some header => do
        match ← partialHeaderOutcome config checks headers store root header currentTimeMs with
        | .accept => pure (.accept, headers.record root header)
        | other => pure (other, headers)
    match outcome with
    | .accept =>
      -- A message with no cell passes.
      if sidecar.cellsPresentBitmap.bits.count true = 0 then return (.accept, headers)
      -- Its cells pass their checks against the header recorded for `r`.
      return (← partialCellsOutcome config setup headers store root sidecar currentTimeMs
        columnIndex, headers)
    | other => return (other, headers)
  | other => return (other, headers)

/-- From Gloas: the checks of a partial sidecar of a group and a column.

The rule reads no clock and records nothing. -/
def validateGloasPartialDataColumnSidecar (setup : TrustedSetup) (store : Store preset fork)
    (gloas : .glamsterdam ≤ fork) (sidecar : PartialDataColumnSidecar preset fork)
    (group : PartialDataColumnGroupID fork) (columnIndex : DataAvailability.ColumnIndex) :
    Except ForkChoiceError ValidationResult :=
  -- Let `r` be the block root of the group.
  let root := group.beaconBlockRoot
  -- The counts come first: at least one cell, and one cell and one proof per set bit.
  (partialCountsOutcome sidecar).andThenM fun _ =>
  -- Ignore it unless the block `r` is known.
  match store.blocks[root]? with
  | none => return .ignore "group id's block has not been seen"
  | some block =>
  -- Reject it unless that block passed validation: the store holds its state.
  match store.blockStates[root]? with
  | none => return .reject "group id's block failed validation"
  | some _ =>
  -- Reject it unless the slot of the group is the slot of the block.
  (rejectUnless (group.slot gloas == block.slot)
    "group id's slot does not match the block's slot").andThenM fun _ =>
  -- Let `C` be the commitments of the bid of the block.
  let commitments := block.bidCommitments gloas
  -- Reject it unless its bitmap has one bit per element of `C`.
  (rejectUnless (sidecar.cellsPresentBitmap.bits.size == commitments.data.size)
    "bitmap length does not match commitments length").andThenM fun _ => do
  -- Reject it unless its KZG proofs show that each cell matches the element of `C` of its set bit.
  let valid ←
    (verifyPartialDataColumnSidecarKzgProofs setup sidecar commitments columnIndex).mapError .kzg
  return rejectUnless valid "invalid sidecar kzg proofs"

end EthLib.Consensus
