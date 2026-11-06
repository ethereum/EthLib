module

public import EthLib.Consensus.Gossip.Sidecar
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the outcomes of the sidecar topics

A blob sidecar and a column sidecar share the checks of their signed header.

Once their fallible steps are computed, the header checks are a chain.

The finalized ancestor, the proofs of the data and the expected proposer complete that chain.

Before the header, each topic checks the seen keys, the shape or index, and the subnet.

From the chain follows which sidecars each topic accepts, ignores and rejects.

A valid sidecar records its key, and the same sidecar is then ignored.

A sidecar with another index keeps the outcome of the seen check.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Kzg Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {setup : TrustedSetup} {seen : Seen} {store : Store preset fork}
  {currentTimeMs subnetId : UInt64}

/-! ## Limits and keys -/

/-- A check that branches on a condition continues each branch with the same next checks. -/
theorem ite_andThen {condition : Prop} [Decidable condition] {first second : ValidationResult}
    {next : Unit → ValidationResult} :
    (if condition then first else second).andThen next =
      if condition then first.andThen next else second.andThen next := by
  split <;> rfl

/-- At Deneb the mainnet limit is 6 blobs per block. -/
theorem blobSidecarLimit_mainnet_deneb : blobSidecarLimit Config.mainnet .dencun = 6 := by
  decide

/-- At Electra the mainnet limit is 9 blobs per block, so index 6 passes there only. -/
theorem blobSidecarLimit_mainnet_electra : blobSidecarLimit Config.mainnet .pectra = 9 := by
  decide

/-- Recording a blob sidecar leaves unseen a sidecar with another index. -/
theorem Seen.recordBlobSidecar_contains_of_index_ne {first second : BlobSidecar preset}
    (other : first.index ≠ second.index) :
    (seen.recordBlobSidecar first).blobSidecarTuples.contains (blobSidecarKey second) =
      seen.blobSidecarTuples.contains (blobSidecarKey second) := by
  simp [Seen.recordBlobSidecar, blobSidecarKey, Ne.symm other]

/-- Recording a column sidecar leaves unseen a sidecar with another index. -/
theorem Seen.recordDataColumnSidecar_contains_of_index_ne {before : fork < .glamsterdam}
    {first second : DataColumnSidecar preset fork} (other : first.index ≠ second.index) :
    (seen.recordDataColumnSidecar before first).dataColumnSidecarTuples.contains
        (dataColumnSidecarKey before second) =
      seen.dataColumnSidecarTuples.contains (dataColumnSidecarKey before second) := by
  simp [Seen.recordDataColumnSidecar, dataColumnSidecarKey, Ne.symm other]

/-! ## The signed header -/

section Header

variable {noun signedNoun : String} {signed : SignedBeaconBlockHeader}
  {proofs : Unit → Except ForkChoiceError ValidationResult} {future : Bool}
  {finalizedSlot : Slot} {parent : BeaconBlock preset fork}
  {parentState state : BeaconState preset fork} {proposer : Validator} {valid : Bool}
  {finalizedBlock : Root} {checked : ValidationResult} {expected : ValidatorIndex}

/-- A header whose parent the node has not seen is ignored, after the clock checks. -/
theorem validateSidecarHeader_of_unknown_parent
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (unknown : store.blocks[signed.message.parentRoot]? = none) :
    validateSidecarHeader config checks store noun signedNoun signed currentTimeMs proofs =
      .ok ((ignoreUnless (!future) s!"{noun} is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < signed.message.slot))
          s!"{noun} is not from a slot greater than the latest finalized slot").andThen fun _ =>
        .ignore s!"{noun}'s parent has not been seen") := by
  unfold validateSidecarHeader
  simp only [clock, start, unknown, bind, Except.bind, pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- A header whose parent the node saw without a state is rejected, after the clock checks. -/
theorem validateSidecarHeader_of_parent_failed
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (failed : store.blockStates[signed.message.parentRoot]? = none) :
    validateSidecarHeader config checks store noun signedNoun signed currentTimeMs proofs =
      .ok ((ignoreUnless (!future) s!"{noun} is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < signed.message.slot))
          s!"{noun} is not from a slot greater than the latest finalized slot").andThen fun _ =>
        .reject s!"{noun}'s parent failed validation") := by
  unfold validateSidecarHeader
  simp only [clock, start, known, failed, bind, Except.bind, pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- A header whose proposer index names no validator of the head state is rejected.

That check comes after the clock checks and the checks of the parent. -/
theorem validateSidecarHeader_of_proposer_out_of_range
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (outOfRange : state.validators.data[signed.message.proposerIndex.toNat]? = none) :
    validateSidecarHeader config checks store noun signedNoun signed currentTimeMs proofs =
      .ok ((ignoreUnless (!future) s!"{noun} is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < signed.message.slot))
          s!"{noun} is not from a slot greater than the latest finalized slot").andThen fun _ =>
        .reject "proposer index out of range") := by
  unfold validateSidecarHeader
  simp only [clock, start, known, parentKnown, head, outOfRange, bind, Except.bind, pure,
    Except.pure, Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- The outcome of a header is its chain of checks, in order.

This holds once the parent and its state are known and the fallible steps are computed. -/
theorem validateSidecarHeader_eq
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (data : proofs () = .ok checked)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    validateSidecarHeader config checks store noun signedNoun signed currentTimeMs proofs =
      .ok ((ignoreUnless (!future) s!"{noun} is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < signed.message.slot))
          s!"{noun} is not from a slot greater than the latest finalized slot").andThen fun _ =>
        (rejectUnless valid s!"invalid proposer signature on {signedNoun}").andThen fun _ =>
        (rejectUnless (decide (parent.slot < signed.message.slot))
          s!"{noun} is not from a higher slot than its parent").andThen fun _ =>
        (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
          s!"finalized checkpoint is not an ancestor of {noun}'s block").andThen fun _ =>
        checked.andThen fun _ =>
        rejectUnless (signed.message.proposerIndex == expected)
          s!"{noun} proposer_index does not match expected proposer") := by
  unfold validateSidecarHeader
  simp only [clock, start, known, parentKnown, head, found, signature, checkpoint, data,
    proposerOf, bind, Except.bind, pure, Except.pure, Except.mapError, ignoreUnless_andThenM,
    ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]
  cases checked <;> simp only [ValidationResult.andThenM, ValidationResult.andThen, pure,
    Except.pure]

end Header

/-! ## Blob sidecars, at Deneb and Electra -/

section Blob

variable {blobs : .dencun ≤ fork ∧ fork < .fusaka} {sidecar : BlobSidecar preset}

/-- A blob sidecar whose key a valid sidecar had already is ignored. -/
theorem validateBlobSidecar_of_seen (known : blobSidecarKey sidecar ∈ seen.blobSidecarTuples) :
    validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs subnetId =
      .ok (.ignore "already seen blob sidecar from this proposer for this slot and index") := by
  simp [validateBlobSidecar, known, pure, Except.pure]

/-- A valid blob sidecar records its key, so the same sidecar is then ignored. -/
theorem validateBlobSidecar_recordBlobSidecar :
    validateBlobSidecar config checks setup (seen.recordBlobSidecar sidecar) store blobs sidecar
        currentTimeMs subnetId =
      .ok (.ignore "already seen blob sidecar from this proposer for this slot and index") :=
  validateBlobSidecar_of_seen (by simp [Seen.recordBlobSidecar])

/-- An unseen blob sidecar whose index reaches the limit of the fork is rejected. -/
theorem validateBlobSidecar_of_limit_le (unseen : blobSidecarKey sidecar ∉ seen.blobSidecarTuples)
    (outOfRange : blobSidecarLimit config fork ≤ sidecar.index) :
    validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs subnetId =
      .ok (.reject "blob index out of range") := by
  have : ¬ sidecar.index < blobSidecarLimit config fork := UInt64.not_lt.mpr outOfRange
  simp [validateBlobSidecar, unseen, this, pure, Except.pure]

variable {subnet : SubnetID} {future : Bool} {finalizedSlot : Slot}
  {parent : BeaconBlock preset fork} {parentState state : BeaconState preset fork}
  {proposer : Validator} {valid kzgValid : Bool} {finalizedBlock : Root}
  {expected : ValidatorIndex}

/-- Once its KZG check is computed, the proofs of a blob sidecar are a chain of two checks. -/
theorem blobSidecarProofs_eq
    (kzg : verifyBlobKzgProof setup sidecar.blob sidecar.kzgCommitment sidecar.kzgProof =
      .ok kzgValid) :
    blobSidecarProofs setup fork sidecar =
      .ok ((rejectUnless (verifyBlobSidecarInclusionProof preset fork sidecar)
        "invalid blob sidecar inclusion proof").andThen fun _ =>
        rejectUnless kzgValid "invalid blob kzg proof") := by
  simp only [blobSidecarProofs, kzg, bind, Except.bind, pure, Except.pure, Except.mapError,
    rejectUnless_andThenM, rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- The outcome of a blob sidecar is its chain of checks, in order.

This holds once the parent and its state are known and the fallible steps are computed. -/
theorem validateBlobSidecar_eq
    (subnetOf : computeSubnetForBlobSidecar config fork sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config sidecar.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[sidecar.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[sidecar.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[sidecar.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      sidecar.signedBlockHeader.message.slot sidecar.signedBlockHeader.message proposer.pubkey
      sidecar.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock sidecar.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyBlobKzgProof setup sidecar.blob sidecar.kzgCommitment sidecar.kzgProof =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState
      sidecar.signedBlockHeader.message.slot = .ok expected) :
    validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs subnetId =
      .ok ((ignoreUnless (!seen.blobSidecarTuples.contains (blobSidecarKey sidecar))
          "already seen blob sidecar from this proposer for this slot and index").andThen fun _ =>
        (rejectUnless (decide (sidecar.index < blobSidecarLimit config fork))
          "blob index out of range").andThen fun _ =>
        (rejectUnless (subnet == subnetId) "blob sidecar is for wrong subnet").andThen fun _ =>
        (ignoreUnless (!future) "blob sidecar is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < sidecar.signedBlockHeader.message.slot))
          "blob sidecar is not from a slot greater than the latest finalized slot").andThen fun _ =>
        (rejectUnless valid "invalid proposer signature on blob sidecar block header").andThen
          fun _ =>
        (rejectUnless (decide (parent.slot < sidecar.signedBlockHeader.message.slot))
          "blob sidecar is not from a higher slot than its parent").andThen fun _ =>
        (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
          "finalized checkpoint is not an ancestor of blob sidecar's block").andThen fun _ =>
        (rejectUnless (verifyBlobSidecarInclusionProof preset fork sidecar)
          "invalid blob sidecar inclusion proof").andThen fun _ =>
        (rejectUnless kzgValid "invalid blob kzg proof").andThen fun _ =>
        rejectUnless (sidecar.signedBlockHeader.message.proposerIndex == expected)
          "blob sidecar proposer_index does not match expected proposer") := by
  unfold validateBlobSidecar
  simp only [subnetOf, bind, Except.bind, pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    validateSidecarHeader_eq (proofs := fun _ => blobSidecarProofs setup fork sidecar) clock start
      known parentKnown head found signature checkpoint (blobSidecarProofs_eq kzg) proposerOf,
    apply_ite (Except.ok (ε := ForkChoiceError))]
  simp only [toString, String.reduceAppend, ite_andThen, rejectUnless_andThen]
  simp only [ValidationResult.andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a blob sidecar is valid exactly when every check passes. -/
theorem validateBlobSidecar_eq_accept
    (subnetOf : computeSubnetForBlobSidecar config fork sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config sidecar.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[sidecar.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[sidecar.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[sidecar.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      sidecar.signedBlockHeader.message.slot sidecar.signedBlockHeader.message proposer.pubkey
      sidecar.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock sidecar.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyBlobKzgProof setup sidecar.blob sidecar.kzgCommitment sidecar.kzgProof =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState
      sidecar.signedBlockHeader.message.slot = .ok expected) :
    validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs subnetId =
        .ok accept ↔
      blobSidecarKey sidecar ∉ seen.blobSidecarTuples ∧
        sidecar.index < blobSidecarLimit config fork ∧ subnet = subnetId ∧ future = false ∧
        finalizedSlot < sidecar.signedBlockHeader.message.slot ∧ valid = true ∧
        parent.slot < sidecar.signedBlockHeader.message.slot ∧
        finalizedBlock = store.finalizedCheckpoint.root ∧
        verifyBlobSidecarInclusionProof preset fork sidecar = true ∧ kzgValid = true ∧
        sidecar.signedBlockHeader.message.proposerIndex = expected := by
  rw [validateBlobSidecar_eq subnetOf clock start known parentKnown head found signature
    checkpoint kzg proposerOf]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  grind

/-- Once its inputs are computed, a blob sidecar is ignored in three cases.

Its key was seen, or its index and subnet pass and it is early or not after the finalized slot. -/
theorem validateBlobSidecar_ignored
    (subnetOf : computeSubnetForBlobSidecar config fork sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config sidecar.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[sidecar.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[sidecar.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[sidecar.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      sidecar.signedBlockHeader.message.slot sidecar.signedBlockHeader.message proposer.pubkey
      sidecar.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock sidecar.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyBlobKzgProof setup sidecar.blob sidecar.kzgCommitment sidecar.kzgProof =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState
      sidecar.signedBlockHeader.message.slot = .ok expected) :
    (∃ reason, validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs
        subnetId = .ok (.ignore reason)) ↔
      blobSidecarKey sidecar ∈ seen.blobSidecarTuples ∨
        (sidecar.index < blobSidecarLimit config fork ∧ subnet = subnetId ∧
          (future = true ∨ sidecar.signedBlockHeader.message.slot ≤ finalizedSlot)) := by
  rw [validateBlobSidecar_eq subnetOf clock start known parentKnown head found signature
    checkpoint kzg proposerOf]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept]
  simp [UInt64.not_lt]
  grind

/-- Once its inputs are computed, a blob sidecar is rejected exactly when a check rejects it.

Its key is unseen, and its index or subnet fails, or a check after the clock checks fails. -/
theorem validateBlobSidecar_rejected
    (subnetOf : computeSubnetForBlobSidecar config fork sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config sidecar.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[sidecar.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[sidecar.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[sidecar.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      sidecar.signedBlockHeader.message.slot sidecar.signedBlockHeader.message proposer.pubkey
      sidecar.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock sidecar.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyBlobKzgProof setup sidecar.blob sidecar.kzgCommitment sidecar.kzgProof =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState
      sidecar.signedBlockHeader.message.slot = .ok expected) :
    (∃ reason, validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs
        subnetId = .ok (.reject reason)) ↔
      blobSidecarKey sidecar ∉ seen.blobSidecarTuples ∧
        (blobSidecarLimit config fork ≤ sidecar.index ∨ subnet ≠ subnetId ∨
          (future = false ∧ finalizedSlot < sidecar.signedBlockHeader.message.slot ∧
            (valid = false ∨ sidecar.signedBlockHeader.message.slot ≤ parent.slot ∨
              finalizedBlock ≠ store.finalizedCheckpoint.root ∨
              verifyBlobSidecarInclusionProof preset fork sidecar = false ∨ kzgValid = false ∨
              sidecar.signedBlockHeader.message.proposerIndex ≠ expected))) := by
  have accepted := validateBlobSidecar_eq_accept (seen := seen) (blobs := blobs)
    (subnetId := subnetId) subnetOf clock start known parentKnown head found signature checkpoint
    kzg proposerOf
  have ignored := validateBlobSidecar_ignored (seen := seen) (blobs := blobs)
    (subnetId := subnetId) subnetOf clock start known parentKnown head found signature checkpoint
    kzg proposerOf
  rw [validateBlobSidecar_eq subnetOf clock start known parentKnown head found signature
    checkpoint kzg proposerOf] at accepted ignored ⊢
  generalize ValidationResult.andThen _ _ = outcome at accepted ignored ⊢
  cases outcome <;> simp [UInt64.not_le] at accepted ignored ⊢ <;> grind

end Blob

/-! ## Column sidecars, from Fulu before Gloas -/

section Column

variable {columns : .fusaka ≤ fork ∧ fork < .glamsterdam}
  {sidecar : DataColumnSidecar preset fork}

/-- A column sidecar whose key a valid sidecar had already is ignored. -/
theorem validateDataColumnSidecar_of_seen
    (known : dataColumnSidecarKey columns.2 sidecar ∈ seen.dataColumnSidecarTuples) :
    validateDataColumnSidecar config checks setup seen store columns sidecar currentTimeMs
        subnetId =
      .ok (.ignore "already seen sidecar from this proposer for this slot and index") := by
  simp [validateDataColumnSidecar, known, pure, Except.pure]

/-- A valid column sidecar records its key, so the same sidecar is then ignored. -/
theorem validateDataColumnSidecar_recordDataColumnSidecar :
    validateDataColumnSidecar config checks setup (seen.recordDataColumnSidecar columns.2 sidecar)
        store columns sidecar currentTimeMs subnetId =
      .ok (.ignore "already seen sidecar from this proposer for this slot and index") :=
  validateDataColumnSidecar_of_seen (by simp [Seen.recordDataColumnSidecar])

/-- An unseen column sidecar with an invalid shape is rejected. -/
theorem validateDataColumnSidecar_of_invalid
    (unseen : dataColumnSidecarKey columns.2 sidecar ∉ seen.dataColumnSidecarTuples)
    (invalid : verifyDataColumnSidecar preset config sidecar (noBidBeforeGloas columns.2) = false) :
    validateDataColumnSidecar config checks setup seen store columns sidecar currentTimeMs
        subnetId =
      .ok (.reject "invalid sidecar") := by
  simp [validateDataColumnSidecar, unseen, invalid, pure, Except.pure]

variable {signed : SignedBeaconBlockHeader} {subnet : SubnetID} {future : Bool}
  {finalizedSlot : Slot} {parent : BeaconBlock preset fork}
  {parentState state : BeaconState preset fork}
  {proposer : Validator} {valid kzgValid : Bool} {finalizedBlock : Root}
  {expected : ValidatorIndex}

/-- Once its KZG check is computed, the proofs of a column sidecar are a chain of two checks. -/
theorem dataColumnSidecarProofs_eq {before : fork < .glamsterdam}
    (kzg : verifyDataColumnSidecarKzgProofs setup sidecar (noBidBeforeGloas before) =
      .ok kzgValid) :
    dataColumnSidecarProofs setup before sidecar =
      .ok ((rejectUnless (verifyDataColumnSidecarInclusionProof preset before sidecar)
        "invalid sidecar inclusion proof").andThen fun _ =>
        rejectUnless kzgValid "invalid sidecar kzg proofs") := by
  simp only [dataColumnSidecarProofs, kzg, bind, Except.bind, pure, Except.pure, Except.mapError,
    rejectUnless_andThenM, rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- The outcome of a column sidecar is its chain of checks, in order.

This holds once the parent and its state are known and the fallible steps are computed. -/
theorem validateDataColumnSidecar_eq
    (header : sidecar.signedBlockHeader columns.2 = signed)
    (subnetOf : computeSubnetForDataColumnSidecar config sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyDataColumnSidecarKzgProofs setup sidecar (noBidBeforeGloas columns.2) =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    validateDataColumnSidecar config checks setup seen store columns sidecar currentTimeMs
        subnetId =
      .ok ((ignoreUnless
          (!seen.dataColumnSidecarTuples.contains (dataColumnSidecarKey columns.2 sidecar))
          "already seen sidecar from this proposer for this slot and index").andThen fun _ =>
        (rejectUnless (verifyDataColumnSidecar preset config sidecar (noBidBeforeGloas columns.2))
          "invalid sidecar").andThen fun _ =>
        (rejectUnless (subnet == subnetId) "sidecar is for wrong subnet").andThen fun _ =>
        (ignoreUnless (!future) "sidecar is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < signed.message.slot))
          "sidecar is not from a slot greater than the latest finalized slot").andThen fun _ =>
        (rejectUnless valid "invalid proposer signature on sidecar block header").andThen
          fun _ =>
        (rejectUnless (decide (parent.slot < signed.message.slot))
          "sidecar is not from a higher slot than its parent").andThen fun _ =>
        (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
          "finalized checkpoint is not an ancestor of sidecar's block").andThen fun _ =>
        (rejectUnless (verifyDataColumnSidecarInclusionProof preset columns.2 sidecar)
          "invalid sidecar inclusion proof").andThen fun _ =>
        (rejectUnless kzgValid "invalid sidecar kzg proofs").andThen fun _ =>
        rejectUnless (signed.message.proposerIndex == expected)
          "sidecar proposer_index does not match expected proposer") := by
  subst header
  have chain := validateSidecarHeader_eq (noun := "sidecar") (signedNoun := "sidecar block header")
    (proofs := fun _ => dataColumnSidecarProofs setup columns.2 sidecar) clock start known
    parentKnown head found signature checkpoint
    (dataColumnSidecarProofs_eq (before := columns.2) kzg) proposerOf
  unfold validateDataColumnSidecar
  simp only [subnetOf, chain, bind, Except.bind, pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]
  simp only [toString, String.reduceAppend, ite_andThen, rejectUnless_andThen]
  simp only [ValidationResult.andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a column sidecar is valid exactly when every check passes. -/
theorem validateDataColumnSidecar_eq_accept
    (header : sidecar.signedBlockHeader columns.2 = signed)
    (subnetOf : computeSubnetForDataColumnSidecar config sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyDataColumnSidecarKzgProofs setup sidecar (noBidBeforeGloas columns.2) =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    validateDataColumnSidecar config checks setup seen store columns sidecar currentTimeMs
        subnetId = .ok accept ↔
      dataColumnSidecarKey columns.2 sidecar ∉ seen.dataColumnSidecarTuples ∧
        verifyDataColumnSidecar preset config sidecar (noBidBeforeGloas columns.2) = true ∧
        subnet = subnetId ∧ future = false ∧
        finalizedSlot < signed.message.slot ∧ valid = true ∧
        parent.slot < signed.message.slot ∧
        finalizedBlock = store.finalizedCheckpoint.root ∧
        verifyDataColumnSidecarInclusionProof preset columns.2 sidecar = true ∧ kzgValid = true ∧
        signed.message.proposerIndex = expected := by
  rw [validateDataColumnSidecar_eq header subnetOf clock start known parentKnown head found
    signature checkpoint kzg proposerOf]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  grind

/-- Once its inputs are computed, a column sidecar is ignored in three cases.

Its key was seen, or its shape and subnet pass and it is early or not after the finalized slot. -/
theorem validateDataColumnSidecar_ignored
    (header : sidecar.signedBlockHeader columns.2 = signed)
    (subnetOf : computeSubnetForDataColumnSidecar config sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyDataColumnSidecarKzgProofs setup sidecar (noBidBeforeGloas columns.2) =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    (∃ reason, validateDataColumnSidecar config checks setup seen store columns sidecar
        currentTimeMs subnetId = .ok (.ignore reason)) ↔
      dataColumnSidecarKey columns.2 sidecar ∈ seen.dataColumnSidecarTuples ∨
        (verifyDataColumnSidecar preset config sidecar (noBidBeforeGloas columns.2) = true ∧
          subnet = subnetId ∧
          (future = true ∨ signed.message.slot ≤ finalizedSlot)) := by
  rw [validateDataColumnSidecar_eq header subnetOf clock start known parentKnown head found
    signature checkpoint kzg proposerOf]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept]
  simp [UInt64.not_lt]
  grind

/-- Once its inputs are computed, a column sidecar is rejected exactly when a check rejects it.

Its key is unseen, and its shape or subnet fails, or a check after the clock checks fails. -/
theorem validateDataColumnSidecar_rejected
    (header : sidecar.signedBlockHeader columns.2 = signed)
    (subnetOf : computeSubnetForDataColumnSidecar config sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (kzg : verifyDataColumnSidecarKzgProofs setup sidecar (noBidBeforeGloas columns.2) =
      .ok kzgValid)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    (∃ reason, validateDataColumnSidecar config checks setup seen store columns sidecar
        currentTimeMs subnetId = .ok (.reject reason)) ↔
      dataColumnSidecarKey columns.2 sidecar ∉ seen.dataColumnSidecarTuples ∧
        (verifyDataColumnSidecar preset config sidecar (noBidBeforeGloas columns.2) = false ∨
          subnet ≠ subnetId ∨
          (future = false ∧ finalizedSlot < signed.message.slot ∧
            (valid = false ∨ signed.message.slot ≤ parent.slot ∨
              finalizedBlock ≠ store.finalizedCheckpoint.root ∨
              verifyDataColumnSidecarInclusionProof preset columns.2 sidecar = false ∨
              kzgValid = false ∨
              signed.message.proposerIndex ≠ expected))) := by
  have accepted := validateDataColumnSidecar_eq_accept (seen := seen) (columns := columns)
    (subnetId := subnetId) header subnetOf clock start known parentKnown head found signature
    checkpoint kzg proposerOf
  have ignored := validateDataColumnSidecar_ignored (seen := seen) (columns := columns)
    (subnetId := subnetId) header subnetOf clock start known parentKnown head found signature
    checkpoint kzg proposerOf
  rw [validateDataColumnSidecar_eq header subnetOf clock start known parentKnown head found
    signature checkpoint kzg proposerOf] at accepted ignored ⊢
  generalize ValidationResult.andThen _ _ = outcome at accepted ignored ⊢
  cases outcome <;> simp [UInt64.not_le] at accepted ignored ⊢ <;> grind

end Column

end EthLib.Consensus
