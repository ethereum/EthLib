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

A partial column sidecar is checked in three parts: its counts, its header, then its cells.

The counts read nothing but the sidecar, so they decide first whatever the store holds.

A header that passes is recorded before the cells, so it stays recorded when they fail.

From Gloas a column sidecar has no header, and its chain reads the block that it names.

A valid one has the slot of that block, and one cell per commitment of its bid.

From Gloas a partial sidecar has no header either, and its chain also reads its block.

It is ignored only when that block is unseen.
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

/-! ## Column sidecars from Gloas -/

section GloasColumn

variable {gloas : .glamsterdam ≤ fork} {sidecar : DataColumnSidecar preset fork}
  {subnet : SubnetID} {future valid : Bool} {block : BeaconBlock preset fork}
  {state : BeaconState preset fork}

/-- From Gloas the commitments of a sidecar are those of the bid it is checked against. -/
theorem DataColumnSidecar.commitments_of_gloas
    {bidCommitments : Since .glamsterdam fork (BlobKZGCommitments preset fork)} :
    sidecar.commitments bidCommitments = bidCommitments gloas := by
  have notBefore : ¬ fork < .glamsterdam := Nat.not_lt_of_le gloas
  simp [DataColumnSidecar.commitments, notBefore]

/-- From Gloas a column sidecar whose block and column a valid sidecar had already is ignored. -/
theorem validateGloasDataColumnSidecar_of_seen
    (known : (sidecar.beaconBlockRoot gloas, sidecar.index) ∈ seen.dataColumnSidecarRoots) :
    validateGloasDataColumnSidecar config setup seen store gloas sidecar currentTimeMs subnetId =
      .ok (.ignore "already seen sidecar for this block root and index") := by
  simp [validateGloasDataColumnSidecar, known, pure, Except.pure]

/-- From Gloas a valid column sidecar records its key, so the same sidecar is then ignored. -/
theorem validateGloasDataColumnSidecar_recordGloasDataColumnSidecar :
    validateGloasDataColumnSidecar config setup (seen.recordGloasDataColumnSidecar gloas sidecar)
        store gloas sidecar currentTimeMs subnetId =
      .ok (.ignore "already seen sidecar for this block root and index") :=
  validateGloasDataColumnSidecar_of_seen (by simp [Seen.recordGloasDataColumnSidecar])

/-- From Gloas the outcome of a column sidecar is its chain of checks, in order.

It holds once the subnet, the clock, the block with its state and the KZG check are computed. -/
theorem validateGloasDataColumnSidecar_eq
    (subnetOf : computeSubnetForDataColumnSidecar config sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config (sidecar.slot gloas) currentTimeMs = .ok future)
    (known : store.blocks[sidecar.beaconBlockRoot gloas]? = some block)
    (held : store.blockStates[sidecar.beaconBlockRoot gloas]? = some state)
    (proofs : verifyDataColumnSidecarKzgProofs setup sidecar block.bidCommitments = .ok valid) :
    validateGloasDataColumnSidecar config setup seen store gloas sidecar currentTimeMs subnetId =
      .ok ((ignoreUnless (!seen.dataColumnSidecarRoots.contains
          (sidecar.beaconBlockRoot gloas, sidecar.index))
          "already seen sidecar for this block root and index").andThen fun _ =>
        (rejectUnless (subnet == subnetId) "sidecar is for wrong subnet").andThen fun _ =>
        (ignoreUnless (!future) "sidecar is from a future slot").andThen fun _ =>
        (rejectUnless (sidecar.slot gloas == block.slot)
          "sidecar's slot does not match block's slot").andThen fun _ =>
        (rejectUnless (verifyDataColumnSidecar preset config sidecar block.bidCommitments)
          "invalid sidecar").andThen fun _ =>
        rejectUnless valid "invalid sidecar kzg proofs") := by
  unfold validateGloasDataColumnSidecar
  simp only [subnetOf, clock, known, held, proofs, bind, Except.bind, pure, Except.pure,
    Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM,
    rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- From Gloas a column sidecar is valid exactly when every check passes, once its inputs are set.
-/
theorem validateGloasDataColumnSidecar_eq_accept
    (subnetOf : computeSubnetForDataColumnSidecar config sidecar.index = .ok subnet)
    (clock : store.isFutureSlot config (sidecar.slot gloas) currentTimeMs = .ok future)
    (known : store.blocks[sidecar.beaconBlockRoot gloas]? = some block)
    (held : store.blockStates[sidecar.beaconBlockRoot gloas]? = some state)
    (proofs : verifyDataColumnSidecarKzgProofs setup sidecar block.bidCommitments = .ok valid) :
    validateGloasDataColumnSidecar config setup seen store gloas sidecar currentTimeMs subnetId =
        .ok accept ↔
      (sidecar.beaconBlockRoot gloas, sidecar.index) ∉ seen.dataColumnSidecarRoots ∧
        subnet = subnetId ∧ future = false ∧ sidecar.slot gloas = block.slot ∧
        verifyDataColumnSidecar preset config sidecar block.bidCommitments = true ∧
        valid = true := by
  rw [validateGloasDataColumnSidecar_eq subnetOf clock known held proofs]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  simp

/-- From Gloas a valid column sidecar has the slot of its block.

It also has one cell per commitment of the bid of its block, and at least one. -/
theorem validateGloasDataColumnSidecar_shape
    (known : store.blocks[sidecar.beaconBlockRoot gloas]? = some block)
    (accepted : validateGloasDataColumnSidecar config setup seen store gloas sidecar currentTimeMs
      subnetId = .ok accept) :
    sidecar.slot gloas = block.slot ∧
      sidecar.column.data.size =
        ((block.body.signedExecutionPayloadBid gloas).message.blobKzgCommitments).data.size ∧
      sidecar.column.data.size ≠ 0 := by
  unfold validateGloasDataColumnSidecar at accepted
  simp only [known, ignoreUnless_andThenM, rejectUnless_andThenM, bind, Except.bind] at accepted
  revert accepted
  repeat' (first | split | intro)
  all_goals simp_all [pure, Except.pure, Except.mapError, verifyDataColumnSidecar,
    DataColumnSidecar.commitments_of_gloas (gloas := gloas), BeaconBlock.bidCommitments]
  all_goals omega

end GloasColumn

/-! ## Partial column sidecars, from Fulu -/

section Partial

variable {headers : PartialHeaders preset fork} {root other : Root}
  {header : PartialDataColumnHeader preset fork} {sidecar : PartialDataColumnSidecar preset fork}

/-- A header recorded for a block is the header found for that block. -/
theorem PartialHeaders.find?_record_self :
    (headers.record root header).find? root = some header := by
  simp [PartialHeaders.record, PartialHeaders.find?]

/-- Recording a header for one block keeps the header found for another block. -/
theorem PartialHeaders.find?_record_of_ne (ne : other ≠ root) :
    (headers.record root header).find? other = headers.find? other := by
  unfold PartialHeaders.record PartialHeaders.find?
  have differ : (root == other) = false := by simp [Ne.symm ne]
  simp only [List.find?_cons, differ, List.find?_filter]
  congr 2
  funext entry
  by_cases same : entry.1 = other <;> simp_all

/-! ### The counts, which read nothing but the sidecar -/

/-- The counts reject a sidecar as empty exactly when it has no header and no set bit. -/
theorem partialCountsOutcome_eq_empty :
    partialCountsOutcome sidecar = .reject "partial message is semantically empty" ↔
      sidecar.headers.size ≠ 1 ∧ sidecar.cellsPresentBitmap.bits.count true = 0 := by
  unfold partialCountsOutcome
  simp only [rejectUnless_andThen]
  by_cases first :
      sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0 <;>
    by_cases cells :
      sidecar.partialColumn.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    by_cases proofs :
      sidecar.kzgProofs.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    simp_all [rejectUnless] <;> omega

/-- The counts reject the cells exactly when the sidecar is not empty and its cells miscount. -/
theorem partialCountsOutcome_eq_cells :
    partialCountsOutcome sidecar = .reject "number of cells does not match number of set bits" ↔
      (sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0) ∧
        sidecar.partialColumn.data.size ≠ sidecar.cellsPresentBitmap.bits.count true := by
  unfold partialCountsOutcome
  simp only [rejectUnless_andThen]
  by_cases first :
      sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0 <;>
    by_cases cells :
      sidecar.partialColumn.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    by_cases proofs :
      sidecar.kzgProofs.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    simp_all [rejectUnless] <;> omega

/-- The counts reject the proofs exactly when the earlier counts pass and the proofs miscount. -/
theorem partialCountsOutcome_eq_proofs :
    partialCountsOutcome sidecar = .reject "number of proofs does not match number of set bits" ↔
      (sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0) ∧
        sidecar.partialColumn.data.size = sidecar.cellsPresentBitmap.bits.count true ∧
        sidecar.kzgProofs.data.size ≠ sidecar.cellsPresentBitmap.bits.count true := by
  unfold partialCountsOutcome
  simp only [rejectUnless_andThen]
  by_cases first :
      sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0 <;>
    by_cases cells :
      sidecar.partialColumn.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    by_cases proofs :
      sidecar.kzgProofs.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    simp_all [rejectUnless] <;> omega

/-- The counts pass exactly when the sidecar is not empty and its cells and proofs count. -/
theorem partialCountsOutcome_eq_accept :
    partialCountsOutcome sidecar = .accept ↔
      (sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0) ∧
        sidecar.partialColumn.data.size = sidecar.cellsPresentBitmap.bits.count true ∧
        sidecar.kzgProofs.data.size = sidecar.cellsPresentBitmap.bits.count true := by
  unfold partialCountsOutcome
  simp only [rejectUnless_andThen]
  by_cases first :
      sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0 <;>
    by_cases cells :
      sidecar.partialColumn.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    by_cases proofs :
      sidecar.kzgProofs.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    simp_all [rejectUnless] <;> omega

/-- The counts never ignore a sidecar. -/
theorem partialCountsOutcome_ne_ignore {reason : String} :
    partialCountsOutcome sidecar ≠ .ignore reason := by
  unfold partialCountsOutcome
  simp only [rejectUnless_andThen]
  by_cases first :
      sidecar.headers.size = 1 ∨ sidecar.cellsPresentBitmap.bits.count true ≠ 0 <;>
    by_cases cells :
      sidecar.partialColumn.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    by_cases proofs :
      sidecar.kzgProofs.data.size = sidecar.cellsPresentBitmap.bits.count true <;>
    simp_all [rejectUnless] <;> omega

/-- An empty partial sidecar: no bit, no cell, no proof and no header. -/
def emptyPartialSidecar : PartialDataColumnSidecar preset fork :=
  ⟨⟨#[], by simp⟩, ⟨#[], by simp⟩, ⟨#[], by simp⟩, fun _ => ⟨#[], by simp⟩⟩

/-- An empty partial sidecar is rejected as empty, so that reason can occur. -/
theorem partialCountsOutcome_emptyPartialSidecar :
    partialCountsOutcome (emptyPartialSidecar (preset := preset) (fork := fork)) =
      .reject "partial message is semantically empty" :=
  partialCountsOutcome_eq_empty.mpr
    (by simp only [emptyPartialSidecar, PartialDataColumnSidecar.headers]; split <;> simp)

/-- Before Gloas, a partial sidecar with only a header passes the counts.

So their accept case can occur. -/
theorem partialCountsOutcome_header_only (before : fork < .glamsterdam) :
    partialCountsOutcome { (emptyPartialSidecar : PartialDataColumnSidecar preset fork) with
      header := fun _ => ⟨#[header], by simp⟩ } = .accept :=
  partialCountsOutcome_eq_accept.mpr
    (by simp [emptyPartialSidecar, PartialDataColumnSidecar.headers, before])

/-- In the minimal preset, one set bit with no cell is rejected for its cell count. -/
theorem partialCountsOutcome_bit_without_cell :
    partialCountsOutcome
        { (emptyPartialSidecar : PartialDataColumnSidecar Preset.minimal fork) with
          cellsPresentBitmap := ⟨#[true], fun _ => by decide⟩ } =
      .reject "number of cells does not match number of set bits" :=
  partialCountsOutcome_eq_cells.mpr (by simp [emptyPartialSidecar])

/-! ### The header, against the headers seen and the store -/

variable {config : Config} {setup : TrustedSetup} {currentTimeMs : UInt64}
  {blockRoot : Root} {future : Bool} {finalizedSlot : Slot} {parent : BeaconBlock preset fork}
  {parentState state : BeaconState preset fork} {proposer : Validator} {valid kzgValid : Bool}
  {finalizedBlock : Root} {expected : ValidatorIndex}
  {columnIndex : DataAvailability.ColumnIndex}

/-- A first check that passes leaves the next check, before a chain that may fail. -/
theorem andThen_andThenM {first : ValidationResult} {next : Unit → ValidationResult}
    {rest : Unit → Except ForkChoiceError ValidationResult} :
    (first.andThen next).andThenM rest = first.andThenM fun _ => (next ()).andThenM rest := by
  cases first <;> rfl

/-- The checks of a partial header that read only the headers seen and the header, in order. -/
def partialHeaderPrechecks (config : Config) (headers : PartialHeaders preset fork) (root : Root)
    (header : PartialDataColumnHeader preset fork) (blockRoot : Root) : ValidationResult :=
  (rejectUnless ((headers.find? root).all (· == header))
    "header differs from previously validated header").andThen fun _ =>
  (rejectUnless (blockRoot == root)
    "header's block root does not match group id's block root").andThen fun _ =>
  (rejectUnless (header.kzgCommitments.data.size != 0)
    "header's kzg_commitments is empty").andThen fun _ =>
  rejectUnless (decide (header.kzgCommitments.data.size ≤ (config.getBlobParameters
      (computeEpochAtSlot preset header.signedBlockHeader.message.slot)).maxBlobsPerBlock.toNat))
    "header's kzg_commitments is too long"

/-- A partial header runs its checks that read no store first, then the checks of a header.

This holds once the root of its block is computed, whatever the store holds. -/
theorem partialHeaderOutcome_eq_prechecks
    (hash : Serialization.Ssz.SszType.hashTreeRoot header.signedBlockHeader.message =
      .ok blockRoot) :
    partialHeaderOutcome config checks headers store root header currentTimeMs =
      (partialHeaderPrechecks config headers root header blockRoot).andThenM fun _ =>
        validateSidecarHeader config checks store "header" "header" header.signedBlockHeader
          currentTimeMs fun _ =>
        pure (rejectUnless (verifyPartialDataColumnHeaderInclusionProof preset header)
          "invalid header inclusion proof") := by
  unfold partialHeaderOutcome partialHeaderPrechecks
  simp only [hash, bind, Except.bind, Except.mapError, andThen_andThenM]

/-- A header that fails a check reading no store gets its outcome, whatever the store holds.

This holds once the root of its block is computed. -/
theorem partialHeaderOutcome_of_prechecks
    (hash : Serialization.Ssz.SszType.hashTreeRoot header.signedBlockHeader.message =
      .ok blockRoot)
    (failed : partialHeaderPrechecks config headers root header blockRoot ≠ .accept) :
    partialHeaderOutcome config checks headers store root header currentTimeMs =
      .ok (partialHeaderPrechecks config headers root header blockRoot) := by
  rw [partialHeaderOutcome_eq_prechecks hash, andThenM_of_ne_accept failed]
  rfl

/-- The outcome of a partial header is its chain of checks, in order.

The checks that read only the headers seen and the header come first, then the clock and the store.

This holds once the parent and its state are known and the fallible steps are computed. -/
theorem partialHeaderOutcome_eq
    (hash : Serialization.Ssz.SszType.hashTreeRoot header.signedBlockHeader.message =
      .ok blockRoot)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[header.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[header.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[header.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      header.signedBlockHeader.message.slot header.signedBlockHeader.message proposer.pubkey
      header.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock header.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (proposerOf : expectedProposer config checks parentState
      header.signedBlockHeader.message.slot = .ok expected) :
    partialHeaderOutcome config checks headers store root header currentTimeMs =
      .ok ((rejectUnless ((headers.find? root).all (· == header))
          "header differs from previously validated header").andThen fun _ =>
        (rejectUnless (blockRoot == root)
          "header's block root does not match group id's block root").andThen fun _ =>
        (rejectUnless (header.kzgCommitments.data.size != 0)
          "header's kzg_commitments is empty").andThen fun _ =>
        (rejectUnless (decide (header.kzgCommitments.data.size ≤ (config.getBlobParameters
        (computeEpochAtSlot preset header.signedBlockHeader.message.slot)).maxBlobsPerBlock.toNat))
          "header's kzg_commitments is too long").andThen fun _ =>
        (ignoreUnless (!future) "header is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < header.signedBlockHeader.message.slot))
          "header is not from a slot greater than the latest finalized slot").andThen fun _ =>
        (rejectUnless valid "invalid proposer signature on header").andThen fun _ =>
        (rejectUnless (decide (parent.slot < header.signedBlockHeader.message.slot))
          "header is not from a higher slot than its parent").andThen fun _ =>
        (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
          "finalized checkpoint is not an ancestor of header's block").andThen fun _ =>
        (rejectUnless (verifyPartialDataColumnHeaderInclusionProof preset header)
          "invalid header inclusion proof").andThen fun _ =>
        rejectUnless (header.signedBlockHeader.message.proposerIndex == expected)
          "header proposer_index does not match expected proposer") := by
  have chain := validateSidecarHeader_eq (noun := "header") (signedNoun := "header")
    (proofs := fun _ => pure (rejectUnless (verifyPartialDataColumnHeaderInclusionProof preset
      header) "invalid header inclusion proof")) clock start known parentKnown head found
    signature checkpoint rfl proposerOf
  unfold partialHeaderOutcome
  simp only [chain]
  simp only [hash, bind, Except.bind, pure, Except.pure, Except.mapError, ignoreUnless_andThen,
    rejectUnless_andThenM, rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]
  simp only [toString, String.reduceAppend]

/-- Once its inputs are computed, a partial header is valid exactly when every check passes. -/
theorem partialHeaderOutcome_eq_accept
    (hash : Serialization.Ssz.SszType.hashTreeRoot header.signedBlockHeader.message =
      .ok blockRoot)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[header.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[header.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[header.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      header.signedBlockHeader.message.slot header.signedBlockHeader.message proposer.pubkey
      header.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock header.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (proposerOf : expectedProposer config checks parentState
      header.signedBlockHeader.message.slot = .ok expected) :
    partialHeaderOutcome config checks headers store root header currentTimeMs = .ok accept ↔
      (∀ prior, headers.find? root = some prior → prior = header) ∧ blockRoot = root ∧
        header.kzgCommitments.data.size ≠ 0 ∧
        header.kzgCommitments.data.size ≤ (config.getBlobParameters
        (computeEpochAtSlot preset header.signedBlockHeader.message.slot)).maxBlobsPerBlock.toNat ∧
        future = false ∧ finalizedSlot < header.signedBlockHeader.message.slot ∧ valid = true ∧
        parent.slot < header.signedBlockHeader.message.slot ∧
        finalizedBlock = store.finalizedCheckpoint.root ∧
        verifyPartialDataColumnHeaderInclusionProof preset header = true ∧
        header.signedBlockHeader.message.proposerIndex = expected := by
  rw [partialHeaderOutcome_eq hash clock start known parentKnown head found signature checkpoint
    proposerOf]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  cases headers.find? root <;> simp <;> grind

/-- Once its inputs are computed, a partial header is ignored exactly when the clock ignores it.

The checks before the clock pass, and the header is early or not after the finalized slot. -/
theorem partialHeaderOutcome_ignored
    (hash : Serialization.Ssz.SszType.hashTreeRoot header.signedBlockHeader.message =
      .ok blockRoot)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[header.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[header.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[header.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      header.signedBlockHeader.message.slot header.signedBlockHeader.message proposer.pubkey
      header.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock header.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (proposerOf : expectedProposer config checks parentState
      header.signedBlockHeader.message.slot = .ok expected) :
    (∃ reason, partialHeaderOutcome config checks headers store root header currentTimeMs =
        .ok (.ignore reason)) ↔
      (∀ prior, headers.find? root = some prior → prior = header) ∧ blockRoot = root ∧
        header.kzgCommitments.data.size ≠ 0 ∧
        header.kzgCommitments.data.size ≤ (config.getBlobParameters
        (computeEpochAtSlot preset header.signedBlockHeader.message.slot)).maxBlobsPerBlock.toNat ∧
        (future = true ∨ header.signedBlockHeader.message.slot ≤ finalizedSlot) := by
  rw [partialHeaderOutcome_eq hash clock start known parentKnown head found signature checkpoint
    proposerOf]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept]
  cases headers.find? root <;> simp [UInt64.not_lt] <;> grind

/-- Once its inputs are computed, a partial header is rejected exactly when a check rejects it.

A check before the clock fails, or the clock checks pass and a later check fails. -/
theorem partialHeaderOutcome_rejected
    (hash : Serialization.Ssz.SszType.hashTreeRoot header.signedBlockHeader.message =
      .ok blockRoot)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[header.signedBlockHeader.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[header.signedBlockHeader.message.parentRoot]? =
      some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[header.signedBlockHeader.message.proposerIndex.toNat]? =
      some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      header.signedBlockHeader.message.slot header.signedBlockHeader.message proposer.pubkey
      header.signedBlockHeader.signature = .ok valid)
    (checkpoint : store.getCheckpointBlock header.signedBlockHeader.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (proposerOf : expectedProposer config checks parentState
      header.signedBlockHeader.message.slot = .ok expected) :
    (∃ reason, partialHeaderOutcome config checks headers store root header currentTimeMs =
        .ok (.reject reason)) ↔
      (∃ prior, headers.find? root = some prior ∧ prior ≠ header) ∨ blockRoot ≠ root ∨
        header.kzgCommitments.data.size = 0 ∨
        (config.getBlobParameters (computeEpochAtSlot preset
          header.signedBlockHeader.message.slot)).maxBlobsPerBlock.toNat <
          header.kzgCommitments.data.size ∨
        (future = false ∧ finalizedSlot < header.signedBlockHeader.message.slot ∧
          (valid = false ∨ header.signedBlockHeader.message.slot ≤ parent.slot ∨
            finalizedBlock ≠ store.finalizedCheckpoint.root ∨
            verifyPartialDataColumnHeaderInclusionProof preset header = false ∨
            header.signedBlockHeader.message.proposerIndex ≠ expected)) := by
  have accepted := partialHeaderOutcome_eq_accept (headers := headers) (root := root)
    hash clock start known parentKnown head found signature checkpoint proposerOf
  have ignored := partialHeaderOutcome_ignored (headers := headers) (root := root)
    hash clock start known parentKnown head found signature checkpoint proposerOf
  rw [partialHeaderOutcome_eq hash clock start known parentKnown head found signature checkpoint
    proposerOf] at accepted ignored ⊢
  generalize ValidationResult.andThen _ _ = outcome at accepted ignored ⊢
  cases outcome <;> simp [UInt64.not_le] at accepted ignored ⊢ <;> grind

/-! ### The cells, against the header recorded for their block -/

/-- Cells whose block has no recorded header are ignored. -/
theorem partialCellsOutcome_of_unknown (unknown : headers.find? root = none) :
    partialCellsOutcome config setup headers store root sidecar currentTimeMs columnIndex =
      .ok (.ignore "valid corresponding header has not been seen") := by
  simp [partialCellsOutcome, unknown, pure, Except.pure]

/-- The outcome of cells is their chain of checks, in order.

This holds once their header is recorded and the fallible steps are computed. -/
theorem partialCellsOutcome_eq
    (recorded : headers.find? root = some header)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (kzg : verifyPartialDataColumnSidecarKzgProofs setup sidecar header.kzgCommitments
      columnIndex = .ok kzgValid) :
    partialCellsOutcome config setup headers store root sidecar currentTimeMs columnIndex =
      .ok ((ignoreUnless (!future) "corresponding header is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < header.signedBlockHeader.message.slot))
          "corresponding header is not from a slot greater than the latest finalized slot").andThen
          fun _ =>
        (rejectUnless (sidecar.cellsPresentBitmap.bits.size == header.kzgCommitments.data.size)
          "bitmap length does not match commitments length").andThen fun _ =>
        rejectUnless kzgValid "invalid sidecar kzg proofs") := by
  unfold partialCellsOutcome
  simp only [recorded, clock, start, kzg, bind, Except.bind, pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once their inputs are computed, cells are valid exactly when every check passes. -/
theorem partialCellsOutcome_eq_accept
    (recorded : headers.find? root = some header)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (kzg : verifyPartialDataColumnSidecarKzgProofs setup sidecar header.kzgCommitments
      columnIndex = .ok kzgValid) :
    partialCellsOutcome config setup headers store root sidecar currentTimeMs columnIndex =
        .ok accept ↔
      future = false ∧ finalizedSlot < header.signedBlockHeader.message.slot ∧
        sidecar.cellsPresentBitmap.bits.size = header.kzgCommitments.data.size ∧
        kzgValid = true := by
  rw [partialCellsOutcome_eq recorded clock start kzg]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  grind

/-- Once their inputs are computed, cells are ignored exactly when the clock ignores them.

Their header is then early or not after the finalized slot. -/
theorem partialCellsOutcome_ignored
    (recorded : headers.find? root = some header)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (kzg : verifyPartialDataColumnSidecarKzgProofs setup sidecar header.kzgCommitments
      columnIndex = .ok kzgValid) :
    (∃ reason, partialCellsOutcome config setup headers store root sidecar currentTimeMs
        columnIndex = .ok (.ignore reason)) ↔
      future = true ∨ header.signedBlockHeader.message.slot ≤ finalizedSlot := by
  rw [partialCellsOutcome_eq recorded clock start kzg]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept]
  simp [UInt64.not_lt]
  grind

/-- Once their inputs are computed, cells are rejected exactly when a later check rejects them.

The clock checks pass, and the bitmap length or the KZG check fails. -/
theorem partialCellsOutcome_rejected
    (recorded : headers.find? root = some header)
    (clock : store.isFutureSlot config header.signedBlockHeader.message.slot currentTimeMs =
      .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (kzg : verifyPartialDataColumnSidecarKzgProofs setup sidecar header.kzgCommitments
      columnIndex = .ok kzgValid) :
    (∃ reason, partialCellsOutcome config setup headers store root sidecar currentTimeMs
        columnIndex = .ok (.reject reason)) ↔
      future = false ∧ finalizedSlot < header.signedBlockHeader.message.slot ∧
        (sidecar.cellsPresentBitmap.bits.size ≠ header.kzgCommitments.data.size ∨
          kzgValid = false) := by
  have accepted := partialCellsOutcome_eq_accept (setup := setup) (sidecar := sidecar)
    recorded clock start kzg
  have ignored := partialCellsOutcome_ignored (setup := setup) (sidecar := sidecar)
    recorded clock start kzg
  rw [partialCellsOutcome_eq recorded clock start kzg] at accepted ignored ⊢
  generalize ValidationResult.andThen _ _ = outcome at accepted ignored ⊢
  cases outcome <;> simp [UInt64.not_le] at accepted ignored ⊢ <;> grind

/-! ### The whole rule: counts, then header, then cells -/

variable {fulu : .fusaka ≤ fork ∧ fork < .glamsterdam} {group : PartialDataColumnGroupID fork}
  {outcome : ValidationResult}

/-- A sidecar whose counts fail gets their outcome, and the headers stay as they were.

The counts come first, so this holds whatever the store and the headers are. -/
theorem validatePartialDataColumnSidecar_of_counts
    (counts : partialCountsOutcome sidecar ≠ .accept) :
    validatePartialDataColumnSidecar config checks setup headers store fulu sidecar currentTimeMs
        group columnIndex =
      .ok (partialCountsOutcome sidecar, headers) := by
  unfold validatePartialDataColumnSidecar
  generalize partialCountsOutcome sidecar = first at counts ⊢
  cases first <;> simp_all [pure, Except.pure]

/-- A sidecar with a header that its checks do not accept gets their outcome.

The headers stay as they were, and the cells are not checked. -/
theorem validatePartialDataColumnSidecar_of_header_not_accept
    (counts : partialCountsOutcome sidecar = .accept)
    (present : sidecar.headers[0]? = some header)
    (checked : partialHeaderOutcome config checks headers store group.beaconBlockRoot header
      currentTimeMs = .ok outcome)
    (notAccepted : outcome ≠ .accept) :
    validatePartialDataColumnSidecar config checks setup headers store fulu sidecar currentTimeMs
        group columnIndex =
      .ok (outcome, headers) := by
  unfold validatePartialDataColumnSidecar
  cases outcome <;> simp_all [bind, Except.bind, pure, Except.pure]

/-- A sidecar with a header that its checks accept records that header before its cells.

The outcome is then the outcome of the cells against the new headers, if any bit is set. -/
theorem validatePartialDataColumnSidecar_of_header_accept
    (counts : partialCountsOutcome sidecar = .accept)
    (present : sidecar.headers[0]? = some header)
    (checked : partialHeaderOutcome config checks headers store group.beaconBlockRoot header
      currentTimeMs = .ok .accept) :
    validatePartialDataColumnSidecar config checks setup headers store fulu sidecar currentTimeMs
        group columnIndex =
      (if sidecar.cellsPresentBitmap.bits.count true = 0 then .ok .accept else
        partialCellsOutcome config setup (headers.record group.beaconBlockRoot header) store
          group.beaconBlockRoot sidecar currentTimeMs columnIndex).map
        (·, headers.record group.beaconBlockRoot header) := by
  unfold validatePartialDataColumnSidecar
  simp only [counts, present, checked, bind, Except.bind, pure, Except.pure]
  split
  · rfl
  · cases partialCellsOutcome config setup (headers.record group.beaconBlockRoot header) store
      group.beaconBlockRoot sidecar currentTimeMs columnIndex <;> rfl

/-- A sidecar with no header is the outcome of its cells, and the headers stay as they were. -/
theorem validatePartialDataColumnSidecar_of_no_header
    (counts : partialCountsOutcome sidecar = .accept)
    (absent : sidecar.headers[0]? = none) :
    validatePartialDataColumnSidecar config checks setup headers store fulu sidecar currentTimeMs
        group columnIndex =
      (if sidecar.cellsPresentBitmap.bits.count true = 0 then .ok .accept else
        partialCellsOutcome config setup headers store group.beaconBlockRoot sidecar
          currentTimeMs columnIndex).map (·, headers) := by
  unfold validatePartialDataColumnSidecar
  simp only [counts, absent, bind, Except.bind, pure, Except.pure]
  split
  · rfl
  · cases partialCellsOutcome config setup headers store group.beaconBlockRoot sidecar
      currentTimeMs columnIndex <;> rfl

/-- A header that its checks accept stays recorded whatever its cells give.

So a valid header followed by cells that fail is still the header of its block. -/
theorem validatePartialDataColumnSidecar_records_header {after : PartialHeaders preset fork}
    (counts : partialCountsOutcome sidecar = .accept)
    (present : sidecar.headers[0]? = some header)
    (checked : partialHeaderOutcome config checks headers store group.beaconBlockRoot header
      currentTimeMs = .ok .accept)
    (run : validatePartialDataColumnSidecar config checks setup headers store fulu sidecar
      currentTimeMs group columnIndex = .ok (outcome, after)) :
    after = headers.record group.beaconBlockRoot header := by
  rw [validatePartialDataColumnSidecar_of_header_accept counts present checked] at run
  split at run
  · simp_all [Except.map]
  · cases cells : partialCellsOutcome config setup (headers.record group.beaconBlockRoot header)
      store group.beaconBlockRoot sidecar currentTimeMs columnIndex <;>
      simp_all [Except.map]

end Partial

/-! ## Partial column sidecars, from Gloas -/

section GloasPartial

variable {gloas : .glamsterdam ≤ fork} {sidecar : PartialDataColumnSidecar preset fork}
  {group : PartialDataColumnGroupID fork} {columnIndex : DataAvailability.ColumnIndex}
  {block : BeaconBlock preset fork} {state : BeaconState preset fork} {valid : Bool}
  {reason : String}

/-- From Gloas the outcome of a partial sidecar is its chain of checks, in order.

It holds once the block of the group, its state and the KZG check are computed. -/
theorem validateGloasPartialDataColumnSidecar_eq
    (known : store.blocks[group.beaconBlockRoot]? = some block)
    (held : store.blockStates[group.beaconBlockRoot]? = some state)
    (proofs : verifyPartialDataColumnSidecarKzgProofs setup sidecar (block.bidCommitments gloas)
      columnIndex = .ok valid) :
    validateGloasPartialDataColumnSidecar setup store gloas sidecar group columnIndex =
      .ok ((partialCountsOutcome sidecar).andThen fun _ =>
        (rejectUnless (group.slot gloas == block.slot)
          "group id's slot does not match the block's slot").andThen fun _ =>
        (rejectUnless (sidecar.cellsPresentBitmap.bits.size ==
            (block.bidCommitments gloas).data.size)
          "bitmap length does not match commitments length").andThen fun _ =>
        rejectUnless valid "invalid sidecar kzg proofs") := by
  unfold validateGloasPartialDataColumnSidecar
  by_cases counts : partialCountsOutcome sidecar = .accept
  · simp only [counts, known, held, proofs, ValidationResult.accept_andThenM,
      ValidationResult.accept_andThen, bind, Except.bind, pure, Except.pure, Except.mapError,
      rejectUnless_andThenM, rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]
  · simp only [ValidationResult.andThenM_of_ne_accept counts, ValidationResult.andThen_of_ne_accept
      counts, pure, Except.pure]

/-- From Gloas a partial sidecar is valid exactly when every check passes, once its inputs are set.
-/
theorem validateGloasPartialDataColumnSidecar_eq_accept
    (known : store.blocks[group.beaconBlockRoot]? = some block)
    (held : store.blockStates[group.beaconBlockRoot]? = some state)
    (proofs : verifyPartialDataColumnSidecarKzgProofs setup sidecar (block.bidCommitments gloas)
      columnIndex = .ok valid) :
    validateGloasPartialDataColumnSidecar setup store gloas sidecar group columnIndex =
        .ok accept ↔
      partialCountsOutcome sidecar = .accept ∧ group.slot gloas = block.slot ∧
        sidecar.cellsPresentBitmap.bits.size = (block.bidCommitments gloas).data.size ∧
        valid = true := by
  rw [validateGloasPartialDataColumnSidecar_eq (gloas := gloas) known held proofs]
  simp only [Except.ok.injEq, ValidationResult.andThen_eq_accept, rejectUnless_eq_accept]
  simp

/-- From Gloas a partial sidecar is ignored exactly when its counts pass and its block is unseen.

So the rule ignores for no other reason, whatever the store and the KZG check give. -/
theorem validateGloasPartialDataColumnSidecar_eq_ignore :
    validateGloasPartialDataColumnSidecar setup store gloas sidecar group columnIndex =
        .ok (.ignore reason) ↔
      partialCountsOutcome sidecar = .accept ∧ store.blocks[group.beaconBlockRoot]? = none ∧
        reason = "group id's block has not been seen" := by
  unfold validateGloasPartialDataColumnSidecar
  by_cases counts : partialCountsOutcome sidecar = .accept
  · simp only [counts, ValidationResult.accept_andThenM, true_and]
    cases known : store.blocks[group.beaconBlockRoot]? with
    | none => simp [pure, Except.pure, eq_comm]
    | some block =>
      cases held : store.blockStates[group.beaconBlockRoot]? with
      | none => simp [pure, Except.pure]
      | some state =>
        simp only [reduceCtorEq, false_and, iff_false]
        simp only [bind, Except.bind, pure, Except.pure, Except.mapError, rejectUnless_andThenM]
        -- The slot check and the bitmap check reject, so they never ignore.
        split
        · split
          · cases verifyPartialDataColumnSidecarKzgProofs setup sidecar
                (block.bidCommitments gloas) columnIndex with
            | error e => simp
            | ok verdict =>
              -- The KZG check accepts or rejects, and never ignores.
              cases verdict <;> simp [rejectUnless]
          · simp
        · simp
  · simp only [ValidationResult.andThenM_of_ne_accept counts, pure, Except.pure, Except.ok.injEq]
    cases h : partialCountsOutcome sidecar <;> simp_all [partialCountsOutcome_ne_ignore]

/-- From Gloas a partial sidecar whose block is known without a state is rejected.

That holds once its counts pass, since its block failed validation. -/
theorem validateGloasPartialDataColumnSidecar_of_failed
    (counts : partialCountsOutcome sidecar = .accept)
    (known : store.blocks[group.beaconBlockRoot]? = some block)
    (failed : store.blockStates[group.beaconBlockRoot]? = none) :
    validateGloasPartialDataColumnSidecar setup store gloas sidecar group columnIndex =
      .ok (.reject "group id's block failed validation") := by
  unfold validateGloasPartialDataColumnSidecar
  simp [counts, known, failed, pure, Except.pure]

end GloasPartial

end EthLib.Consensus
