module

public import EthLib.Consensus.Gossip.Block
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the outcomes of the block topic

The block topic checks a block in a fixed order, so its outcome is a chain of checks.

The chain needs the clock, the finalized slot, the head state and the signature.

It also needs the payload checks, the finalized ancestor and the expected proposer.

Once these are computed, the outcome is that chain.

From the chain follows which blocks the topic accepts and which it ignores.

A valid block records its slot and proposer, and the same block is then ignored.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {statuses : PayloadStatuses}
  {signed : SignedBeaconBlock preset fork} {currentTimeMs : UInt64}

/-! ## Helpers -/

/-- Before Bellatrix a parent with no state makes the block rejected. -/
theorem parentWithoutStateOutcome_of_lt_bellatrix {before : fork < .glamsterdam}
    {body : BeaconBlockBody preset fork} {status : PayloadValidationStatus}
    (early : ¬ .bellatrix ≤ fork) :
    parentWithoutStateOutcome store before body status =
      .ok (.reject "block's parent is invalid") := by
  have notCapella : ¬ .shapella ≤ fork := fun h => early (Nat.le_trans (by decide) h)
  simp [parentWithoutStateOutcome, notCapella, early, pure, Except.pure]

/-- From Capella a parent with no state makes the block rejected or ignored by its payload.

A payload not yet validated rejects, and any other status ignores. -/
theorem parentWithoutStateOutcome_of_capella {before : fork < .glamsterdam}
    {body : BeaconBlockBody preset fork} {status : PayloadValidationStatus}
    (capella : .shapella ≤ fork) :
    parentWithoutStateOutcome store before body status =
      .ok (if status = PAYLOAD_STATUS_NOT_VALIDATED then
        .reject "block's parent is invalid and its payload is optimistic"
      else .ignore "block's parent is invalid and its payload is processed") := by
  simp [parentWithoutStateOutcome, capella, pure, Except.pure]

/-- Before Bellatrix a block has no payload to check. -/
theorem payloadOutcome_of_lt_bellatrix {state : BeaconState preset fork}
    {before : fork < .glamsterdam} {block : BeaconBlock preset fork}
    {status : PayloadValidationStatus} (early : ¬ .bellatrix ≤ fork) :
    payloadOutcome config state before block status = .ok accept := by
  simp [payloadOutcome, early, pure, Except.pure]

/-- Before Deneb a block commits to no blob, so the limit holds. -/
theorem blobCountWithinLimit_of_lt_deneb {before : fork < .glamsterdam}
    {block : BeaconBlock preset fork} (early : ¬ .dencun ≤ fork) :
    blobCountWithinLimit config before block = true := by
  simp [blobCountWithinLimit, early]

/-! ## Blocks -/

/-- A block whose slot and proposer a valid block had already is ignored. -/
theorem validateBeaconBlock_of_seen (gloas : ¬ .glamsterdam ≤ fork)
    (known : (signed.message.slot, signed.message.proposerIndex) ∈ seen.proposerSlots) :
    validateBeaconBlock config checks seen store statuses signed currentTimeMs =
      .ok (.ignore "block is not the first valid block for this slot and proposer") := by
  simp [validateBeaconBlock, gloas, known, pure, Except.pure]

/-- A valid block records its slot and proposer, so the same block is then ignored. -/
theorem validateBeaconBlock_recordBeaconBlock (gloas : ¬ .glamsterdam ≤ fork) :
    validateBeaconBlock config checks (seen.recordBeaconBlock signed) store statuses signed
        currentTimeMs =
      .ok (.ignore "block is not the first valid block for this slot and proposer") :=
  validateBeaconBlock_of_seen gloas (by simp [Seen.recordBeaconBlock])

/-- From Gloas the rule is not yet specified here, so it fails. -/
theorem validateBeaconBlock_of_gloas (gloas : .glamsterdam ≤ fork) :
    validateBeaconBlock config checks seen store statuses signed currentTimeMs =
      .error (.forkNotYetSpecified fork) := by
  simp [validateBeaconBlock, gloas, throw, throwThe, MonadExceptOf.throw]

section Chain

variable {future : Bool} {finalizedSlot : Slot} {parent : BeaconBlock preset fork}
  {parentState state : BeaconState preset fork} {proposer : Validator} {valid : Bool}
  {payload : ValidationResult} {finalizedBlock : Root} {expected : ValidatorIndex}

/-- A block whose parent the node has not seen is ignored.

That check comes after the checks of the seen keys, of the clock and of the finalized slot. -/
theorem validateBeaconBlock_of_unknown_parent (gloas : ¬ .glamsterdam ≤ fork)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (unknown : store.blocks[signed.message.parentRoot]? = none) :
    validateBeaconBlock config checks seen store statuses signed currentTimeMs =
      .ok ((ignoreUnless (!seen.proposerSlots.contains
          (signed.message.slot, signed.message.proposerIndex))
          "block is not the first valid block for this slot and proposer").andThen fun _ =>
        (ignoreUnless (!future) "block is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < signed.message.slot))
          "block is not from a slot greater than the latest finalized slot").andThen fun _ =>
        .ignore "block's parent has not been seen") := by
  unfold validateBeaconBlock
  simp only [gloas, dite_false, clock, start, unknown, bind, Except.bind, pure, Except.pure,
    Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- The outcome of a block is its chain of checks, in order.

This holds once the parent and its state are known and the fallible steps are computed. -/
theorem validateBeaconBlock_eq (gloas : ¬ .glamsterdam ≤ fork)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (payloadChecks : payloadOutcome config state (Nat.lt_of_not_le gloas) signed.message
      (statuses.get signed.message.parentRoot) = .ok payload)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    validateBeaconBlock config checks seen store statuses signed currentTimeMs =
      .ok ((ignoreUnless (!seen.proposerSlots.contains
          (signed.message.slot, signed.message.proposerIndex))
          "block is not the first valid block for this slot and proposer").andThen fun _ =>
        (ignoreUnless (!future) "block is from a future slot").andThen fun _ =>
        (ignoreUnless (decide (finalizedSlot < signed.message.slot))
          "block is not from a slot greater than the latest finalized slot").andThen fun _ =>
        (ignoreUnless (!(decide (.shapella ≤ fork)) ||
          statuses.get signed.message.parentRoot != PAYLOAD_STATUS_INVALIDATED)
          "block's parent is valid and its payload is invalid").andThen fun _ =>
        (rejectUnless valid "invalid proposer signature").andThen fun _ =>
        payload.andThen fun _ =>
        (rejectUnless (decide (parent.slot < signed.message.slot))
          "block is not from a higher slot than its parent").andThen fun _ =>
        (rejectUnless (finalizedBlock == store.finalizedCheckpoint.root)
          "finalized checkpoint is not an ancestor of block").andThen fun _ =>
        (rejectUnless (blobCountWithinLimit config (Nat.lt_of_not_le gloas) signed.message)
          "too many blob kzg commitments").andThen fun _ =>
        rejectUnless (signed.message.proposerIndex == expected)
          "block proposer_index does not match expected proposer") := by
  unfold validateBeaconBlock
  simp only [gloas, dite_false, clock, start, known, parentKnown, head, found, signature,
    payloadChecks, checkpoint, proposerOf, bind, Except.bind, pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]
  cases payload <;> simp only [ValidationResult.andThenM, ValidationResult.andThen, pure,
    Except.pure, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a block with a known parent state is ignored in five cases.

A valid block had its slot and proposer, it is early, or it is not after the finalized slot.

Or, from Capella, the payload of its parent is invalid.

Or it is signed and the payload checks ignore it, which happens only at Bellatrix. -/
theorem validateBeaconBlock_ignored (gloas : ¬ .glamsterdam ≤ fork)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (payloadChecks : payloadOutcome config state (Nat.lt_of_not_le gloas) signed.message
      (statuses.get signed.message.parentRoot) = .ok payload)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    (∃ reason, validateBeaconBlock config checks seen store statuses signed currentTimeMs =
        .ok (.ignore reason)) ↔
      (signed.message.slot, signed.message.proposerIndex) ∈ seen.proposerSlots ∨
        future = true ∨ signed.message.slot ≤ finalizedSlot ∨
        (.shapella ≤ fork ∧
          statuses.get signed.message.parentRoot = PAYLOAD_STATUS_INVALIDATED) ∨
        (valid = true ∧ ∃ reason, payload = .ignore reason) := by
  rw [validateBeaconBlock_eq gloas clock start known parentKnown head found signature
    payloadChecks checkpoint proposerOf]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept]
  cases payload <;> simp [UInt64.not_lt] <;> grind

/-- A block with a known parent state is valid exactly when every check passes.

This holds once its inputs are computed. -/
theorem validateBeaconBlock_eq_accept (gloas : ¬ .glamsterdam ≤ fork)
    (clock : store.isFutureSlot config signed.message.slot currentTimeMs = .ok future)
    (start : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (known : store.blocks[signed.message.parentRoot]? = some parent)
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.proposerIndex.toNat]? = some proposer)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_BEACON_PROPOSER
      signed.message.slot signed.message proposer.pubkey signed.signature = .ok valid)
    (payloadChecks : payloadOutcome config state (Nat.lt_of_not_le gloas) signed.message
      (statuses.get signed.message.parentRoot) = .ok payload)
    (checkpoint : store.getCheckpointBlock signed.message.parentRoot
      store.finalizedCheckpoint.epoch = .ok finalizedBlock)
    (proposerOf : expectedProposer config checks parentState signed.message.slot = .ok expected) :
    validateBeaconBlock config checks seen store statuses signed currentTimeMs = .ok accept ↔
      (signed.message.slot, signed.message.proposerIndex) ∉ seen.proposerSlots ∧
        future = false ∧ finalizedSlot < signed.message.slot ∧
        (¬ .shapella ≤ fork ∨
          statuses.get signed.message.parentRoot ≠ PAYLOAD_STATUS_INVALIDATED) ∧
        valid = true ∧ payload = accept ∧ parent.slot < signed.message.slot ∧
        finalizedBlock = store.finalizedCheckpoint.root ∧
        blobCountWithinLimit config (Nat.lt_of_not_le gloas) signed.message = true ∧
        signed.message.proposerIndex = expected := by
  rw [validateBeaconBlock_eq gloas clock start known parentKnown head found signature
    payloadChecks checkpoint proposerOf]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  grind

end Chain

end EthLib.Consensus
