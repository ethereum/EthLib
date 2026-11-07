module

public import EthLib.Consensus.Gossip.Payload
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the topics of envelopes and of votes on payloads

Each topic checks a message in a fixed order, so its outcome is a chain of checks.

Once the computed inputs are fixed, the outcome is that chain.

From the chain follows which messages each topic accepts and ignores.

A valid message records its key, and a message with the same key is then ignored.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Networking.Gossip.ValidationResult Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {gloas : .glamsterdam ≤ fork}

/-- The limits of the requests accept exactly when each count is within its limit. -/
theorem checkExecutionRequestsLimits_eq_accept {requests : ExecutionRequests preset fork} :
    checkExecutionRequestsLimits gloas requests = .accept ↔
      requests.withdrawals.data.size ≤ preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD.toNat ∧
        requests.consolidations.data.size ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat ∧
        (requests.builderDeposits gloas).data.size ≤
          preset.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD.toNat ∧
        (requests.builderExits gloas).data.size ≤
          preset.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD.toNat := by
  simp only [checkExecutionRequestsLimits, andThen_eq_accept, rejectUnless_eq_accept,
    decide_eq_true_eq]

/-- The limits of the requests never ignore. -/
theorem checkExecutionRequestsLimits_ne_ignore {requests : ExecutionRequests preset fork}
    {reason : String} : checkExecutionRequestsLimits gloas requests ≠ .ignore reason := by
  simp only [checkExecutionRequestsLimits, ne_eq, andThen_eq_ignore, rejectUnless_ne_ignore,
    false_or, and_false, not_false_eq_true]

/-! ## Envelopes -/

section Envelope

variable {signed : SignedExecutionPayloadEnvelope preset fork} {block : BeaconBlock preset fork}
  {state : BeaconState preset fork} {finalizedSlot : Slot} {requestsRoot : Root} {valid : Bool}

/-- An envelope whose block and builder have a valid envelope already is ignored. -/
theorem validateExecutionPayloadEnvelope_of_seen
    (known : (signed.message.beaconBlockRoot, signed.message.builderIndex) ∈
      seen.executionPayloadEnvelopes) :
    validateExecutionPayloadEnvelope config checks seen store gloas signed =
      .ok (.ignore "already seen envelope for this block root from this builder") := by
  simp [validateExecutionPayloadEnvelope, known, pure, Except.pure]

/-- After a valid envelope, an envelope of the same builder for the same block is ignored. -/
theorem validateExecutionPayloadEnvelope_recordExecutionPayloadEnvelope
    {other : SignedExecutionPayloadEnvelope preset fork}
    (sameRoot : other.message.beaconBlockRoot = signed.message.beaconBlockRoot)
    (sameBuilder : other.message.builderIndex = signed.message.builderIndex) :
    validateExecutionPayloadEnvelope config checks (seen.recordExecutionPayloadEnvelope signed)
        store gloas other =
      .ok (.ignore "already seen envelope for this block root from this builder") :=
  validateExecutionPayloadEnvelope_of_seen (by
    simp [Seen.recordExecutionPayloadEnvelope, sameRoot, sameBuilder])

/-- The outcome of an envelope is its chain of checks, in order.

It holds once the block, its state, the finalized slot, two roots and the signature are fixed. -/
theorem validateExecutionPayloadEnvelope_eq
    (known : store.blocks[signed.message.beaconBlockRoot]? = some block)
    (held : store.blockStates[signed.message.beaconBlockRoot]? = some state)
    (finalized : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (rooted : SszType.hashTreeRoot signed.message.executionRequests = .ok requestsRoot)
    (signature : verifyExecutionPayloadEnvelopeSignature config checks state gloas signed =
      .ok valid) :
    validateExecutionPayloadEnvelope config checks seen store gloas signed =
      .ok ((ignoreUnless (!seen.executionPayloadEnvelopes.contains
            (signed.message.beaconBlockRoot, signed.message.builderIndex))
          "already seen envelope for this block root from this builder").andThen fun _ =>
        (ignoreUnless (finalizedSlot ≤ signed.message.payload.slotNumber gloas)
          "envelope is from a slot before the latest finalized slot").andThen fun _ =>
        (rejectUnless (block.slot == signed.message.payload.slotNumber gloas)
          "block's slot does not match payload's slot number").andThen fun _ =>
        (rejectUnless (signed.message.builderIndex ==
            (block.body.signedExecutionPayloadBid gloas).message.builderIndex)
          "envelope's builder index does not match the bid's builder index").andThen fun _ =>
        (rejectUnless (signed.message.payload.blockHash ==
            (block.body.signedExecutionPayloadBid gloas).message.blockHash)
          "payload's block hash does not match the bid's block hash").andThen fun _ =>
        (rejectUnless (requestsRoot ==
            (block.body.signedExecutionPayloadBid gloas).message.executionRequestsRoot)
          "envelope's execution requests root does not match the bid's").andThen fun _ =>
        (checkExecutionRequestsLimits gloas signed.message.executionRequests).andThen fun _ =>
        (rejectUnless
            ((signed.message.payload.withdrawals (Nat.le_trans (by decide) gloas)).data.size ≤
              preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat) "too many withdrawals").andThen fun _ =>
        rejectUnless valid "invalid envelope signature") := by
  unfold validateExecutionPayloadEnvelope
  simp only [known, held, finalized, rooted, signature, bind, Except.bind, pure, Except.pure,
    Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM,
    rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]
  cases checkExecutionRequestsLimits gloas signed.message.executionRequests <;>
    simp [andThenM, andThen, pure, Except.pure, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, an envelope is ignored exactly in two cases.

Its builder has a valid envelope for its block already, or its slot is before the finalized slot.
-/
theorem validateExecutionPayloadEnvelope_ignored
    (known : store.blocks[signed.message.beaconBlockRoot]? = some block)
    (held : store.blockStates[signed.message.beaconBlockRoot]? = some state)
    (finalized : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (rooted : SszType.hashTreeRoot signed.message.executionRequests = .ok requestsRoot)
    (signature : verifyExecutionPayloadEnvelopeSignature config checks state gloas signed =
      .ok valid) :
    (∃ reason, validateExecutionPayloadEnvelope config checks seen store gloas signed =
        .ok (.ignore reason)) ↔
      (signed.message.beaconBlockRoot, signed.message.builderIndex) ∈
          seen.executionPayloadEnvelopes ∨
        signed.message.payload.slotNumber gloas < finalizedSlot := by
  rw [validateExecutionPayloadEnvelope_eq known held finalized rooted signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  have limits := @checkExecutionRequestsLimits_ne_ignore _ _ gloas signed.message.executionRequests
  repeat' split
  all_goals simp_all [andThen_eq_ignore, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
  all_goals omega

/-- Once its inputs are computed, an envelope is valid exactly when every check passes. -/
theorem validateExecutionPayloadEnvelope_eq_accept
    (known : store.blocks[signed.message.beaconBlockRoot]? = some block)
    (held : store.blockStates[signed.message.beaconBlockRoot]? = some state)
    (finalized : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (rooted : SszType.hashTreeRoot signed.message.executionRequests = .ok requestsRoot)
    (signature : verifyExecutionPayloadEnvelopeSignature config checks state gloas signed =
      .ok valid) :
    validateExecutionPayloadEnvelope config checks seen store gloas signed = .ok accept ↔
      (signed.message.beaconBlockRoot, signed.message.builderIndex) ∉
          seen.executionPayloadEnvelopes ∧
        finalizedSlot ≤ signed.message.payload.slotNumber gloas ∧
        block.slot = signed.message.payload.slotNumber gloas ∧
        signed.message.builderIndex =
          (block.body.signedExecutionPayloadBid gloas).message.builderIndex ∧
        signed.message.payload.blockHash =
          (block.body.signedExecutionPayloadBid gloas).message.blockHash ∧
        requestsRoot = (block.body.signedExecutionPayloadBid gloas).message.executionRequestsRoot ∧
        checkExecutionRequestsLimits gloas signed.message.executionRequests = .accept ∧
        (signed.message.payload.withdrawals (Nat.le_trans (by decide) gloas)).data.size ≤
          preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat ∧
        valid = true := by
  rw [validateExecutionPayloadEnvelope_eq known held finalized rooted signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [andThen_eq_accept]
  all_goals intros
  all_goals simp_all [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  all_goals omega

/-- An envelope whose block is not known is ignored, after the check of the seen keys. -/
theorem validateExecutionPayloadEnvelope_of_unknown
    (fresh : (signed.message.beaconBlockRoot, signed.message.builderIndex) ∉
      seen.executionPayloadEnvelopes)
    (unknown : store.blocks[signed.message.beaconBlockRoot]? = none) :
    validateExecutionPayloadEnvelope config checks seen store gloas signed =
      .ok (.ignore "envelope's block has not been seen") := by
  simp [validateExecutionPayloadEnvelope, fresh, unknown, pure, Except.pure]

/-- An envelope whose block is known without a state is rejected, after the seen keys. -/
theorem validateExecutionPayloadEnvelope_of_failed
    (fresh : (signed.message.beaconBlockRoot, signed.message.builderIndex) ∉
      seen.executionPayloadEnvelopes)
    (known : store.blocks[signed.message.beaconBlockRoot]? = some block)
    (failed : store.blockStates[signed.message.beaconBlockRoot]? = none) :
    validateExecutionPayloadEnvelope config checks seen store gloas signed =
      .ok (.reject "envelope's block failed validation") := by
  simp [validateExecutionPayloadEnvelope, fresh, known, failed, pure, Except.pure]

end Envelope

/-! ## Votes on payloads -/

section PayloadAttestation

variable {message : PayloadAttestationMessage} {currentTimeMs : UInt64} {current : Bool}
  {block : BeaconBlock preset fork} {blockState state : BeaconState preset fork}
  {validator : Validator} {committee : PayloadTimelinessCommittee preset} {valid : Bool}

/-- From Gloas, a vote whose member has a valid vote at its slot already is ignored. -/
theorem validatePayloadAttestationMessage_of_seen
    (gloasSlot : config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset message.data.slot)
    (known : (message.data.slot, message.validatorIndex) ∈ seen.payloadAttestationValidators) :
    validatePayloadAttestationMessage config checks seen store gloas message currentTimeMs =
      .ok (.ignore "already seen payload attestation from this validator") := by
  simp [validatePayloadAttestationMessage, gloasSlot, known, pure, Except.pure]

/-- A valid vote records its key, so a vote of the same member at the same slot is then ignored.
-/
theorem validatePayloadAttestationMessage_recordPayloadAttestationMessage
    {other : PayloadAttestationMessage}
    (gloasSlot : config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset other.data.slot)
    (sameSlot : other.data.slot = message.data.slot)
    (sameValidator : other.validatorIndex = message.validatorIndex) :
    validatePayloadAttestationMessage config checks
        (seen.recordPayloadAttestationMessage message) store gloas other currentTimeMs =
      .ok (.ignore "already seen payload attestation from this validator") :=
  validatePayloadAttestationMessage_of_seen gloasSlot (by
    simp [Seen.recordPayloadAttestationMessage, sameSlot, sameValidator])

/-- The outcome of a vote is its chain of checks, in order.

It holds once the clock, the block, the states, the committee and the signature are fixed. -/
theorem validatePayloadAttestationMessage_eq
    (clock : store.isCurrentSlot config message.data.slot currentTimeMs = .ok current)
    (known : store.blocks[message.data.beaconBlockRoot]? = some block)
    (held : store.blockStates[message.data.beaconBlockRoot]? = some blockState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[message.validatorIndex.toNat]? = some validator)
    (seated : getPtc config state gloas message.data.slot = .ok committee)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_PTC_ATTESTER message.data.slot
      message.data validator.pubkey message.signature = .ok valid) :
    validatePayloadAttestationMessage config checks seen store gloas message currentTimeMs =
      .ok ((rejectUnless (config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset message.data.slot)
          "payload attestation's slot is pre-gloas").andThen fun _ =>
        (ignoreUnless (!seen.payloadAttestationValidators.contains
            (message.data.slot, message.validatorIndex))
          "already seen payload attestation from this validator").andThen fun _ =>
        (ignoreUnless current "payload attestation is not for the current slot").andThen fun _ =>
        (ignoreUnless (block.slot == message.data.slot)
          "payload attestation's block is not at the assigned slot").andThen fun _ =>
        (rejectUnless (committee.toList.contains message.validatorIndex)
          "validator is not in the payload timeliness committee").andThen fun _ =>
        rejectUnless valid "invalid payload attestation signature") := by
  unfold validatePayloadAttestationMessage
  simp only [clock, known, held, head, found, seated, signature, bind, Except.bind, pure,
    Except.pure, Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen,
    rejectUnless_andThenM, rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a vote is ignored exactly in three cases.

Its member has voted at its slot already, its slot is not current, or its block is at another slot.

Each case needs a slot that is not before Gloas, else the vote is rejected first. -/
theorem validatePayloadAttestationMessage_ignored
    (clock : store.isCurrentSlot config message.data.slot currentTimeMs = .ok current)
    (known : store.blocks[message.data.beaconBlockRoot]? = some block)
    (held : store.blockStates[message.data.beaconBlockRoot]? = some blockState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[message.validatorIndex.toNat]? = some validator)
    (seated : getPtc config state gloas message.data.slot = .ok committee)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_PTC_ATTESTER message.data.slot
      message.data validator.pubkey message.signature = .ok valid) :
    (∃ reason, validatePayloadAttestationMessage config checks seen store gloas message
        currentTimeMs = .ok (.ignore reason)) ↔
      config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset message.data.slot ∧
        ((message.data.slot, message.validatorIndex) ∈ seen.payloadAttestationValidators ∨
          current = false ∨ block.slot ≠ message.data.slot) := by
  rw [validatePayloadAttestationMessage_eq clock known held head found seated signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all
  all_goals intros
  all_goals simp_all [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  all_goals omega

/-- Once its inputs are computed, a vote is valid exactly when every check passes. -/
theorem validatePayloadAttestationMessage_eq_accept
    (clock : store.isCurrentSlot config message.data.slot currentTimeMs = .ok current)
    (known : store.blocks[message.data.beaconBlockRoot]? = some block)
    (held : store.blockStates[message.data.beaconBlockRoot]? = some blockState)
    (head : store.headState config = .ok state)
    (found : state.validators.data[message.validatorIndex.toNat]? = some validator)
    (seated : getPtc config state gloas message.data.slot = .ok committee)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_PTC_ATTESTER message.data.slot
      message.data validator.pubkey message.signature = .ok valid) :
    validatePayloadAttestationMessage config checks seen store gloas message currentTimeMs =
        .ok accept ↔
      config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset message.data.slot ∧
        (message.data.slot, message.validatorIndex) ∉ seen.payloadAttestationValidators ∧
        current = true ∧ block.slot = message.data.slot ∧
        message.validatorIndex ∈ committee.toList ∧ valid = true := by
  rw [validatePayloadAttestationMessage_eq clock known held head found seated signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all
  all_goals intros
  all_goals simp_all [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  all_goals omega

end PayloadAttestation

end EthLib.Consensus
