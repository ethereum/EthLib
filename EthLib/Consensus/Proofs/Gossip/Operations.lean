module

public import EthLib.Consensus.Gossip.Operations
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the outcomes of the operation topics

Each topic checks a message in a fixed order, so its outcome is a chain of checks.

Once the clock, the head state and each signature are computed, the outcome is that chain.

From the chain follows which messages each topic accepts, ignores and rejects.

A valid message records its key, and the same message is then ignored.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {currentTimeMs : UInt64}
  {state : BeaconState preset fork}

/-- A set of seen keys answers false for a key exactly when the key is not in it. -/
theorem seenKeys_contains_eq_false {keys : Std.TreeSet ValidatorIndex} {index : ValidatorIndex} :
    keys.contains index = false ↔ index ∉ keys := by
  rw [Std.TreeSet.mem_iff_contains, Bool.not_eq_true]

/-! ## Voluntary exits -/

section VoluntaryExit

variable {signed : SignedVoluntaryExit} {future : Bool} {validator : Validator}
  {eligible : Epoch} {valid : Bool}

/-- An exit whose validator has a valid exit already is ignored. -/
theorem validateVoluntaryExit_of_seen
    (known : signed.message.validatorIndex ∈ seen.voluntaryExitIndices) :
    validateVoluntaryExit config checks seen store signed currentTimeMs =
      .ok (.ignore "already seen voluntary exit for this validator") := by
  simp [validateVoluntaryExit, seenKeys_contains_eq_false, known, pure, Except.pure]

/-- A valid exit records its validator, so the same exit is then ignored. -/
theorem validateVoluntaryExit_recordVoluntaryExit :
    validateVoluntaryExit config checks (seen.recordVoluntaryExit signed) store signed
        currentTimeMs =
      .ok (.ignore "already seen voluntary exit for this validator") :=
  validateVoluntaryExit_of_seen (by simp [Seen.recordVoluntaryExit])

/-- An exit whose index names no validator of the head state is rejected.

That check comes after the checks of the seen keys and of the clock. -/
theorem validateVoluntaryExit_of_missing
    (clock : store.isFutureEpoch config signed.message.epoch currentTimeMs = .ok future)
    (head : store.headState config = .ok state)
    (missing : state.validators.data[signed.message.validatorIndex.toNat]? = none) :
    validateVoluntaryExit config checks seen store signed currentTimeMs =
      .ok ((ignoreUnless (!seen.voluntaryExitIndices.contains signed.message.validatorIndex)
          "already seen voluntary exit for this validator").andThen fun _ =>
        (ignoreUnless (!future) "voluntary exit epoch is in the future").andThen fun _ =>
        .reject "validator index out of range") := by
  unfold validateVoluntaryExit
  simp only [clock, head, missing, bind, Except.bind, pure, Except.pure,
    ignoreUnless_andThenM, ignoreUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- The outcome of an exit is its chain of checks, in order.

This holds once the clock, the head state, the eligible epoch and the signature are computed. -/
theorem validateVoluntaryExit_eq
    (clock : store.isFutureEpoch config signed.message.epoch currentTimeMs = .ok future)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.validatorIndex.toNat]? = some validator)
    (sum : addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD = .ok eligible)
    (signature : isValidVoluntaryExitSignature config checks state validator.pubkey signed =
      .ok valid) :
    validateVoluntaryExit config checks seen store signed currentTimeMs =
      .ok ((ignoreUnless (!seen.voluntaryExitIndices.contains signed.message.validatorIndex)
          "already seen voluntary exit for this validator").andThen fun _ =>
        (ignoreUnless (!future) "voluntary exit epoch is in the future").andThen fun _ =>
        (ignoreUnless (validator.exitEpoch == FAR_FUTURE_EPOCH)
          "validator has already initiated exit").andThen fun _ =>
        (rejectUnless (isActiveValidator validator (getCurrentEpoch state))
          "validator is not active").andThen fun _ =>
        (rejectUnless (decide (eligible ≤ getCurrentEpoch state))
          "validator has not been active long enough").andThen fun _ =>
        rejectUnless valid "invalid voluntary exit signature") := by
  unfold validateVoluntaryExit
  simp only [clock, head, found, sum, signature, bind, Except.bind, pure, Except.pure,
    Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, an exit is ignored exactly in three cases.

Its validator has a valid exit already, its epoch is in the future, or its validator exits. -/
theorem validateVoluntaryExit_ignored
    (clock : store.isFutureEpoch config signed.message.epoch currentTimeMs = .ok future)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.validatorIndex.toNat]? = some validator)
    (sum : addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD = .ok eligible)
    (signature : isValidVoluntaryExitSignature config checks state validator.pubkey signed =
      .ok valid) :
    (∃ reason, validateVoluntaryExit config checks seen store signed currentTimeMs =
        .ok (.ignore reason)) ↔
      signed.message.validatorIndex ∈ seen.voluntaryExitIndices ∨
        future = true ∨ validator.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  rw [validateVoluntaryExit_eq clock head found sum signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false, UInt64.le_iff_toNat_le]
  all_goals omega

/-- Once its inputs are computed, an exit is valid exactly when every check passes. -/
theorem validateVoluntaryExit_eq_accept
    (clock : store.isFutureEpoch config signed.message.epoch currentTimeMs = .ok future)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.validatorIndex.toNat]? = some validator)
    (sum : addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD = .ok eligible)
    (signature : isValidVoluntaryExitSignature config checks state validator.pubkey signed =
      .ok valid) :
    validateVoluntaryExit config checks seen store signed currentTimeMs = .ok accept ↔
      signed.message.validatorIndex ∉ seen.voluntaryExitIndices ∧
        future = false ∧ validator.exitEpoch = FAR_FUTURE_EPOCH ∧
        isActiveValidator validator (getCurrentEpoch state) = true ∧
        eligible ≤ getCurrentEpoch state ∧ valid = true := by
  rw [validateVoluntaryExit_eq clock head found sum signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false, UInt64.le_iff_toNat_le]
  all_goals omega

end VoluntaryExit

/-! ## Proposer slashings -/

section ProposerSlashing

variable {slashing : ProposerSlashing} {proposer : Validator} {valid1 valid2 : Bool}

/-- A slashing of a proposer that has a valid slashing already is ignored. -/
theorem validateProposerSlashing_of_seen
    (known : slashing.signedHeader1.message.proposerIndex ∈ seen.proposerSlashingIndices) :
    validateProposerSlashing config checks seen store slashing =
      .ok (.ignore "already seen proposer slashing for this proposer") := by
  simp [validateProposerSlashing, seenKeys_contains_eq_false, known, pure, Except.pure]

/-- A valid proposer slashing records its proposer, so the same slashing is then ignored. -/
theorem validateProposerSlashing_recordProposerSlashing :
    validateProposerSlashing config checks (seen.recordProposerSlashing slashing) store slashing =
      .ok (.ignore "already seen proposer slashing for this proposer") :=
  validateProposerSlashing_of_seen (by simp [Seen.recordProposerSlashing])

/-- The outcome of a proposer slashing is its chain of checks, in order.

This holds once the head state and both signatures are computed. -/
theorem validateProposerSlashing_eq (head : store.headState config = .ok state)
    (found : state.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? =
      some proposer)
    (signature1 : isValidHeaderSignature config checks state proposer.pubkey
      slashing.signedHeader1 = .ok valid1)
    (signature2 : isValidHeaderSignature config checks state proposer.pubkey
      slashing.signedHeader2 = .ok valid2) :
    validateProposerSlashing config checks seen store slashing =
      .ok ((ignoreUnless (!seen.proposerSlashingIndices.contains
          slashing.signedHeader1.message.proposerIndex)
          "already seen proposer slashing for this proposer").andThen fun _ =>
        (rejectUnless (slashing.signedHeader1.message.slot == slashing.signedHeader2.message.slot)
          "header slots do not match").andThen fun _ =>
        (rejectUnless (slashing.signedHeader1.message.proposerIndex ==
          slashing.signedHeader2.message.proposerIndex)
          "header proposer indices do not match").andThen fun _ =>
        (rejectUnless (slashing.signedHeader1.message != slashing.signedHeader2.message)
          "headers are not different").andThen fun _ =>
        (rejectUnless (isSlashableValidator proposer (getCurrentEpoch state))
          "proposer is not slashable").andThen fun _ =>
        (rejectUnless valid1 "invalid proposer slashing signature").andThen fun _ =>
        rejectUnless valid2 "invalid proposer slashing signature") := by
  unfold validateProposerSlashing
  simp only [head, found, signature1, signature2, bind, Except.bind, pure, Except.pure,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a proposer slashing is valid exactly when every check passes. -/
theorem validateProposerSlashing_eq_accept (head : store.headState config = .ok state)
    (found : state.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? =
      some proposer)
    (signature1 : isValidHeaderSignature config checks state proposer.pubkey
      slashing.signedHeader1 = .ok valid1)
    (signature2 : isValidHeaderSignature config checks state proposer.pubkey
      slashing.signedHeader2 = .ok valid2) :
    validateProposerSlashing config checks seen store slashing = .ok accept ↔
      slashing.signedHeader1.message.proposerIndex ∉ seen.proposerSlashingIndices ∧
        slashing.signedHeader1.message.slot = slashing.signedHeader2.message.slot ∧
        slashing.signedHeader1.message.proposerIndex =
          slashing.signedHeader2.message.proposerIndex ∧
        slashing.signedHeader1.message ≠ slashing.signedHeader2.message ∧
        isSlashableValidator proposer (getCurrentEpoch state) = true ∧
        valid1 = true ∧ valid2 = true := by
  rw [validateProposerSlashing_eq head found signature1 signature2]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false]

/-- A proposer slashing is ignored only as a duplicate.

Once its inputs are computed, it is ignored exactly when its proposer has a valid slashing. -/
theorem validateProposerSlashing_ignored (head : store.headState config = .ok state)
    (found : state.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? =
      some proposer)
    (signature1 : isValidHeaderSignature config checks state proposer.pubkey
      slashing.signedHeader1 = .ok valid1)
    (signature2 : isValidHeaderSignature config checks state proposer.pubkey
      slashing.signedHeader2 = .ok valid2) :
    (∃ reason, validateProposerSlashing config checks seen store slashing =
        .ok (.ignore reason)) ↔
      slashing.signedHeader1.message.proposerIndex ∈ seen.proposerSlashingIndices := by
  rw [validateProposerSlashing_eq head found signature1 signature2]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false]

end ProposerSlashing

/-! ## Attester slashings -/

section AttesterSlashing

variable {slashing : AttesterSlashing preset fork} {valid1 valid2 : Bool}

/-- An attester slashing whose every slashable validator is already recorded is ignored.

This holds when the two attestations share no validator, since then nothing is new. -/
theorem validateAttesterSlashing_of_seen
    (known : ∀ index ∈ slashableIndices slashing,
      index ∈ seen.attesterSlashingIndices) :
    validateAttesterSlashing config checks seen store slashing =
      .ok (.ignore "all attester slashing indices already seen") := by
  have none_new : (slashableIndices slashing).any
      (!seen.attesterSlashingIndices.contains ·) = false := by
    simpa [seenKeys_contains_eq_false] using known
  simp [validateAttesterSlashing, none_new, pure, Except.pure]

/-- A valid attester slashing records its slashable validators.

So the same slashing is then ignored. -/
theorem validateAttesterSlashing_recordAttesterSlashing :
    validateAttesterSlashing config checks (seen.recordAttesterSlashing slashing) store
        slashing =
      .ok (.ignore "all attester slashing indices already seen") :=
  validateAttesterSlashing_of_seen fun index mem => by
    simp [Seen.recordAttesterSlashing, mem]

/-- The outcome of an attester slashing is its chain of checks, in order.

This holds once the head state and the validity of both attestations are computed. -/
theorem validateAttesterSlashing_eq (head : store.headState config = .ok state)
    (attestation1 : isValidIndexedAttestation config checks state slashing.attestation1 =
      .ok valid1)
    (attestation2 : isValidIndexedAttestation config checks state slashing.attestation2 =
      .ok valid2) :
    validateAttesterSlashing config checks seen store slashing =
      .ok ((ignoreUnless ((slashableIndices slashing).any
          (!seen.attesterSlashingIndices.contains ·))
          "all attester slashing indices already seen").andThen fun _ =>
        (rejectUnless (isSlashableAttestationData slashing.attestation1.data
          slashing.attestation2.data) "attestation data is not slashable").andThen fun _ =>
        (rejectUnless (indicesInRange state slashing.attestation1)
          "validator index out of range in indexed attestation 1").andThen fun _ =>
        (rejectUnless valid1 "invalid indexed attestation 1").andThen fun _ =>
        (rejectUnless (indicesInRange state slashing.attestation2)
          "validator index out of range in indexed attestation 2").andThen fun _ =>
        (rejectUnless valid2 "invalid indexed attestation 2").andThen fun _ =>
        rejectUnless ((slashableIndices slashing).any (isSlashableIndex state))
          "no slashable validators in intersection") := by
  unfold validateAttesterSlashing
  simp only [head, attestation1, attestation2, bind, Except.bind, pure, Except.pure,
    Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- An attester slashing is ignored only when it names no new validator.

Once its inputs are computed, it is ignored exactly when each validator that both name is seen. -/
theorem validateAttesterSlashing_ignored (head : store.headState config = .ok state)
    (attestation1 : isValidIndexedAttestation config checks state slashing.attestation1 =
      .ok valid1)
    (attestation2 : isValidIndexedAttestation config checks state slashing.attestation2 =
      .ok valid2) :
    (∃ reason, validateAttesterSlashing config checks seen store slashing =
        .ok (.ignore reason)) ↔
      ∀ index ∈ slashableIndices slashing, index ∈ seen.attesterSlashingIndices := by
  rw [validateAttesterSlashing_eq head attestation1 attestation2]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false]

/-- Once its inputs are computed, an attester slashing is valid exactly when each check passes. -/
theorem validateAttesterSlashing_eq_accept (head : store.headState config = .ok state)
    (attestation1 : isValidIndexedAttestation config checks state slashing.attestation1 =
      .ok valid1)
    (attestation2 : isValidIndexedAttestation config checks state slashing.attestation2 =
      .ok valid2) :
    validateAttesterSlashing config checks seen store slashing = .ok accept ↔
      (∃ index ∈ slashableIndices slashing,
          index ∉ seen.attesterSlashingIndices) ∧
        isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data = true ∧
        indicesInRange state slashing.attestation1 = true ∧ valid1 = true ∧
        indicesInRange state slashing.attestation2 = true ∧ valid2 = true ∧
        ∃ index ∈ slashableIndices slashing, isSlashableIndex state index = true := by
  rw [validateAttesterSlashing_eq head attestation1 attestation2]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false]

end AttesterSlashing

/-! ## Changes of BLS credentials -/

section BlsToExecutionChange

variable {signed : SignedBLSToExecutionChange} {early : Bool} {validator : Validator}
  {valid : Bool}

/-- A change for a validator that has a valid change already is ignored. -/
theorem validateBlsToExecutionChange_of_seen
    (known : signed.message.validatorIndex ∈ seen.blsToExecutionChangeIndices) :
    validateBlsToExecutionChange config checks seen store signed currentTimeMs =
      .ok (.ignore "already seen BLS to execution change for this validator") := by
  simp [validateBlsToExecutionChange, seenKeys_contains_eq_false, known, pure, Except.pure]

/-- A valid change records its validator, so the same change is then ignored. -/
theorem validateBlsToExecutionChange_recordBlsToExecutionChange :
    validateBlsToExecutionChange config checks (seen.recordBlsToExecutionChange signed) store
        signed currentTimeMs =
      .ok (.ignore "already seen BLS to execution change for this validator") :=
  validateBlsToExecutionChange_of_seen (by simp [Seen.recordBlsToExecutionChange])

/-- The outcome of a change of BLS credentials is its chain of checks, in order.

This holds once the clock, the head state and the signature are computed. -/
theorem validateBlsToExecutionChange_eq
    (clock : store.isFutureEpoch config config.CAPELLA_FORK_EPOCH currentTimeMs = .ok early)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.validatorIndex.toNat]? = some validator)
    (signature : isValidBlsToExecutionChangeSignature config checks state signed = .ok valid) :
    validateBlsToExecutionChange config checks seen store signed currentTimeMs =
      .ok ((ignoreUnless (!seen.blsToExecutionChangeIndices.contains
          signed.message.validatorIndex)
          "already seen BLS to execution change for this validator").andThen fun _ =>
        (ignoreUnless (!early) "current epoch is pre-capella").andThen fun _ =>
        (rejectUnless (blsCredentialsPrefixed validator.withdrawalCredentials)
          "validator does not have BLS withdrawal credentials").andThen fun _ =>
        (rejectUnless (blsCredentialsMatch validator.withdrawalCredentials
          signed.message.fromBlsPubkey)
          "pubkey does not match validator withdrawal credentials").andThen fun _ =>
        rejectUnless valid "invalid BLS to execution change signature") := by
  unfold validateBlsToExecutionChange
  simp only [clock, head, found, signature, bind, Except.bind, pure, Except.pure,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a change of BLS credentials is ignored exactly in two cases.

Its validator has a valid change already, or the clock is before Capella. -/
theorem validateBlsToExecutionChange_ignored
    (clock : store.isFutureEpoch config config.CAPELLA_FORK_EPOCH currentTimeMs = .ok early)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.validatorIndex.toNat]? = some validator)
    (signature : isValidBlsToExecutionChangeSignature config checks state signed = .ok valid) :
    (∃ reason, validateBlsToExecutionChange config checks seen store signed currentTimeMs =
        .ok (.ignore reason)) ↔
      signed.message.validatorIndex ∈ seen.blsToExecutionChangeIndices ∨
        early = true := by
  rw [validateBlsToExecutionChange_eq clock head found signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false]

/-- Once its inputs are computed, a change of credentials is valid exactly when all checks pass. -/
theorem validateBlsToExecutionChange_eq_accept
    (clock : store.isFutureEpoch config config.CAPELLA_FORK_EPOCH currentTimeMs = .ok early)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.validatorIndex.toNat]? = some validator)
    (signature : isValidBlsToExecutionChangeSignature config checks state signed = .ok valid) :
    validateBlsToExecutionChange config checks seen store signed currentTimeMs = .ok accept ↔
      signed.message.validatorIndex ∉ seen.blsToExecutionChangeIndices ∧
        early = false ∧ blsCredentialsPrefixed validator.withdrawalCredentials = true ∧
        blsCredentialsMatch validator.withdrawalCredentials signed.message.fromBlsPubkey =
          true ∧
        valid = true := by
  rw [validateBlsToExecutionChange_eq clock head found signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [seenKeys_contains_eq_false]

end BlsToExecutionChange

end EthLib.Consensus
