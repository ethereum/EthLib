module

import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Checked reads for historical-anchor transport

A receiver can read the weight of an older committee window in its own balance state.

The caller's successful read supplies the arithmetic at the first slot.

The receiver's longer committee window supplies the shorter window and its final-slot arithmetic.

Successful registry lookups and an active total then supply the checked balance read.
-/

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- Activity at any queried epoch requires a finite activation epoch. -/
private theorem finiteActivation {state : BeaconState preset fork} {epoch : Epoch}
    {position : Nat} (active : isActiveAt state epoch position = true) :
    ∃ validator, state.validators.data[position]? = some validator ∧
      validator.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨validator, found, active⟩ := isActiveAt_eq_true_iff.mp active
  refine ⟨validator, found, ?_⟩
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  intro far
  have below := UInt64.lt_iff_toNat_lt.mp active.2
  have above := UInt64.le_iff_toNat_le.mp active.1
  rw [far] at above
  have bound := validator.exitEpoch.toNat_lt
  change 18446744073709551615 ≤ epoch.toNat at above
  omega

/-- Entries beyond a historical registry boundary still await activation eligibility. -/
private def PendingTail (count : Nat) (epoch : Epoch) (state : BeaconState preset fork) : Prop :=
  ∀ index validator, count ≤ index → state.validators.data[index]? = some validator →
    epoch < validator.activationEligibilityEpoch ∧ validator.activationEpoch = FAR_FUTURE_EPOCH

/-- Equal registries preserve the pending suffix without any slot condition. -/
private theorem pendingTail_of_validators {state after : BeaconState preset fork}
    {count : Nat} {epoch : Epoch} (same : after.validators.data = state.validators.data)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  intro index validator lower found
  exact tail index validator lower (same ▸ found)

/-- Replacing an entry preserves the suffix if it preserves the entry's pending condition. -/
private theorem pendingTail_setValidatorAt_of {state after : BeaconState preset fork}
    {position count : Nat} {epoch : Epoch} {old validator : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after)
    (kept : epoch < old.activationEligibilityEpoch → old.activationEpoch = FAR_FUTURE_EPOCH →
      epoch < validator.activationEligibilityEpoch ∧ validator.activationEpoch = FAR_FUTURE_EPOCH)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  intro index entry lower read
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at read
  split at read
  · rename_i same
    subst index
    cases read
    obtain ⟨eligible, pending⟩ := tail position old lower
      (by rw [Array.getElem?_eq_getElem inside, oldEq])
    exact kept eligible pending
  · exact tail index entry lower read

/-- Replacing an entry with unchanged activation fields preserves the suffix. -/
private theorem pendingTail_setValidatorAt {state after : BeaconState preset fork}
    {position count : Nat} {epoch : Epoch} {old validator : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after)
    (eligibility : validator.activationEligibilityEpoch = old.activationEligibilityEpoch)
    (activation : validator.activationEpoch = old.activationEpoch)
    (tail : PendingTail count epoch state) : PendingTail count epoch after :=
  pendingTail_setValidatorAt_of found set
    (fun eligible pending => ⟨eligibility ▸ eligible, activation.trans pending⟩) tail

/-- Effective-balance updates cannot change pending activation eligibility or activation. -/
private theorem pendingTail_processEffectiveBalanceUpdates {state after : BeaconState preset fork}
    {count : Nat} {epoch : Epoch}
    (run : processEffectiveBalanceUpdates state = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  apply foldlM_ok_invariant (PendingTail count epoch) (fun s i t before ok => ?_) tail run
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact pendingTail_setValidatorAt found set rfl rfl before

/-- Scheduling an exit preserves both activation fields of the pending suffix. -/
private theorem pendingTail_initiateValidatorExit {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    {count : Nat} {epoch : Epoch}
    (run : initiateValidatorExit config state index = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  obtain ⟨validator, found, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok run
  · rw [unchanged.2]; exact tail
  · have same := (exitQueue_validators queue).1
    rw [setValidator_eq_setValidatorAt] at set
    have queuedFound : getValidatorAt queued index.toNat = .ok validator := by
      rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]
      exact found
    exact pendingTail_setValidatorAt queuedFound set rfl rfl
      (pendingTail_of_validators (congrArg (·.data) same) tail)

/-- Slashing changes exit, withdrawal and slashed fields, but not pending activation fields. -/
private theorem pendingTail_slashValidator {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    {whistleblower : Option ValidatorIndex} {count : Nat} {epoch : Epoch}
    (run : slashValidator config state index whistleblower = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  obtain ⟨exited, old, _, marked, _, _, _, _, _, _, _, last, exitedOk, found, _, set,
    _, _, _, lowered, _, _, raised, final, done⟩ := slashValidator_ok run
  have same := (slashValidator_last (last := last) (after := after) (index := index)
    (by subst done; rfl)).1.trans ((increaseBalance_validators final).trans
      ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  rw [setValidator_eq_setValidatorAt] at set
  rw [getValidator_eq_getValidatorAt] at found
  exact pendingTail_of_validators (congrArg (·.data) same)
    (pendingTail_setValidatorAt found set rfl rfl
      (pendingTail_initiateValidatorExit exitedOk tail))

/-- A proposer slashing preserves the pending activation suffix. -/
private theorem pendingTail_processProposerSlashing {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    {count : Nat} {epoch : Epoch}
    (run : processProposerSlashing config checks state slashing = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at run
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := run
  exact pendingTail_slashValidator slashed tail

/-- An attester-slashing step either keeps the state or slashes its selected validator. -/
private theorem pendingTail_slashIfSlashable {config : Config}
    {step next : BeaconState preset fork × Bool} {index : ValidatorIndex}
    {count : Nat} {epoch : Epoch}
    (run : slashIfSlashable config step index = .ok next)
    (tail : PendingTail count epoch step.1) : PendingTail count epoch next.1 := by
  obtain ⟨state, flag⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at run
  obtain ⟨_, _, run⟩ := run
  split at run
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at run
    obtain ⟨_, slashed, rfl⟩ := run
    exact pendingTail_slashValidator slashed tail
  · simp only [pure, Except.pure, Except.ok.injEq] at run
    exact run ▸ tail

/-- The existing attester-slashing fold preserves the pending activation suffix. -/
private theorem pendingTail_processAttesterSlashing {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    {count : Nat} {epoch : Epoch}
    (run : processAttesterSlashing config checks state slashing = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at run
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := run
  exact foldlM_ok_invariant (fun step => PendingTail count epoch step.1)
    (fun _ _ _ before ok => pendingTail_slashIfSlashable ok before) tail folded

/-- Electra registry updates cannot activate entries beyond the finalized boundary. -/
private theorem pendingTail_updateRegistryEntryElectra {config : Config}
    {state after : BeaconState preset fork} {index count : Nat} {epoch activation : Epoch}
    (run : updateRegistryEntryElectra config activation state index = .ok after)
    (boundary : epoch ≤ getCurrentEpoch state)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at run
  obtain ⟨old, found, rest⟩ := run
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at rest
    obtain ⟨next, nextOk, set⟩ := rest
    apply pendingTail_setValidatorAt_of found set (fun _ pending => ?_) tail
    have sum := (addChecked_ok_iff.mp nextOk).2
    have bound := UInt64.le_iff_toNat_le.mp boundary
    change epoch < next ∧ old.activationEpoch = FAR_FUTURE_EPOCH
    norm_num only [UInt64.toNat_ofNat] at sum
    exact ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), pending⟩
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok] at rest
    obtain ⟨_, _, exited⟩ := rest
    exact pendingTail_initiateValidatorExit exited tail
  split at rest
  · rename_i eligible
    apply pendingTail_setValidatorAt_of found (liftAccessor_ok.mp rest) (fun beyond _ => ?_) tail
    have lower : old.activationEligibilityEpoch ≤ state.finalizedCheckpoint.epoch := by
      simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at eligible
      exact eligible.1
    exact False.elim (UInt64.not_lt.mpr (UInt64.le_trans lower finalized) beyond)
  · cases rest; exact tail

/-- The actual Electra registry fold preserves a tail beyond the finalized boundary. -/
private theorem pendingTail_processRegistryUpdatesElectra {config : Config}
    {state after : BeaconState preset fork} {count : Nat} {epoch : Epoch}
    (electra : .pectra ≤ fork) (run : processRegistryUpdates config state = .ok after)
    (boundary : epoch ≤ getCurrentEpoch state)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  simp only [processRegistryUpdates, electra, ↓reduceIte, bind_ok_iff, liftAccessor_ok] at run
  obtain ⟨activation, _, folded⟩ := run
  have result := foldlM_ok_invariant
    (fun s => PendingTail count epoch s ∧ s.slot = state.slot ∧
      s.finalizedCheckpoint = state.finalizedCheckpoint)
    (fun s i t before ok => by
      have frame := frame_updateRegistryEntryElectra ok
      refine ⟨pendingTail_updateRegistryEntryElectra ok ?_ ?_ before.1,
        frame.slot.trans before.2.1, frame.finalized.trans before.2.2⟩
      · simpa only [getCurrentEpoch, before.2.1] using boundary
      · simpa only [before.2.2] using finalized)
    ⟨tail, rfl, rfl⟩ folded
  exact result.1

/-- The legacy first pass queues eligibility after the boundary and keeps activation unassigned. -/
private theorem pendingTail_updateRegistryEntry {config : Config}
    {state after : BeaconState preset fork} {index count : Nat} {epoch : Epoch}
    (run : updateRegistryEntry config state index = .ok after)
    (boundary : epoch ≤ getCurrentEpoch state) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at run
  obtain ⟨old, found, queued, queue, marked, set, rest⟩ := run
  have markedTail : PendingTail count epoch marked := by
    apply pendingTail_setValidatorAt_of found set (fun beyond pending => ?_) tail
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
        pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨next, nextOk, rfl⟩ := queue
      have sum := (addChecked_ok_iff.mp nextOk).2
      have bound := UInt64.le_iff_toNat_le.mp boundary
      norm_num only [UInt64.toNat_ofNat] at sum
      change epoch < next ∧ old.activationEpoch = FAR_FUTURE_EPOCH
      exact ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), pending⟩
    · cases queue; exact ⟨beyond, pending⟩
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok] at rest
    obtain ⟨_, _, exited⟩ := rest
    exact pendingTail_initiateValidatorExit exited markedTail
  · cases rest; exact markedTail

/-- Both registry schedules keep the pending suffix beyond their finalized boundary. -/
private theorem pendingTail_processRegistryUpdates {config : Config}
    {state after : BeaconState preset fork} {count : Nat} {epoch : Epoch}
    (run : processRegistryUpdates config state = .ok after)
    (boundary : epoch ≤ getCurrentEpoch state)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  by_cases electra : .pectra ≤ fork
  · exact pendingTail_processRegistryUpdatesElectra electra run boundary finalized tail
  simp only [processRegistryUpdates, electra, ↓reduceIte, bind_ok_iff] at run
  obtain ⟨updated, first, activated⟩ := run
  have updatedFacts := foldlM_ok_invariant
    (fun s => PendingTail count epoch s ∧ s.slot = state.slot ∧
      s.finalizedCheckpoint = state.finalizedCheckpoint)
    (fun s i t before ok => by
      have frame := frame_updateRegistryEntry ok
      refine ⟨pendingTail_updateRegistryEntry ok ?_ before.1,
        frame.slot.trans before.2.1, frame.finalized.trans before.2.2⟩
      simpa only [getCurrentEpoch, before.2.1] using boundary)
    ⟨tail, rfl, rfl⟩ first
  have queueBefore : ∀ index ∈ activationQueue updated, index.toNat < count := by
    intro index member
    obtain ⟨position, validator, equal, found, eligible⟩ := mem_activationQueue member
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have small := updated.validators.bound
      (Nat.lt_trans (Nat.lt_of_not_le electra) (by decide : Fork.pectra < .glamsterdam))
    have exactIndex : index.toNat = position := by
      rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by
        have := UInt64.toNat_lt preset.VALIDATOR_REGISTRY_LIMIT
        change position < 18446744073709551616
        omega)]
    rw [exactIndex]
    by_contra outside
    have beyond := (updatedFacts.1 position validator (Nat.le_of_not_gt outside) found).1
    have lower : validator.activationEligibilityEpoch ≤ updated.finalizedCheckpoint.epoch := by
      simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at eligible
      exact eligible.1
    rw [updatedFacts.2.2] at lower
    exact UInt64.not_lt.mpr (UInt64.le_trans lower finalized) beyond
  apply foldlM_ok_invariant_of_mem (PendingTail count epoch) (fun s index t member before ok => ?_)
    updatedFacts.1 activated
  have lower : index.toNat < count := queueBefore index (List.mem_of_mem_take member)
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, set⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  intro position validator beyond found
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at found
  split at found
  · omega
  · exact before position validator beyond found

/-- A newly deposited validator is pending beyond every finite boundary epoch. -/
private theorem pendingTail_addValidator {state after : BeaconState preset fork}
    {count : Nat} {epoch : Epoch} {pubkey : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (run : addValidatorToRegistry state pubkey credentials amount = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  have added := addValidatorToRegistry_validators_eq_push run
  intro index validator lower found
  rw [added, Array.getElem?_push] at found
  split at found
  · cases found
    exact ⟨finite, rfl⟩
  · exact tail index validator lower found

/-- A pending deposit cannot assign either activation epoch. -/
private theorem pendingTail_applyPendingDeposit {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {deposit : PendingDeposit}
    {count : Nat} {epoch : Epoch}
    (run : applyPendingDeposit config checks state deposit = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  unfold applyPendingDeposit at run
  split at run
  · split at run
    · cases run; exact tail
    simp only [bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    split at run
    · exact pendingTail_addValidator run finite tail
    · cases run; exact tail
  · simp only [liftAccessor_ok, bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    exact pendingTail_of_validators (congrArg (·.data) (increaseBalance_validators run)) tail

/-- Both deposit rules preserve pending activation fields, including a newly appended entry. -/
private theorem pendingTail_applyDeposit {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {pubkey : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    {count : Nat} {epoch : Epoch}
    (run : applyDeposit config checks state pubkey credentials amount signature = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  rcases applyDeposit_cases run with rfl | ⟨_, middle, _, rfl | added, rfl⟩ | ⟨_, applied⟩
  · exact tail
  · exact pendingTail_of_validators rfl tail
  · exact pendingTail_of_validators (state := middle) rfl
      (pendingTail_addValidator added finite tail)
  · exact pendingTail_applyPendingDeposit applied finite tail

/-- Checking a block deposit and advancing its deposit index do not change the pending suffix. -/
private theorem pendingTail_processDeposit {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {before : fork < .hegota} {deposit : Deposit}
    {count : Nat} {epoch : Epoch}
    (run : processDeposit config checks before state deposit = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok run
  exact pendingTail_applyDeposit applied finite (pendingTail_of_validators rfl tail)

/-- A checked voluntary exit preserves the pending activation fields. -/
private theorem pendingTail_processVoluntaryExit {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {signed : SignedVoluntaryExit}
    {count : Nat} {epoch : Epoch}
    (run : processVoluntaryExit config checks state signed = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after :=
  pendingTail_initiateValidatorExit (processVoluntaryExit_initiates run) tail

/-- A credential change leaves both activation fields unchanged. -/
private theorem pendingTail_processBlsToExecutionChange {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange} {count : Nat} {epoch : Epoch}
    (run : processBlsToExecutionChange config checks state signed = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  obtain ⟨old, found, _, _, _, set⟩ := processBlsToExecutionChange_ok run
  rw [setValidator_eq_setValidatorAt] at set
  have read : getValidatorAt state signed.message.validatorIndex.toNat = .ok old := by
    rwa [← getValidator_eq_getValidatorAt]
  exact pendingTail_setValidatorAt read set rfl rfl tail

/-- Withdrawal requests preserve pending activation fields in every successful case. -/
private theorem pendingTail_processWithdrawalRequest {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : WithdrawalRequest} {count : Nat} {epoch : Epoch}
    (run : processWithdrawalRequest config state electra request = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  rcases withdrawalRequest_cases run with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · exact tail
  · exact pendingTail_initiateValidatorExit exited tail
  · exact pendingTail_of_validators
      (congrArg (·.data) (requestPartialWithdrawal_kept withdrawn).1) tail

/-- Switching credentials and queueing excess balance preserve pending activation fields. -/
private theorem pendingTail_switchToCompoundingValidator
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {count : Nat} {epoch : Epoch}
    (run : switchToCompoundingValidator state electra index = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at run
  obtain ⟨old, found, switched, set, queued⟩ := run
  rw [setValidator_eq_setValidatorAt] at set
  have read : getValidatorAt state index.toNat = .ok old := by
    rwa [← getValidator_eq_getValidatorAt]
  exact pendingTail_of_validators
    (congrArg (·.data) (queueExcessActiveBalance_validators queued))
    (pendingTail_setValidatorAt read set rfl rfl tail)

/-- Consolidation queueing changes exit fields, not pending activation fields. -/
private theorem pendingTail_queueConsolidation {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {index target : ValidatorIndex} {source : Validator} {count : Nat} {epoch : Epoch}
    (found : state.validators.data[index.toNat]? = some source)
    (run : queueConsolidation config state electra index source target = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at run
  obtain ⟨⟨churned, exitEpoch⟩, churn, _, _, written, set, _, _, rfl⟩ := run
  have same := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidatorAt churned index.toNat = .ok source := by
    rw [← getValidator_eq_getValidatorAt, getValidator, same, found]
  rw [setValidator_eq_setValidatorAt] at set
  exact pendingTail_of_validators (state := written) rfl
    (pendingTail_setValidatorAt read set rfl rfl
      (pendingTail_of_validators (congrArg (·.data) same) tail))

/-- Every successful consolidation request preserves the pending activation suffix. -/
private theorem pendingTail_processConsolidationRequest {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest} {count : Nat} {epoch : Epoch}
    (run : processConsolidationRequest config state electra request = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  unfold processConsolidationRequest at run
  simp only [bind, Except.bind, pure, Except.pure] at run
  repeat' split at run
  all_goals first
    | (cases run; done)
    | (cases run; exact tail)
    | exact pendingTail_switchToCompoundingValidator (liftAccessor_ok.mp run) tail
    | exact pendingTail_queueConsolidation
        (getElem?_toNat_of_ofNatChecked (by assumption)) run tail

/-- The existing pending-deposit pass transports the suffix through all applied deposits. -/
private theorem pendingTail_passPendingDeposits {config : Config} {checks : SignatureChecks}
    {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei}
    {deposits : List PendingDeposit} {state : BeaconState preset fork}
    {processed : Gwei} {count : Nat} {postponed : Array PendingDeposit} {pass}
    {boundary : Nat} {epoch : Epoch}
    (run : passPendingDeposits config checks stop nextEpoch available state processed count
      postponed deposits = .ok pass) (finite : epoch < FAR_FUTURE_EPOCH)
    (tail : PendingTail boundary epoch state) : PendingTail boundary epoch pass.1.state :=
  passPendingDeposits_of (fun s t => PendingTail boundary epoch s → PendingTail boundary epoch t)
    (fun _ holds => holds) (fun one two holds => two (one holds))
    (fun ok holds => pendingTail_applyPendingDeposit ok finite holds) run tail

/-- Processing an epoch's pending deposits preserves the pending suffix. -/
private theorem pendingTail_processPendingDeposits {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {count : Nat} {epoch : Epoch}
    (run : processPendingDeposits config checks state electra = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  unfold processPendingDeposits at run
  simp only [bind, Except.bind, pure, Except.pure] at run
  repeat' (split at run <;> try cases run)
  all_goals
    exact pendingTail_of_validators rfl (pendingTail_passPendingDeposits ‹_› finite tail)

/-- An active entry cannot belong to the unassigned suffix, even for a future query epoch. -/
private theorem active_before_pendingTail {state : BeaconState preset fork}
    {epoch boundary : Epoch} {count position : Nat}
    (tail : PendingTail count boundary state)
    (active : isActiveAt state epoch position = true) : position < count := by
  obtain ⟨validator, found, finite⟩ := finiteActivation active
  by_contra outside
  exact finite (tail position validator (Nat.le_of_not_gt outside) found).2

/-- A registry containing the historical prefix contains every active queried position.

The prefix inclusion remains a separate input; default-false slashing flags do not supply it. -/
private theorem active_registry_of_pendingTail {state cached : BeaconState preset fork}
    {epoch boundary : Epoch} {count : Nat}
    (tail : PendingTail count boundary state) (contains : count ≤ cached.validators.data.size)
    {position : Nat} (active : isActiveAt state epoch position = true) :
    ∃ validator, cached.validators.data[position]? = some validator := by
  have inside := Nat.lt_of_lt_of_le (active_before_pendingTail tail active) contains
  exact ⟨cached.validators.data[position], Array.getElem?_eq_getElem inside⟩

/-- A finite active stake supplies the checked total, without bounding inactive balances. -/
private theorem activeTotal_exists {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit)
    (bounded : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset < 2 ^ 64) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  let value := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
  have fits : value < 2 ^ 64 := max_lt preset.EFFECTIVE_BALANCE_INCREMENT.toNat_lt bounded
  refine ⟨value.toUInt64, ?_⟩
  unfold getTotalActiveBalance
  rw [getActiveValidatorIndicesChecked_of_within within]
  apply getTotalBalance_ok_iff_stake.mpr
  refine ⟨?_, bounded, UInt64.toNat_ofNat_of_lt' fits⟩
  intro v member
  obtain ⟨validator, found, _⟩ := (mem_getActiveValidatorIndices within).mp member
  exact (Array.getElem?_eq_some_iff.mp found).1

/-- A successful total also bounds a subset, without bounding inactive balances. -/
private theorem totalBalance_exists_of_subset {state : BeaconState preset fork}
    {indices all : List ValidatorIndex} {total : Gwei}
    (read : getTotalBalance state all = .ok total)
    (subset : ∀ v ∈ indices, v ∈ all) :
    ∃ result, getTotalBalance state indices = .ok result := by
  obtain ⟨inside, bounded, -⟩ := getTotalBalance_ok_iff_stake.mp read
  have small : stake (fun v => balanceAt state v.toNat) indices.toFinset < 2 ^ 64 :=
    lt_of_le_of_lt (stake_mono fun v member =>
      List.mem_toFinset.mpr (subset v (List.mem_toFinset.mp member))) bounded
  let value := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (stake (fun v => balanceAt state v.toNat) indices.toFinset)
  have fits : value < 2 ^ 64 := max_lt preset.EFFECTIVE_BALANCE_INCREMENT.toNat_lt small
  refine ⟨value.toUInt64, getTotalBalance_ok_iff_stake.mpr
    ⟨fun v member => inside v (subset v member), small, ?_⟩⟩
  exact UInt64.toNat_ofNat_of_lt' fits

/-- Registry lookups and a checked active total supply a checked filtered total. -/
private theorem filteredTotal_exists {state : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (read : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ active result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) =
        .ok active ∧ getTotalBalance state active = .ok result := by
  obtain ⟨active, filtered⟩ := filterM_exists_ok (test := fun index => do
    return isActiveValidator (← validatorAt state index) (getCurrentEpoch state))
    (list := participants.toList) (fun v member => by
      obtain ⟨validator, found⟩ := inside v (Std.TreeSet.mem_toList.mp member)
      exact ⟨isActiveValidator validator (getCurrentEpoch state), by simp [found]⟩)
  obtain ⟨result, resultOk⟩ := totalBalance_exists_of_subset
    (indices := active) (getTotalActiveBalance_ok read) (fun v member => by
      have passed := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passed
      obtain ⟨validator, found, isActive⟩ := passed
      exact mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, isActive⟩))
  exact ⟨active, result, filtered, resultOk⟩

/-- Execution requests preserve the pending suffix through their three actual folds. -/
private theorem pendingTail_processExecutionRequests {config : Config}
    {source after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam} {boundary : Epoch} {count : Nat}
    (run : processExecutionRequests config source body electra = .ok after)
    (tail : PendingTail count boundary source) : PendingTail count boundary after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at run
  obtain ⟨requested, requestRun, withdrawn, withdrawalRun, consolidationRun⟩ := run
  have requestedTail := foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ holds ok => pendingTail_of_validators
      (congrArg (·.data) (processDepositRequest_ok ok).2.1) holds) tail requestRun
  have withdrawnTail := foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ holds ok => pendingTail_processWithdrawalRequest ok holds)
    requestedTail withdrawalRun
  exact foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ holds ok => pendingTail_processConsolidationRequest ok holds)
    withdrawnTail consolidationRun

/-- The shared operation schedule preserves the pending suffix at every fork before Gloas. -/
private theorem pendingTail_processOperations {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {parentSlot : Slot} (early : fork < .glamsterdam)
    {boundary : Epoch} {count : Nat}
    (run : processOperations config checks source body parentSlot = .ok after)
    (finite : boundary < FAR_FUTURE_EPOCH) (tail : PendingTail count boundary source) :
    PendingTail count boundary after := by
  let R := fun (s t : BeaconState preset fork) =>
    PendingTail count boundary s → PendingTail count boundary t
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of R (fun _ tail => tail) (fun one two tail => two (one tail))
      (fun ok tail => pendingTail_processDeposit ok finite tail)
      (fun ok tail => pendingTail_processVoluntaryExit ok tail)
      (fun ok tail => pendingTail_processBlsToExecutionChange ok tail)
      (fun ok tail => pendingTail_processExecutionRequests ok tail)
      (fun {state after} {gloas} _ => (Nat.not_le.mpr early gloas).elim) run
  have proposerTail := foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ held ok => pendingTail_processProposerSlashing ok held) tail proposersOk
  have slashingTail := foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ held ok => pendingTail_processAttesterSlashing ok held) proposerTail slashingsOk
  exact rest (foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ held ok => pendingTail_of_validators
      (congrArg (·.data) (processAttestation_registry ok).1) held) slashingTail attestedOk)

/-- A block before Gloas transports its input pending tail.

The execution prefix and sync aggregate keep the registry.

Boundary applicability remains an input. -/
private theorem pendingTail_processBlock {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {source after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (early : fork < .glamsterdam)
    {boundary : Epoch} {count : Nat}
    (run : processBlock config checks engine source block = .ok after)
    (finite : boundary < FAR_FUTURE_EPOCH) (tail : PendingTail count boundary source) :
    PendingTail count boundary after := by
  obtain ⟨input, operated, started, operations, _, synced⟩ := processBlock_operationsInput run
  have inputTail := pendingTail_of_validators
    (congrArg (·.data) (started.validators_eq early)) tail
  have same : after.validators = operated.validators := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      rfl
    · cases synced; rfl
  exact pendingTail_of_validators (congrArg (·.data) same)
    (pendingTail_processOperations early operations finite inputTail)

/-- Every non-registry stage preserves the pending tail, including intervening epoch stages. -/
private theorem pendingTail_epochStage {config : Config} {checks : SignatureChecks}
    {stage : EpochStage} {source after : BeaconState preset fork} {count : Nat} {epoch : Epoch}
    (run : EpochStage.action config checks stage source = .ok after)
    (other : stage ≠ .registry) (finite : epoch < FAR_FUTURE_EPOCH)
    (tail : PendingTail count epoch source) : PendingTail count epoch after := by
  have edge := EpochStage.action_cases.mp run
  cases stage
  case registry => exact absurd rfl other
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact pendingTail_processPendingDeposits edge finite tail
    · exact edge ▸ tail
  case effectiveBalances => exact pendingTail_processEffectiveBalanceUpdates edge tail
  all_goals
    exact pendingTail_of_validators
      (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)) tail

/-- An equation-bearing schedule without registry updates transports the pending tail. -/
private theorem pendingTail_epochTrace {config : Config} {checks : SignatureChecks}
    {stages : List EpochStage} {source after : BeaconState preset fork}
    {count : Nat} {epoch : Epoch}
    (trace : EpochTrace (EpochStage.action config checks) stages source after)
    (other : ∀ stage ∈ stages, stage ≠ .registry) (finite : epoch < FAR_FUTURE_EPOCH)
    (tail : PendingTail count epoch source) : PendingTail count epoch after := by
  exact trace.transport
    (fun s t => PendingTail count epoch s → PendingTail count epoch t)
    (fun _ holds => holds) (fun one two holds => two (one holds))
    (fun stage member _ _ run holds =>
      pendingTail_epochStage run (other stage member) finite holds) tail

/-- A successful epoch supplies its prefix, registry equation and complete suffix. -/
private theorem processEpoch_registryCut {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork}
    (run : processEpoch config checks source = .ok after) :
    ∃ ready registered,
      EpochTrace (EpochStage.action config checks)
        [.justification, .inactivity, .rewards] source ready ∧
      processRegistryUpdates config ready = .ok registered ∧
      EpochTrace (EpochStage.action config checks)
        ([.slashings, .eth1Reset, .pendingDeposits, .pendingConsolidations] ++
          EpochStage.middleStages ++ EpochStage.tailStages) registered after := by
  have trace := processEpoch_trace run
  change EpochTrace _ ([.justification, .inactivity, .rewards] ++
    (.registry :: ([.slashings, .eth1Reset, .pendingDeposits, .pendingConsolidations] ++
      EpochStage.middleStages ++ EpochStage.tailStages))) source after at trace
  obtain ⟨ready, before, rest⟩ := EpochTrace.append_iff.mp trace
  cases rest with
  | cons registry suffix => exact ⟨ready, _, before, EpochStage.action_cases.mp registry, suffix⟩

/-- The actual epoch prefix keeps the registry and slot, including the rewards stage. -/
private theorem epochPrefix_kept {config : Config} {checks : SignatureChecks}
    {source ready : BeaconState preset fork}
    (beforeRegistry : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards] source ready) :
    ready.validators = source.validators ∧ ready.slot = source.slot := by
  apply beforeRegistry.transport
    (fun (s t : BeaconState preset fork) => t.validators = s.validators ∧ t.slot = s.slot)
    (fun _ => ⟨rfl, rfl⟩)
    (fun {a b c} (one : b.validators = a.validators ∧ b.slot = a.slot)
      (two : c.validators = b.validators ∧ c.slot = b.slot) =>
      ⟨two.1.trans one.1, two.2.trans one.2⟩)
  intro stage member s t run
  have edge := EpochStage.action_cases.mp run
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals first
    | rw [processRewardsAndPenalties_frame edge]; exact ⟨rfl, rfl⟩
    | exact ⟨edge.validators_eq ⟨nofun, nofun, nofun⟩,
        (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2⟩

/-- Every stage after justification preserves the finalized checkpoint exactly. -/
private theorem finalized_epochTrace {config : Config} {checks : SignatureChecks}
    {stages : List EpochStage} {source after : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks) stages source after)
    (other : ∀ stage ∈ stages, stage ≠ .justification) :
    after.finalizedCheckpoint = source.finalizedCheckpoint := by
  apply trace.transport
    (fun (s t : BeaconState preset fork) => t.finalizedCheckpoint = s.finalizedCheckpoint)
    (fun _ => rfl) (fun one two => two.trans one)
  intro stage member s t run
  have edge := EpochStage.action_cases.mp run
  by_cases deposits : stage = .pendingDeposits
  · subst stage
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact (frame_processPendingDeposits edge).finalized
    · exact edge ▸ rfl
  by_cases payments : stage = .payments
  · subst stage
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact (frame_processBuilderPendingPayments edge).finalized
    · exact edge ▸ rfl
  by_cases participation : stage = .participation
  · subst stage
    simp only [EpochStage.Edge] at edge
    split at edge
    · subst edge; exact (frame_processParticipationFlagUpdates _ _).finalized
    · exact (frame_processParticipationRecordUpdates edge).finalized
  exact (mutatorEpochFrameLaws.toEpochStepLaws.epochEdge
    ⟨other stage member, payments, participation, deposits⟩ run).finalized

/-- The output finalized bound suffices to preserve the tail through an epoch. -/
private theorem pendingTail_processEpoch
    {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork}
    {boundEpoch : Epoch} {count : Nat}
    (run : processEpoch config checks source = .ok after)
    (boundary : boundEpoch ≤ getCurrentEpoch source)
    (finalized : after.finalizedCheckpoint.epoch ≤ boundEpoch)
    (finite : boundEpoch < FAR_FUTURE_EPOCH) (tail : PendingTail count boundEpoch source) :
    PendingTail count boundEpoch after := by
  obtain ⟨ready, registered, beforeRegistry, registry, suffix⟩ := processEpoch_registryCut run
  obtain ⟨validators, slot⟩ := epochPrefix_kept beforeRegistry
  have readyTail := pendingTail_of_validators (congrArg (·.data) validators) tail
  have readyBound : boundEpoch ≤ getCurrentEpoch ready := by
    simpa only [getCurrentEpoch, slot] using boundary
  have same := finalized_epochTrace
    (EpochTrace.cons ((EpochStage.action_cases (stage := .registry)).mpr registry) suffix)
    (by simp [EpochStage.middleStages, EpochStage.tailStages])
  have readyFinalized : ready.finalizedCheckpoint.epoch ≤ boundEpoch := by
    simpa only [same] using finalized
  exact pendingTail_epochTrace suffix
    (by simp [EpochStage.middleStages, EpochStage.tailStages]) finite
    (pendingTail_processRegistryUpdates registry readyBound readyFinalized readyTail)

/-- The actual cache, optional epoch and slot increment preserve the pending suffix. -/
private theorem pendingTail_advanceSlot {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork}
    {boundEpoch : Epoch} {count : Nat}
    (run : advanceSlot config checks source = .ok after)
    (boundary : boundEpoch ≤ getCurrentEpoch source)
    (finalized : after.finalizedCheckpoint.epoch ≤ boundEpoch)
    (finite : boundEpoch < FAR_FUTURE_EPOCH) (tail : PendingTail count boundEpoch source) :
    PendingTail count boundEpoch after := by
  obtain ⟨next, cached, epoched, _, cacheOk, epochOk, rfl⟩ := advanceSlot_ok run
  obtain ⟨_, _, _, _, cacheEq⟩ := processSlot_ok cacheOk
  have cachedTail : PendingTail count boundEpoch cached :=
    pendingTail_of_validators (by rw [cacheEq]) tail
  have epochedTail : PendingTail count boundEpoch epoched := by
    unfold epochIfLast at epochOk
    split at epochOk
    · apply pendingTail_processEpoch epochOk ?_ finalized finite cachedTail
      simpa only [getCurrentEpoch, cacheEq] using boundary
    · cases epochOk; exact cachedTail
  exact epochedTail

/-- The shared successful-slot traversal preserves the tail using its output finalized bound. -/
private theorem pendingTail_processSlots {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork} {slot : Slot} {boundEpoch : Epoch} {count : Nat}
    (holds : Invariant source) (run : processSlots config checks source slot = .ok after)
    (boundary : boundEpoch ≤ getCurrentEpoch source)
    (finalized : after.finalizedCheckpoint.epoch ≤ boundEpoch)
    (finite : boundEpoch < FAR_FUTURE_EPOCH) (tail : PendingTail count boundEpoch source) :
    PendingTail count boundEpoch after := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
  obtain ⟨_, _, advanced⟩ := run
  let R := fun (s t : BeaconState preset fork) =>
    getCurrentEpoch s ≤ getCurrentEpoch t ∧
      (boundEpoch ≤ getCurrentEpoch s → t.finalizedCheckpoint.epoch ≤ boundEpoch →
        PendingTail count boundEpoch s → PendingTail count boundEpoch t)
  have refl : ∀ s, R s s := fun _ => ⟨UInt64.le_refl _, fun _ _ held => held⟩
  have trans : ∀ {s m t}, m.finalizedCheckpoint.epoch ≤ t.finalizedCheckpoint.epoch →
      R s m → R m t → R s t := by
    intro s m t ordered one two
    exact ⟨UInt64.le_trans one.1 two.1, fun low high held =>
      two.2 (UInt64.le_trans low one.1) high
        (one.2 low (UInt64.le_trans ordered high) held)⟩
  have step : ∀ {s t}, Invariant s → advanceSlot config checks s = .ok t → R s t := by
    intro s t _ ok
    exact ⟨(runKept_advanceSlot ok).later, fun low high held =>
      pendingTail_advanceSlot ok low high finite held⟩
  exact (advanceSlots_invariant_of R refl trans step holds advanced).2.2.2 boundary finalized tail

/-- A successful state transition transports its pre-slot input pending tail.

Invariant and finalized applicability remain private inputs at every fork before Gloas. -/
private theorem pendingTail_stateTransition {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {source after : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validate : Bool}
    (early : fork < .glamsterdam)
    {boundary : Epoch} {count : Nat} (holds : Invariant source)
    (run : stateTransition config checks engine source signed validate = .ok after)
    (low : boundary ≤ getCurrentEpoch source)
    (finalized : after.finalizedCheckpoint.epoch ≤ boundary)
    (finite : boundary < FAR_FUTURE_EPOCH) (tail : PendingTail count boundary source) :
    PendingTail count boundary after := by
  obtain ⟨advanced, slots, _, _, block, _⟩ := stateTransition_ok run
  have advancedFinalized : advanced.finalizedCheckpoint.epoch ≤ boundary := by
    simpa only [(frame_processBlock block).finalized] using finalized
  exact pendingTail_processBlock early block finite
    (pendingTail_processSlots holds slots low advancedFinalized finite tail)

private def PendingTailRun (count : Nat) (epoch : Epoch)
    (s t : BeaconState preset fork) : Prop :=
    getCurrentEpoch s ≤ getCurrentEpoch t ∧
      (Invariant s → Invariant t ∧ s.finalizedCheckpoint.epoch ≤ t.finalizedCheckpoint.epoch ∧
        (epoch ≤ getCurrentEpoch s → t.finalizedCheckpoint.epoch ≤ epoch →
          PendingTail count epoch s → PendingTail count epoch t))

private theorem PendingTailRun.refl {count : Nat} {epoch : Epoch}
    (s : BeaconState preset fork) : PendingTailRun count epoch s s :=
  ⟨UInt64.le_refl _, fun inv => ⟨inv, UInt64.le_refl _, fun _ _ tail => tail⟩⟩

private theorem PendingTailRun.trans {count : Nat} {epoch : Epoch}
    {s m t : BeaconState preset fork}
    (one : PendingTailRun count epoch s m) (two : PendingTailRun count epoch m t) :
    PendingTailRun count epoch s t := by
  refine ⟨UInt64.le_trans one.1 two.1, fun inv => ?_⟩
  obtain ⟨middle, firstFinalized, firstTail⟩ := one.2 inv
  obtain ⟨last, secondFinalized, secondTail⟩ := two.2 middle
  exact ⟨last, UInt64.le_trans firstFinalized secondFinalized, fun low high tail =>
    secondTail (UInt64.le_trans low one.1) high
      (firstTail low (UInt64.le_trans secondFinalized high) tail)⟩

private theorem pendingTailRun_processSlots {config : Config} {checks : SignatureChecks}
    {s t : BeaconState preset fork} {slot : Slot} {epoch : Epoch} {count : Nat}
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : processSlots config checks s slot = .ok t) : PendingTailRun count epoch s t := by
  refine ⟨(runKept_processSlots ok).later, fun inv => ?_⟩
  obtain ⟨afterInv, ordered⟩ := processSlots_invariant inv ok
  exact ⟨afterInv, ordered, fun low high tail =>
    pendingTail_processSlots inv ok low high finite tail⟩

private theorem pendingTailRun_processBlock {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork} {epoch : Epoch} {count : Nat}
    (early : fork < .glamsterdam)
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : processBlock config checks engine s block = .ok t) : PendingTailRun count epoch s t := by
  have frame := frame_processBlock ok
  refine ⟨(runKept_processBlock ok).later, fun inv =>
    ⟨frame.invariant inv, ?_,
      fun _ _ tail => pendingTail_processBlock early ok finite tail⟩⟩
  rw [frame.finalized]
  exact UInt64.le_refl _

private theorem pendingTailRun_stateTransition {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {epoch : Epoch} {count : Nat}
    (early : fork < .glamsterdam)
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : stateTransition config checks engine s signed true = .ok t) :
    PendingTailRun count epoch s t := by
  refine ⟨(runKept_stateTransition ok).later, fun inv => ?_⟩
  obtain ⟨afterInv, ordered⟩ := stateTransition_invariant inv ok
  exact ⟨afterInv, ordered, fun low high tail =>
    pendingTail_stateTransition early inv ok low high finite tail⟩

/-- An uncached checkpoint prefix comes from the first actual descendant's slot processing. -/
private theorem relation_of_checkpoint_lookahead {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (R : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ s, R s s) (trans : ∀ {s m t}, R s m → R m t → R s t)
    (edge : ∀ {s t : BeaconState preset fork} {checks' : SignatureChecks}
      {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork},
      stateTransition config checks' engine s signed true = .ok t → R s t)
    (fromPrefix : ∀ {s mid t : BeaconState preset fork} {middle : Slot}
      {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork},
      processSlots config checks s middle = .ok mid → middle ≤ signed.message.slot →
      stateTransition config checks engine s signed true = .ok t → R mid t)
    (slots : ∀ {s t : BeaconState preset fork} {slot : Slot},
      processSlots config checks s slot = .ok t → R s t)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {checkpoint : Checkpoint} {root : Root} {block : BeaconBlock preset fork}
    {start target : Slot} {base source after : BeaconState preset fork}
    (walk : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (bound : start ≤ max block.slot target)
    (baseFound : store.blockStates[checkpoint.root]? = some base)
    (sourceFound : store.blockStates[root]? = some source)
    (advanced : lookaheadState config checks source target = .ok after) :
    ∃ boundary, lookaheadState config checks base start = .ok boundary ∧ R boundary after := by
  by_cases atBlock : start ≤ block.slot
  · obtain ⟨boundary, boundaryOk, related⟩ := reached.relation_of_checkpointPrefix R refl trans
      edge fromPrefix anchorSlot walk found startOk atBlock baseFound sourceFound
    refine ⟨boundary, boundaryOk, trans related ?_⟩
    unfold lookaheadState at advanced
    split at advanced
    · exact slots (mapError_ok_iff.mp advanced)
    · cases advanced; exact refl _
  have below : block.slot < start := UInt64.not_le.mp atBlock
  have rootEq : root = checkpoint.root := by
    simpa [Store.getCheckpointBlock, startOk, Except.mapError,
      Store.getAncestor_of_le (node := ⟨root, .pending⟩) found (UInt64.le_of_lt below),
      bind, Except.bind,
      pure, Except.pure] using walk
  rw [rootEq, baseFound, Option.some.injEq] at sourceFound
  subst source
  have targetBound : start ≤ target := by
    have := UInt64.le_iff_toNat_le.mp bound
    have := UInt64.lt_iff_toNat_lt.mp below
    simp only [toNat_max] at *
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  by_cases before : base.slot < start
  · have advancing : base.slot < target := UInt64.lt_of_lt_of_le before targetBound
    have slotsOk : processSlots config checks base target = .ok after := by
      simpa [lookaheadState, advancing, mapError_ok_iff] using advanced
    rcases UInt64.lt_or_eq_of_le targetBound with strict | rfl
    · obtain ⟨boundary, boundaryOk, rest⟩ := processSlots_split before strict slotsOk
      exact ⟨boundary, by simp [lookaheadState, before, boundaryOk, Except.mapError], slots rest⟩
    · exact ⟨after, advanced, refl _⟩
  · refine ⟨base, by simp [lookaheadState, before, pure, Except.pure], ?_⟩
    unfold lookaheadState at advanced
    split at advanced
    · exact slots (mapError_ok_iff.mp advanced)
    · cases advanced; exact refl _

/-- An uncached checkpoint prefix comes from the first actual descendant's slot processing. -/
private theorem pendingTailRun_checkpointPrefix {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (early : fork < .glamsterdam)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {checkpoint : Checkpoint} {root : Root} {block : BeaconBlock preset fork}
    {start slot : Slot} {source base after : BeaconState preset fork} {epoch : Epoch} {count : Nat}
    (target : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (atOrAfter : start ≤ max block.slot slot)
    (baseFound : store.blockStates[checkpoint.root]? = some base)
    (sourceFound : store.blockStates[root]? = some source)
    (advanced : lookaheadState config checks source slot = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) :
    ∃ boundary, lookaheadState config checks base start = .ok boundary ∧
      PendingTailRun count epoch boundary after := by
  exact relation_of_checkpoint_lookahead (PendingTailRun count epoch)
    PendingTailRun.refl (fun one two => one.trans two)
    (fun ok => pendingTailRun_stateTransition early finite ok)
    (fun slots bound ok => relation_of_processSlots_of_stateTransition (PendingTailRun count epoch)
      (fun one two => one.trans two) (fun rest => pendingTailRun_processSlots finite rest)
      (fun step => pendingTailRun_processBlock early finite step) slots bound ok)
    (fun ok => pendingTailRun_processSlots finite ok)
    anchorSlot reached target found startOk atOrAfter baseFound sourceFound advanced

/-- A held checkpoint bounds every finitely activated source position in the receiver registry.

The source lookahead transports its tail, while the receiver lookahead supplies the prefix size.

Historical applicability is still required separately; no validator identity is inferred. -/
private theorem registry_of_checkpointPrefix {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} (early : fork < .glamsterdam)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorInvariant : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH)
    {checkpoint : Checkpoint} {root sourceRoot : Root}
    {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    {source advancedSource boundaryBase base cached : BeaconState preset fork}
    {sourceTarget : Slot}
    (walk : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (bound : start ≤ max block.slot target)
    (baseFound : store.blockStates[root]? = some base)
    (boundaryBaseFound : store.blockStates[checkpoint.root]? = some boundaryBase)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceRun : lookaheadState config checks source sourceTarget = .ok advancedSource)
    (sourceWalk : store.getCheckpointBlock sourceRoot checkpoint.epoch = .ok checkpoint.root)
    (sourceBlockFound : store.blocks[sourceRoot]? = some sourceBlock)
    (sourceBound : start ≤ max sourceBlock.slot sourceTarget)
    (sourceFound : store.blockStates[sourceRoot]? = some source)
    (finalized : advancedSource.finalizedCheckpoint.epoch ≤ checkpoint.epoch)
    (finite : checkpoint.epoch < FAR_FUTURE_EPOCH) :
    ∀ epoch position, isActiveAt advancedSource epoch position = true →
      ∃ validator, cached.validators.data[position]? = some validator := by
  obtain ⟨boundary, boundaryRun, receiverRun⟩ := relation_of_checkpoint_lookahead
    RunKept RunKept.refl (fun one two => one.trans two)
    (fun ok => runKept_stateTransition ok)
    (fun slots bound ok => runKept_of_processSlots_of_stateTransition slots bound ok)
    (fun ok => runKept_processSlots ok)
    anchorSlot reached walk found startOk bound boundaryBaseFound baseFound advanced
  obtain ⟨sourceBoundary, sourceBoundaryRun, related⟩ := pendingTailRun_checkpointPrefix
    (count := boundary.validators.data.size) early anchorSlot reached sourceWalk
    sourceBlockFound startOk sourceBound boundaryBaseFound sourceFound sourceRun finite
  have same : sourceBoundary = boundary :=
    Except.ok.inj (sourceBoundaryRun.symm.trans boundaryRun)
  subst sourceBoundary
  have holds : Invariant boundary := by
    have baseInv := (reached.reachable.ordered anchorInvariant).2 boundaryBaseFound
    unfold lookaheadState at boundaryRun
    split at boundaryRun
    · exact (processSlots_invariant baseInv (mapError_ok_iff.mp boundaryRun)).1
    · cases boundaryRun; exact baseInv
  obtain ⟨_, _, transport⟩ := related.2 holds
  have low : checkpoint.epoch ≤ getCurrentEpoch boundary := by
    have slotBound : start ≤ boundary.slot := by
      unfold lookaheadState at boundaryRun
      split at boundaryRun
      · exact UInt64.le_of_eq (processSlots_slot (mapError_ok_iff.mp boundaryRun)).2.symm
      · cases boundaryRun
        exact UInt64.not_lt.mp ‹¬ _›
    rw [← computeEpochAtSlot_computeStartSlotAtEpoch positive startOk]
    exact UInt64.le_iff_toNat_le.mpr
      (Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp slotBound))
  have tail : PendingTail boundary.validators.data.size checkpoint.epoch advancedSource :=
    transport low finalized (fun i v outside found => by
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      omega)
  intro epoch position active
  exact active_registry_of_pendingTail tail receiverRun.grows active

/-- The maximum succeeds when its arithmetic, committee, registry and total reads succeed. -/
private theorem maximum_exists_of_total {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei} {covered : Bool}
    (coverage : isFullValidatorSetCovered preset first last = .ok covered)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ maximum, store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum := by
  by_cases empty : last < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  cases covered
  · obtain ⟨active, result, filtered, resultOk⟩ := filteredTotal_exists totalOk inside
    simp only [bind, Except.bind, pure, Except.pure] at filtered
    exact ⟨result, by
      simp only [Store.computeCommitteeWeightBetweenSlots, Store.computeCommitteeWeightAndMembers,
        empty, ↓reduceIte, coverage, bind, Except.bind, Bool.false_eq_true, windowOk,
        filtered, resultOk, Except.mapError, pure, Except.pure]⟩
  · exact ⟨total, by
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered coverage]
      rw [totalOk]; rfl⟩

/-- A successful committee window supplies every shorter window with the same first slot. -/
private theorem committeeWindow_prefix {store : Store preset fork} {head : Root}
    {first last shortLast : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (before : shortLast ≤ last) :
    ∃ short, store.getCommitteesBetweenSlots head first shortLast = .ok short ∧
      ∀ v ∈ short, v ∈ members := by
  have original := read
  unfold Store.getCommitteesBetweenSlots at read
  obtain ⟨afterLast, afterOk, folded⟩ := bind_ok_iff.mp read
  have afterNat := addChecked_ok_iff.mp (mapError_ok_iff.mp afterOk)
  have shorter : shortLast.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have shortOk := addChecked_of_lt shorter
  have shortNat := (addChecked_ok_iff.mp shortOk).2
  have counts : (shortLast + 1).toNat - first.toNat ≤ afterLast.toNat - first.toNat := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have split : List.range (afterLast.toNat - first.toNat) =
      List.range ((shortLast + 1).toNat - first.toNat) ++
        (List.range (afterLast.toNat - first.toNat)).drop
          ((shortLast + 1).toNat - first.toNat) := by
    simpa only [List.take_range, Nat.min_eq_left counts] using
      (List.take_append_drop ((shortLast + 1).toNat - first.toNat)
        (List.range (afterLast.toNat - first.toNat))).symm
  rw [split, List.foldlM_append] at folded
  obtain ⟨short, prefixOk, _⟩ := bind_ok_iff.mp folded
  have shortRead : store.getCommitteesBetweenSlots head first shortLast = .ok short := by
    simpa only [Store.getCommitteesBetweenSlots, shortOk, Except.mapError,
      bind, Except.bind] using prefixOk
  exact ⟨short, shortRead, fun _ member =>
    Store.mem_getCommitteesBetweenSlots_of_le shortRead original before member⟩

/-- A nonempty maximum supplies first-slot arithmetic for another range with the same start. -/
private theorem coverage_exists_of_maximum {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last otherLast afterOther : Slot} {maximum : Gwei}
    (nonempty : first ≤ last)
    (read : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (afterOk : addChecked otherLast 1 = .ok afterOther) :
    ∃ covered, isFullValidatorSetCovered preset first otherLast = .ok covered := by
  have notEmpty : ¬last < first := UInt64.not_lt.mpr nonempty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff] at read
  obtain ⟨result, read, -⟩ := read
  simp only [Store.computeCommitteeWeightAndMembers, notEmpty, ↓reduceIte,
    bind_ok_iff] at read
  obtain ⟨covered, coverage, -⟩ := read
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at coverage
  obtain ⟨afterFirst, firstOk, lastFirst, lastFirstOk, _, _, -⟩ := coverage
  refine ⟨decide (computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterOther), ?_⟩
  simp only [isFullValidatorSetCovered, firstOk, lastFirstOk, afterOk, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- The receiver reads the old maximum from its own balance state.

The caller supplies range arithmetic, not balances or registry containment. -/
private theorem receiver_oldMaximum {caller receiver : Store preset fork}
    {head receiverHead : Root} {source state : BeaconState preset fork}
    {first oldLast last : Slot} {maximum total : Gwei}
    {window : Std.TreeSet ValidatorIndex}
    (read : caller.computeCommitteeWeightBetweenSlots head source first oldLast = .ok maximum)
    (windowOk : receiver.getCommitteesBetweenSlots receiverHead first last = .ok window)
    (before : oldLast ≤ last) (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ window, ∃ validator, validatorAt state v = .ok validator) :
    ∃ result, receiver.computeCommitteeWeightBetweenSlots receiverHead state first oldLast =
      .ok result := by
  by_cases empty : oldLast < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  obtain ⟨members, membersOk, subset⟩ := committeeWindow_prefix windowOk before
  have afterRead := membersOk
  unfold Store.getCommitteesBetweenSlots at afterRead
  obtain ⟨afterOld, afterOk, _⟩ := bind_ok_iff.mp afterRead
  obtain ⟨covered, coverage⟩ := coverage_exists_of_maximum (UInt64.not_lt.mp empty) read
    (mapError_ok_iff.mp afterOk)
  exact maximum_exists_of_total coverage membersOk totalOk
    (fun v member => inside v (subset v member))

/-- Slot processing keeps slashing flags, including the default at an absent position. -/
private def SlashFlagsKept (state after : BeaconState preset fork) : Prop :=
  ∀ i : Nat, (after.validators.data[i]?.map (·.slashed)).getD false =
    (state.validators.data[i]?.map (·.slashed)).getD false

private theorem SlashFlagsKept.refl (state : BeaconState preset fork) :
    SlashFlagsKept state state := fun _ => rfl

private theorem SlashFlagsKept.trans {first second third : BeaconState preset fork}
    (one : SlashFlagsKept first second) (two : SlashFlagsKept second third) :
    SlashFlagsKept first third := fun i => (two i).trans (one i)

private theorem slashFlags_of_validators {state after : BeaconState preset fork}
    (same : after.validators.data = state.validators.data := by rfl) :
    SlashFlagsKept state after := by intro i; simp only [same]

private theorem slashFlags_of_map {state after : BeaconState preset fork}
    (same : after.validators.data.toList.map (·.slashed) =
      state.validators.data.toList.map (·.slashed)) : SlashFlagsKept state after := by
  intro i
  have atIndex := congrArg (fun xs => (xs[i]?).getD false) same
  simpa only [List.getElem?_map, Array.getElem?_toList] using atIndex

private theorem slashFlags_fold {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    {xs : List α} {state after : BeaconState preset fork}
    (keeps : ∀ s x t, step s x = .ok t → SlashFlagsKept s t)
    (ok : xs.foldlM step state = .ok after) : SlashFlagsKept state after :=
  foldlM_ok_invariant (SlashFlagsKept state)
    (fun _ _ _ before ok => before.trans (keeps _ _ _ ok)) (.refl state) ok

/-- Replacing one validator with the same flag keeps the flag map. -/
private theorem slashFlags_setValidatorAt {state after : BeaconState preset fork}
    {position : Nat} {validator old : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after) (same : validator.slashed =
      old.slashed) : SlashFlagsKept state after := by
  apply slashFlags_of_map
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.toList_set, List.map_set]
  rw [same, ← oldEq]
  have atValue : (state.validators.data.toList.map (·.slashed))[position]'(by
      simpa using inside) = state.validators.data[position].slashed := by simp
  rw [← atValue]
  exact List.set_getElem_self _

/-- Exit scheduling changes neither existing slashing flags nor registry length. -/
private theorem slashFlags_initiateValidatorExit {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    (run : initiateValidatorExit config state index = .ok after) :
    SlashFlagsKept state after := by
  obtain ⟨validator, found, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok run
  · rw [unchanged.2]; exact .refl _
  · have same := (exitQueue_validators queue).1
    have kept := slashFlags_setValidatorAt
      (by rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]; exact found)
      (by rwa [← setValidator_eq_setValidatorAt]) (by rfl)
    exact (slashFlags_of_validators (congrArg (·.data) same)).trans kept

/-- Registry updates schedule activity without changing slashing flags. -/
private theorem slashFlags_processRegistryUpdates {config : Config}
    {state after : BeaconState preset fork}
    (run : processRegistryUpdates config state = .ok after) : SlashFlagsKept state after := by
  have update {s t : BeaconState preset fork} {i : Nat}
      (ok : updateRegistryEntry config s i = .ok t) : SlashFlagsKept s t := by
    simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, queued, queue, marked, set, ok⟩ := ok
    have flag : queued.slashed = validator.slashed := by
      unfold queueForActivation at queue
      split at queue
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
        obtain ⟨_, _, rfl⟩ := queue
        rfl
      · cases queue; rfl
    have first := slashFlags_setValidatorAt found set flag
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact first.trans (slashFlags_initiateValidatorExit exited)
    · cases ok; exact first
  have activate {s t : BeaconState preset fork} {i : ValidatorIndex}
      (ok : activateValidator s i = .ok t) : SlashFlagsKept s t := by
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, set⟩ := ok
    rw [setValidator_eq_setValidatorAt] at set
    rw [getValidator_eq_getValidatorAt] at found
    exact slashFlags_setValidatorAt found set rfl
  have updateElectra {s t : BeaconState preset fork} {epoch : Epoch} {i : Nat}
      (ok : updateRegistryEntryElectra config epoch s i = .ok t) : SlashFlagsKept s t := by
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact slashFlags_setValidatorAt found set rfl
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact slashFlags_initiateValidatorExit exited
    split at ok
    · exact slashFlags_setValidatorAt found (liftAccessor_ok.mp ok) rfl
    · cases ok; exact .refl _
  unfold processRegistryUpdates at run
  split at run
  · simp only [bind_ok_iff, liftAccessor_ok] at run
    obtain ⟨_, _, run⟩ := run
    exact slashFlags_fold (fun _ _ _ ok => updateElectra ok) run
  · simp only [bind_ok_iff] at run
    obtain ⟨_, updated, activated⟩ := run
    exact (slashFlags_fold (fun _ _ _ ok => update ok) updated).trans
      (slashFlags_fold (fun _ _ _ ok => activate ok) activated)

/-- A new validator has the same false flag as an absent registry position. -/
private theorem slashFlags_addValidator {state after : BeaconState preset fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (run : addValidatorToRegistry state pubkey credentials amount = .ok after) :
    SlashFlagsKept state after := by
  have added := addValidatorToRegistry_validators_eq_push run
  intro i
  rw [added]
  by_cases before : i < state.validators.data.size
  · simp [Array.getElem?_push, before, Nat.ne_of_lt before]
  · by_cases atEnd : i = state.validators.data.size
    · subst i
      simp [getValidatorFromDeposit]
    · simp [Array.getElem?_push, before, atEnd]

/-- A pending deposit credits a balance or appends an unslashed validator. -/
private theorem slashFlags_applyPendingDeposit {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {deposit : PendingDeposit}
    (run : applyPendingDeposit config checks state deposit = .ok after) :
    SlashFlagsKept state after := by
  unfold applyPendingDeposit at run
  split at run
  · split at run
    · cases run; exact .refl _
    simp only [bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    split at run
    · exact slashFlags_addValidator run
    · cases run; exact .refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    exact slashFlags_of_validators (congrArg (·.data) (increaseBalance_validators run))

/-- Passing pending deposits preserves flags even when the registry grows. -/
private theorem slashFlags_passPendingDeposits {config : Config} {checks : SignatureChecks}
    {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei}
    {deposits : List PendingDeposit} {state : BeaconState preset fork}
    {processed : Gwei} {count : Nat} {postponed : Array PendingDeposit} {pass}
    (run : passPendingDeposits config checks stop nextEpoch available state processed count
      postponed deposits = .ok pass) : SlashFlagsKept state pass.1.state :=
  passPendingDeposits_of SlashFlagsKept .refl (fun one two => one.trans two)
    (fun ok => slashFlags_applyPendingDeposit ok) run

/-- Effective-balance updates preserve each slashing flag. -/
private theorem slashFlags_processEffectiveBalanceUpdates {state after : BeaconState preset fork}
    (run : processEffectiveBalanceUpdates state = .ok after) : SlashFlagsKept state after := by
  apply slashFlags_fold (fun _ _ _ ok => ?_) run
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact slashFlags_setValidatorAt found set rfl

/-- Every stage in the shared epoch schedule preserves the default-false slashing flag. -/
private theorem slashFlags_processEpoch {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (run : processEpoch config checks state = .ok after) : SlashFlagsKept state after := by
  apply (processEpoch_trace run).transport SlashFlagsKept .refl (fun a b => a.trans b)
  intro stage _ s t ok
  have edge := EpochStage.action_cases.mp ok
  cases stage
  case registry => exact slashFlags_processRegistryUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · unfold processPendingDeposits at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact (slashFlags_passPendingDeposits ‹_›).trans slashFlags_of_validators
    · exact edge ▸ .refl _
  case effectiveBalances => exact slashFlags_processEffectiveBalanceUpdates edge
  all_goals
    exact slashFlags_of_validators
      (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

/-- Successful lookahead preserves flags across any number of epochs, at every position. -/
private theorem slashFlags_lookahead {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) : SlashFlagsKept state after := by
  have step {s t : BeaconState preset fork}
      (ok : advanceSlot config checks s = .ok t) : SlashFlagsKept s t := by
    obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have first : SlashFlagsKept s cached := slashFlags_of_validators (by rw [cachedEq])
    have middle : SlashFlagsKept cached epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · exact slashFlags_processEpoch epochedOk
      · cases epochedOk; exact .refl _
    exact (first.trans middle).trans slashFlags_of_validators
  have steps {count : Nat} {s t : BeaconState preset fork}
      (ok : advanceSlots config checks count s = .ok t) : SlashFlagsKept s t := by
    induction count generalizing s with
    | zero => cases ok; exact .refl _
    | succ count ih =>
      obtain ⟨_, first, rest⟩ := bind_ok_iff.mp ok
      exact (step first).trans (ih rest)
  unfold lookaheadState at run
  split at run
  · have slotsOk := mapError_ok_iff.mp run
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, advanced⟩ := slotsOk
    exact steps advanced
  · cases run; exact .refl _

/-- Folding a committee into a set preserves a property held by both inputs. -/
private theorem members_array_insert {committee : Array ValidatorIndex}
    {members : Std.TreeSet ValidatorIndex} (P : ValidatorIndex → Prop)
    (old : ∀ v ∈ members, P v) (new : ∀ v ∈ committee, P v) :
    ∀ v ∈ committee.foldl (·.insert ·) members, P v := by
  apply Array.foldl_induction (fun _ set => ∀ v ∈ set, P v) old
  intro i set held v member
  rcases Std.TreeSet.mem_insert.mp member with same | previous
  · have same : committee[i] = v := Std.LawfulEqCmp.compare_eq_iff_eq.mp same
    exact same ▸ new _ (Array.getElem_mem i.isLt)
  · exact held v previous

/-- Every member of a successful slot committee is active at that slot in the head state. -/
private theorem active_of_slotCommittee {store : Store preset fork} {head : Root} {slot : Slot}
    {state : BeaconState preset fork} {members : Std.TreeSet ValidatorIndex}
    (early : fork < .glamsterdam) (held : store.blockState head = .ok state)
    (read : store.getSlotCommittee head slot = .ok members) :
    ∀ v ∈ members, isActiveAt state (computeEpochAtSlot preset slot) v.toNat = true := by
  simp only [Store.getSlotCommittee, held, bind, Except.bind] at read
  apply foldlM_ok_invariant
    (fun set => ∀ v ∈ set, isActiveAt state (computeEpochAtSlot preset slot) v.toNat = true)
    (fun set index next old step => ?_) (by simp) read
  obtain ⟨committee, computed, result⟩ := bind_ok_iff.mp step
  cases result
  apply members_array_insert _ old
  intro v member
  exact isActiveAt_eq_true_iff.mpr
    ((mem_getActiveValidatorIndices (BeaconState.registryWithinLimit_of_lt early state)).mp
      (mem_getActiveValidatorIndices_of_getBeaconCommittee (mapError_ok_iff.mp computed) member))

/-- A window member is active at a queried epoch of the held head state. -/
private theorem active_of_committeeWindow {store : Store preset fork} {head : Root}
    {first last : Slot} {state : BeaconState preset fork} {members : Std.TreeSet ValidatorIndex}
    (early : fork < .glamsterdam) (held : store.blockState head = .ok state)
    (read : store.getCommitteesBetweenSlots head first last = .ok members) :
    ∀ v ∈ members, ∃ epoch, isActiveAt state epoch v.toNat = true := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨_, _, folded⟩ := read
  intro v member
  rcases (mem_foldlM_committees_iff folded).mp member with empty | ⟨offset, _, set, read, inside⟩
  · simp at empty
  · exact ⟨_, active_of_slotCommittee early held read v inside⟩

private def NotSlashed (state : BeaconState preset fork) (v : ValidatorIndex) : Prop :=
  (state.validators.data[v.toNat]?.map (·.slashed)).getD false = false

/-- Lookahead preserves unslashedness without a committee, chain or honest-set premise. -/
private theorem notSlashed_lookahead {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) :
    ∀ v, NotSlashed after v ↔ NotSlashed state v := by
  intro v
  unfold NotSlashed
  rw [slashFlags_lookahead run v.toNat]

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Recent vote targets and the actual head have a common committee-preserving history. -/
private def VoteCommitteeCommonHistory (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
    ∀ (head : ForkChoiceNode) headState current v (attestation : Attestation preset fork)
      targetState,
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).blockState head.root = .ok headState →
    ((e.world k).state w).getCurrentStoreEpoch config = .ok current →
    attestation.data.target.epoch.toNat ≤ current.toNat →
    current.toNat ≤ attestation.data.target.epoch.toNat + 1 →
    ((e.world k).state w).VoteOrigin config v attestation →
    ((e.world k).state w).checkpointStates[attestation.data.target]? = some targetState →
    ∃ common : BeaconState preset fork,
      RunKept common headState ∧ RunKept common targetState ∧
      attestation.data.target.epoch.toNat ≤
        (getCurrentEpoch common).toNat + preset.MIN_SEED_LOOKAHEAD.toNat ∧
      attestation.data.target.epoch ≤ activityFixedEpoch common ∧
      (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        attestation.data.target.epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ∧
      (getCurrentEpoch targetState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        attestation.data.target.epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat

/-- A far target within the parent's two-epoch horizon is the actual receiver epoch. -/
private theorem common_history_of_far_vote {last n : Nat} {u v : ValidatorIndex}
    (history : VoteCommitteeCommonHistory (e := e) last) (honest : u ∈ J)
    (time : (e.world n).time ≤ last)
    {head : ForkChoiceNode} {headState targetState : BeaconState preset fork}
    {current : Epoch} {parent : BeaconBlock preset fork} {attestation : Attestation preset fork}
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (headFound : ((e.world n).state u).blockState head.root = .ok headState)
    (epochRead : ((e.world n).state u).getCurrentStoreEpoch config = .ok current)
    (horizon : current.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (far : (computeEpochAtSlot preset parent.slot).toNat + 1 < attestation.data.target.epoch.toNat)
    (origin : ((e.world n).state u).VoteOrigin config v attestation)
    (targetRead : ((e.world n).state u).checkpointState attestation.data.target = .ok targetState) :
    ∃ common, RunKept common targetState ∧ RunKept common headState ∧
      attestation.data.target.epoch ≤ activityFixedEpoch common := by
  obtain ⟨slot, slotRead, past⟩ := origin.past
  have currentEq : computeEpochAtSlot preset slot = current := by
    simpa [Store.getCurrentStoreEpoch, slotRead, bind, Except.bind, pure, Except.pure]
      using epochRead
  have targetLe : attestation.data.target.epoch.toNat ≤ current.toNat := by
    rw [origin.targetEpoch, ← currentEq]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt past))
  have same : current.toNat = attestation.data.target.epoch.toNat := by omega
  obtain ⟨common, headRun, targetRun, _, fixed, _, _⟩ := history u honest n time
    head headState current v attestation targetState headRead headFound epochRead targetLe
    (by omega) origin (Store.checkpointState_ok_iff.mp targetRead)
  exact ⟨common, targetRun, headRun, fixed⟩

/-- Held-state finality supplies the source bound at the store's realized checkpoint.

The two ancestry reads remain separate inputs; this does not bound cached-output finality. -/
private theorem registry_of_honest_block {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH) (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    {boundaryBase source base cached : BeaconState preset fork}
    {root sourceRoot : Root} {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    (boundaryBaseFound : ((e.world n).state u).blockStates[
      ((e.world n).state u).finalizedCheckpoint.root]? = some boundaryBase)
    (startOk : computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch =
      .ok start)
    (walk : ((e.world n).state u).getCheckpointBlock root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (bound : start ≤ max block.slot target)
    (baseFound : ((e.world n).state u).blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceWalk : ((e.world n).state u).getCheckpointBlock sourceRoot
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    (sourceBlockFound : ((e.world n).state u).blocks[sourceRoot]? = some sourceBlock)
    (sourceFound : ((e.world n).state u).blockStates[sourceRoot]? = some source)
    (sourceBound : start ≤ sourceBlock.slot)
    (finite : ((e.world n).state u).finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH) :
    ∀ epoch position, isActiveAt source epoch position = true →
      ∃ validator, cached.validators.data[position]? = some validator := by
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  have finalized := (reached.reachable.ordered_finalized anchorInvariant).2 sourceFound
  have identity : lookaheadState config checks source source.slot = .ok source := by
    simp [lookaheadState, pure, Except.pure]
  have sourceStart : start ≤ max sourceBlock.slot source.slot := by
    rw [UInt64.le_iff_toNat_le, toNat_max]
    exact Nat.le_trans (UInt64.le_iff_toNat_le.mp sourceBound) (Nat.le_max_left _ _)
  exact registry_of_checkpointPrefix early anchorSlot reached anchorInvariant positive
    walk found startOk bound baseFound boundaryBaseFound advanced identity sourceWalk
    sourceBlockFound sourceStart sourceFound finalized finite

/-- An invariant state's three old checkpoints are below the far-future epoch. -/
private theorem oldCheckpoints_finite {state : BeaconState preset fork}
    (holds : Invariant state) :
    state.currentJustifiedCheckpoint.epoch < FAR_FUTURE_EPOCH ∧
      state.previousJustifiedCheckpoint.epoch < FAR_FUTURE_EPOCH ∧
      state.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH := by
  have settled := UInt64.le_iff_toNat_le.mp holds.settled
  rw [getPreviousEpoch_toNat] at settled
  have current := (getCurrentEpoch state).toNat_lt
  have previous := UInt64.le_iff_toNat_le.mp holds.ordered.2
  have finalized := UInt64.le_iff_toNat_le.mp holds.ordered.1
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  simp only [UInt64.lt_iff_toNat_lt, far]
  omega

/-- Exact checkpoint origins preserve finite finality from a finite anchor epoch. -/
private theorem finalized_finite_of_anchor {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (anchorFinite : getCurrentEpoch anchorState < FAR_FUTURE_EPOCH) :
    store.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH := by
  rcases reached.finalized_origins _ (.inl rfl) with
    ⟨_, _, same⟩ | ⟨_, state, held, same⟩ | ⟨_, state, pulled, held, run, same⟩
  · simpa only [same] using anchorFinite
  · simpa only [same] using (oldCheckpoints_finite ((reached.ordered sound).2 held)).2.2
  · rw [same]
    have old := oldCheckpoints_finite ((reached.ordered sound).2 held)
    rcases processJustificationAndFinalization_ok run with rfl | ⟨_, _, _, weighed⟩
    · exact old.2.2
    · rcases (weighJustificationAndFinalization_checkpoints weighed).2.2.1 with same | same | same
      · exact same ▸ old.2.2
      · exact same ▸ old.2.1
      · exact same ▸ old.1

/-- A held head supplies registry lookups for the receiver's checked older-window maximum.

No cached target-state finality bound is used in this construction. -/
private theorem receiver_oldMaximum_of_honest_block {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH) (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    {boundaryBase source base cached : BeaconState preset fork}
    {root head : Root} {block headBlock : BeaconBlock preset fork} {start target : Slot}
    {caller : Store preset fork} {callerHead : Root} {callerState : BeaconState preset fork}
    {callerNode : ValidatorIndex} {callerTime : Nat} (callerHonest : callerNode ∈ J)
    (callerOrigin : caller = (e.world callerTime).state callerNode)
    {first oldLast last : Slot} {maximum : Gwei} {window : Std.TreeSet ValidatorIndex}
    (boundaryBaseFound : ((e.world n).state u).blockStates[
      ((e.world n).state u).finalizedCheckpoint.root]? = some boundaryBase)
    (startOk : computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch =
      .ok start)
    (walk : ((e.world n).state u).getCheckpointBlock root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (bound : start ≤ max block.slot target)
    (baseFound : ((e.world n).state u).blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (headWalk : ((e.world n).state u).getCheckpointBlock head
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    (headBlockFound : ((e.world n).state u).blocks[head]? = some headBlock)
    (headStateFound : ((e.world n).state u).blockStates[head]? = some source)
    (headBound : start ≤ headBlock.slot)
    {parent : BeaconBlock preset fork} {parentRoot : Root}
    (callerParentFound : caller.blocks[parentRoot]? = some parent)
    (parentSafe : ((e.world n).state u).isAncestor ⟨head, .pending⟩
      ⟨parentRoot, .pending⟩ = .ok true)
    (parentNext : addChecked parent.slot 1 = .ok first)
    (anchorParentAbsent : ((e.world n).state u).blocks[anchorBlock.parentRoot]? = none)
    (read : caller.computeCommitteeWeightBetweenSlots callerHead callerState first oldLast =
      .ok maximum)
    (windowOk : ((e.world n).state u).getCommitteesBetweenSlots head first last = .ok window)
    (before : oldLast ≤ last)
    (stakeBound : stake (fun v => balanceAt cached v.toNat)
      (getActiveValidatorIndices cached (getCurrentEpoch cached)).toFinset ≤ 2 * 10 ^ 17) :
    (∃ result, ((e.world n).state u).computeCommitteeWeightBetweenSlots head cached first oldLast =
      .ok result) ∨ ∃ leftBlock rightBlock,
      Store.findBlockCollision caller ((e.world n).state u) [parentRoot] =
        some (parentRoot, leftBlock, rightBlock) ∧ leftBlock ≠ rightBlock ∧
      Serialization.Ssz.SszType.hashTreeRoot leftBlock = .ok parentRoot ∧
      Serialization.Ssz.SszType.hashTreeRoot rightBlock = .ok parentRoot := by
  have reachableAt : ∀ w ∈ J, ∀ k,
      Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    intro w member k
    exact e.reachable
      (fun v hv => (anchored v hv) ▸ Store.Reachable.anchor anchorStore) k w member
  have parentRead := parentSafe
  unfold Store.isAncestor at parentRead
  obtain ⟨receiverParent, parentOk, _⟩ := bind_ok_iff.mp parentRead
  have receiverParentFound := Store.block_ok_iff.mp parentOk
  by_cases same : parent = receiverParent
  swap
  · have searched : Store.findBlockCollision caller ((e.world n).state u) [parentRoot] =
        some (parentRoot, parent, receiverParent) := by
      simp [Store.findBlockCollision, callerParentFound, receiverParentFound, same]
    have valid := Store.findBlockCollision_valid
      (callerOrigin.symm ▸ reachableAt callerNode callerHonest callerTime)
      (reachableAt u honest n) searched
    exact .inr ⟨parent, receiverParent, searched, valid⟩
  subst receiverParent
  left
  have parentFound := receiverParentFound
  have reached := reachableAt u honest n
  obtain ⟨_, _, anchorFound⟩ := reached.anchor_known
  have anchorLe := reached.orphans_le (UInt64.le_of_eq anchorSlot)
    anchorFound anchorParentAbsent parentFound
  have anchorFinite : getCurrentEpoch anchorState < FAR_FUTURE_EPOCH := by
    have step := (addChecked_ok_iff.mp parentNext).1
    have le := UInt64.le_iff_toNat_le.mp anchorLe
    have epoch := getCurrentEpoch_toNat_le_slot anchorState
    rw [anchorSlot] at le
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    rw [UInt64.lt_iff_toNat_lt, far]
    have one : (1 : UInt64).toNat = 1 := rfl
    rw [one] at step
    omega
  have finite := finalized_finite_of_anchor reached anchorInvariant anchorFinite
  have inside := registry_of_honest_block anchorStore anchored anchorInvariant
    (UInt64.le_of_eq anchorSlot)
    positive early honest boundaryBaseFound startOk walk found bound baseFound advanced
    headWalk headBlockFound headStateFound headBound finite
  obtain ⟨total, totalOk⟩ := activeTotal_exists
    (BeaconState.registryWithinLimit_of_lt early cached) (by omega)
  apply receiver_oldMaximum read windowOk before totalOk
  intro v member
  obtain ⟨epoch, active⟩ := active_of_committeeWindow early
    (Store.blockState_ok_iff.mpr headStateFound) windowOk v member
  obtain ⟨validator, found⟩ := inside epoch v.toNat active
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- A near-epoch cache read has bounded finality even when its target precedes an empty slot. -/
private theorem checkpoint_finalized_le_of_near_epoch {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    {checkpoint : Checkpoint} {state : BeaconState preset fork} {boundary : Epoch}
    (read : ((e.world n).state u).checkpointState checkpoint = .ok state)
    (storeBound : ((e.world n).state u).finalizedCheckpoint.epoch ≤ boundary)
    (near : checkpoint.epoch.toNat ≤ boundary.toNat + 1) :
    state.finalizedCheckpoint.epoch ≤ boundary := by
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  obtain ⟨base, start, held, startOk, advanced⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp read)
  unfold lookaheadState at advanced
  split at advanced
  · have slotsOk := mapError_ok_iff.mp advanced
    have inv := (processSlots_invariant
      ((reached.reachable.ordered anchorInvariant).2 held) slotsOk).1
    have epoch : getCurrentEpoch state = checkpoint.epoch := by
      change computeEpochAtSlot preset state.slot = checkpoint.epoch
      rw [(processSlots_slot slotsOk).2]
      exact computeEpochAtSlot_computeStartSlotAtEpoch positive startOk
    have upper := UInt64.le_trans (Store.finalized_le_currentJustified inv.ordered) inv.settled
    rw [UInt64.le_iff_toNat_le, getPreviousEpoch_toNat, epoch] at upper
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  · cases advanced
    exact UInt64.le_trans
      ((reached.reachable.ordered_finalized anchorInvariant).2 held) storeBound

/-- An actual descendant bounds the finalized epoch of its cached checkpoint prefix. -/
private theorem checkpoint_finalized_le_of_descendant {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    {checkpoint : Checkpoint} {state descendant : BeaconState preset fork}
    {root : Root} {block : BeaconBlock preset fork} {start : Slot}
    (read : ((e.world n).state u).checkpointState checkpoint = .ok state)
    (walk : ((e.world n).state u).getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (atOrAfter : start ≤ block.slot)
    (held : ((e.world n).state u).blockStates[root]? = some descendant) :
    state.finalizedCheckpoint.epoch ≤ ((e.world n).state u).finalizedCheckpoint.epoch := by
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  -- The existing block traversal composes invariant-indexed finality monotonicity.
  let R := fun (s t : BeaconState preset fork) =>
    Invariant s → Invariant t ∧ s.finalizedCheckpoint.epoch ≤ t.finalizedCheckpoint.epoch
  have trans : ∀ {s m t}, R s m → R m t → R s t := by
    intro s m t first second inv
    obtain ⟨middleInv, firstLe⟩ := first inv
    obtain ⟨lastInv, secondLe⟩ := second middleInv
    exact ⟨lastInv, UInt64.le_trans firstLe secondLe⟩
  have related := reached.relation_of_checkpointState R
    (fun _ inv => ⟨inv, UInt64.le_refl _⟩) trans
    (fun ok inv => stateTransition_invariant inv ok)
    (fun slotsOk bound ok => relation_of_processSlots_of_stateTransition R trans
      (fun slots inv => processSlots_invariant inv slots)
      (fun computed inv => by
        have frame := frame_processBlock computed
        refine ⟨frame.invariant inv, ?_⟩
        rw [frame.finalized]
        exact UInt64.le_refl _)
      slotsOk bound ok)
    anchorSlot walk found startOk atOrAfter (Store.checkpointState_ok_iff.mp read) held
  have inv := reached.reachable.checkpointStatesHold anchorInvariant
    (Store.checkpointState_ok_iff.mp read)
  exact UInt64.le_trans (related inv).2
    ((reached.reachable.ordered_finalized anchorInvariant).2 held)

/-- Honest checkpoint origins supply the actual source prefix, including an older held block. -/
private theorem registry_of_honest_checkpoint {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    {checkpoint targetCheckpoint : Checkpoint}
    {boundaryBase targetState base cached : BeaconState preset fork}
    {root : Root} {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    (targetRead : ((e.world n).state u).checkpointState targetCheckpoint = .ok targetState)
    (boundaryBaseFound : ((e.world n).state u).blockStates[checkpoint.root]? = some boundaryBase)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (walk : ((e.world n).state u).getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (bound : start ≤ max block.slot target)
    (baseFound : ((e.world n).state u).blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceWalk : ((e.world n).state u).getCheckpointBlock targetCheckpoint.root checkpoint.epoch =
      .ok checkpoint.root)
    (sourceBlockFound : ((e.world n).state u).blocks[targetCheckpoint.root]? = some sourceBlock)
    (sourceEpoch : checkpoint.epoch ≤ targetCheckpoint.epoch)
    (finalized : targetState.finalizedCheckpoint.epoch ≤ checkpoint.epoch ∨
      (((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch ∧
        targetCheckpoint.epoch.toNat ≤ checkpoint.epoch.toNat + 1) ∨
      ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch ∧
        ∃ root block start descendant,
          ((e.world n).state u).getCheckpointBlock root targetCheckpoint.epoch =
            .ok targetCheckpoint.root ∧
          ((e.world n).state u).blocks[root]? = some block ∧
          computeStartSlotAtEpoch preset targetCheckpoint.epoch = .ok start ∧
          start ≤ block.slot ∧
          ((e.world n).state u).blockStates[root]? = some descendant)
    (finite : checkpoint.epoch < FAR_FUTURE_EPOCH) :
    ∀ epoch position, isActiveAt targetState epoch position = true →
      ∃ validator, cached.validators.data[position]? = some validator := by
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  obtain ⟨source, sourceStart, sourceFound, sourceStartOk, sourceRun⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp targetRead)
  have sourceBound : start ≤ max sourceBlock.slot sourceStart := by
    have ordered := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (UInt64.le_iff_toNat_le.mp sourceEpoch)
    rw [← (computeStartSlotAtEpoch_ok_iff.mp startOk).2,
      ← (computeStartSlotAtEpoch_ok_iff.mp sourceStartOk).2] at ordered
    rw [UInt64.le_iff_toNat_le, toNat_max]
    exact Nat.le_trans ordered (Nat.le_max_right _ _)
  have targetFinalized : targetState.finalizedCheckpoint.epoch ≤ checkpoint.epoch := by
    rcases finalized with direct | ⟨storeBound, near⟩ | ⟨storeBound, root, block, start,
      descendant, walk, found, startOk, atOrAfter, held⟩
    · exact direct
    · exact checkpoint_finalized_le_of_near_epoch anchorStore anchored anchorInvariant positive
        honest targetRead storeBound near
    · exact UInt64.le_trans
        (checkpoint_finalized_le_of_descendant anchorStore anchored anchorInvariant anchorSlot
          honest targetRead walk found startOk atOrAfter held) storeBound
  exact registry_of_checkpointPrefix early anchorSlot reached anchorInvariant positive
    walk found startOk bound baseFound boundaryBaseFound advanced sourceRun sourceWalk
    sourceBlockFound sourceBound sourceFound targetFinalized finite

/-- An actual lookahead preserves the run relation in both slot branches. -/
private theorem runKept_lookahead {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) : RunKept state after := by
  unfold lookaheadState at run
  split at run
  · exact runKept_processSlots (mapError_ok_iff.mp run)
  · cases run
    exact RunKept.refl _

/-- A growing registry retains every index read in the earlier state. -/
private theorem registry_of_runKept {state after : BeaconState preset fork}
    (run : RunKept state after) {epoch : Epoch} {position : Nat}
    (active : isActiveAt state epoch position = true) :
    ∃ validator, after.validators.data[position]? = some validator := by
  obtain ⟨validator, held, _⟩ := isActiveAt_eq_true_iff.mp active
  have inside := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp held).1 run.grows
  exact ⟨after.validators.data[position], Array.getElem?_eq_getElem inside⟩

/-- Each accepted signer supplies activity in its own actual cached target state.

The receiver still filters at its own epoch; no activity is transported backwards. -/
private theorem filteredTotal_of_voteOrigins {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    {checkpoint : Checkpoint} {attestation : ValidatorIndex → Attestation preset fork}
    {targetState : ValidatorIndex → BeaconState preset fork}
    {boundaryBase base cached : BeaconState preset fork}
    {sourceBlock : ValidatorIndex → BeaconBlock preset fork}
    {root : Root} {block : BeaconBlock preset fork} {start target : Slot}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (targetRead : ∀ v ∈ participants,
      ((e.world n).state u).checkpointState (attestation v).data.target = .ok (targetState v))
    (origins : ∀ v ∈ participants,
      ((e.world n).state u).VoteOrigin config v (attestation v))
    (boundaryBaseFound : ((e.world n).state u).blockStates[checkpoint.root]? = some boundaryBase)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (walk : ((e.world n).state u).getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (bound : start ≤ max block.slot target)
    (baseFound : ((e.world n).state u).blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceWalk : ∀ v ∈ participants,
      ((e.world n).state u).getCheckpointBlock (attestation v).data.target.root
      checkpoint.epoch = .ok checkpoint.root)
    (sourceBlockFound : ∀ v ∈ participants,
      ((e.world n).state u).blocks[(attestation v).data.target.root]? = some (sourceBlock v))
    (sourceEpoch : ∀ v ∈ participants, checkpoint.epoch ≤ (attestation v).data.target.epoch)
    (finalized : ∀ v ∈ participants,
      ((targetState v).finalizedCheckpoint.epoch ≤ checkpoint.epoch ∨
        (((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch ∧
          (attestation v).data.target.epoch.toNat ≤ checkpoint.epoch.toNat + 1) ∨
        ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch ∧
          ∃ root block start descendant,
            ((e.world n).state u).getCheckpointBlock root (attestation v).data.target.epoch =
              .ok (attestation v).data.target.root ∧
            ((e.world n).state u).blocks[root]? = some block ∧
            computeStartSlotAtEpoch preset (attestation v).data.target.epoch = .ok start ∧
            start ≤ block.slot ∧
            ((e.world n).state u).blockStates[root]? = some descendant) ∨
        ∃ headState headRoot headBlock,
          ((∃ common, RunKept common (targetState v) ∧ RunKept common headState ∧
            (attestation v).data.target.epoch ≤ activityFixedEpoch common) ∨
            ∃ last head current, ∃ parent : BeaconBlock preset fork,
              VoteCommitteeCommonHistory (e := e) last ∧ (e.world n).time ≤ last ∧
              ((e.world n).state u).getHead config = .ok head ∧ head.root = headRoot ∧
              ((e.world n).state u).getCurrentStoreEpoch config = .ok current ∧
              current.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2 ∧
              (computeEpochAtSlot preset parent.slot).toNat + 1 <
                (attestation v).data.target.epoch.toNat) ∧
          ((e.world n).state u).blockStates[headRoot]? = some headState ∧
          (headRoot = root ∨ headRoot = checkpoint.root ∨
            ((e.world n).state u).blocks[headRoot]? = some headBlock ∧
            ((e.world n).state u).getCheckpointBlock headRoot checkpoint.epoch =
              .ok checkpoint.root ∧
            ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch))
    (finite : checkpoint.epoch < FAR_FUTURE_EPOCH)
    (read : getTotalActiveBalance cached = .ok total) :
    ∃ selected result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt cached index) (getCurrentEpoch cached)) =
        .ok selected ∧ getTotalBalance cached selected = .ok result := by
  apply filteredTotal_exists read
  intro v member
  have active : isActiveAt (targetState v) (computeEpochAtSlot preset (attestation v).data.slot)
      v.toNat = true := by
    obtain ⟨state, indexed, stored, _, computed, listed⟩ := (origins v member).committees
    have same : state = targetState v := by
      have targetStored := Store.checkpointState_ok_iff.mp (targetRead v member)
      rw [stored] at targetStored
      exact Option.some.inj targetStored
    subst state
    obtain ⟨attesters, attestersOk, indices⟩ :=
      getAttestingIndices_of_getIndexedAttestation computed
    have attester : v ∈ attesters := by simpa [indices] using listed
    exact isActiveAt_eq_true_iff.mpr
      ((mem_getActiveValidatorIndices
        (BeaconState.registryWithinLimit_of_lt early (targetState v))).mp
        (mem_getActiveValidatorIndices_of_getAttestingIndices attestersOk attester))
  have position : ∃ validator, cached.validators.data[v.toNat]? = some validator := by
    rcases finalized v member with cacheBound | ⟨headState, headRoot, headBlock,
      commonSource, headFound, headPath⟩
    · exact registry_of_honest_checkpoint anchorStore anchored anchorInvariant anchorSlot
        positive early honest (targetRead v member) boundaryBaseFound startOk walk found
        bound baseFound advanced (sourceWalk v member) (sourceBlockFound v member)
        (sourceEpoch v member) cacheBound finite _ v.toNat active
    · -- Common-history activity identifies a held source at the same queried epoch.
      have commonWitness : ∃ common, RunKept common (targetState v) ∧
          RunKept common headState ∧
          (attestation v).data.target.epoch ≤ activityFixedEpoch common := by
        rcases commonSource with ready | ⟨last, head, current, parent, history, time,
          headRead, rootEq, epochRead, horizon, far⟩
        · exact ready
        · exact common_history_of_far_vote history honest time headRead
            (Store.blockState_ok_iff.mpr (rootEq ▸ headFound)) epochRead horizon far
            (origins v member) (targetRead v member)
      obtain ⟨common, toTarget, toHead, fixed⟩ := commonWitness
      rw [← (origins v member).targetEpoch, toTarget.active _ fixed v.toNat,
        ← toHead.active _ fixed v.toNat] at active
      have atBoundaryRange (same : headRoot = checkpoint.root) :
          ∃ validator, cached.validators.data[v.toNat]? = some validator := by
        rw [same, boundaryBaseFound, Option.some.injEq] at headFound
        subst headState
        have reached := e.forwardReachableWith
          (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
          n u honest
        obtain ⟨boundary, prefixOk, run⟩ := relation_of_checkpoint_lookahead RunKept RunKept.refl
          (fun one two => one.trans two) (fun ok => runKept_stateTransition ok)
          (fun slots bound ok => runKept_of_processSlots_of_stateTransition slots bound ok)
          (fun ok => runKept_processSlots ok) anchorSlot reached walk found startOk bound
          boundaryBaseFound baseFound advanced
        exact registry_of_runKept ((runKept_lookahead prefixOk).trans run) active
      rcases headPath with same | atBoundary | ⟨headBlockFound, headWalk, storeBound⟩
      · -- A fallback head at the cache base needs only the actual lookahead's registry growth.
        rw [same, baseFound, Option.some.injEq] at headFound
        subst headState
        exact registry_of_runKept (runKept_lookahead advanced) active
      · exact atBoundaryRange atBoundary
      by_cases headBound : start ≤ headBlock.slot
      swap
      · -- A checkpoint walk below the boundary stops at the held head itself.
        have same : headRoot = checkpoint.root := by
          simpa [Store.getCheckpointBlock, startOk, Except.mapError,
            Store.getAncestor_of_le (node := ⟨headRoot, .pending⟩) headBlockFound
              (UInt64.le_of_lt (UInt64.not_le.mp headBound)), bind, Except.bind,
            pure, Except.pure] using headWalk
        exact atBoundaryRange same
      have reached := e.forwardReachableWith
        (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
        n u honest
      have heldBound := UInt64.le_trans
        ((reached.reachable.ordered_finalized anchorInvariant).2 headFound) storeBound
      have identity : lookaheadState config checks headState headState.slot = .ok headState := by
        simp [lookaheadState, pure, Except.pure]
      have sourceBound : start ≤ max headBlock.slot headState.slot := by
        rw [UInt64.le_iff_toNat_le, toNat_max]
        exact Nat.le_trans (UInt64.le_iff_toNat_le.mp headBound) (Nat.le_max_left _ _)
      exact registry_of_checkpointPrefix early anchorSlot reached anchorInvariant positive
        walk found startOk bound baseFound boundaryBaseFound advanced identity headWalk
        headBlockFound sourceBound headFound heldBound finite _ v.toNat active
  obtain ⟨validator, found⟩ := position
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- Held-state flags suffice for a cached checkpoint through its fixed-check lookahead origin. -/
private theorem notSlashed_checkpointState {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u : ValidatorIndex} (honest : u ∈ J) {n : ℕ}
    (flags : ∀ (root : Root) (base : BeaconState preset fork),
      ((e.world n).state u).blockStates[root]? = some base →
      ∀ v ∈ J, NotSlashed base v)
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (read : ((e.world n).state u).checkpointState checkpoint = .ok state) :
    ∀ v ∈ J, NotSlashed state v := by
  obtain ⟨base, slot, stored, _, advanced⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp read)
  intro v member
  exact (notSlashed_lookahead advanced v).mpr (flags checkpoint.root base stored v member)

/-- Honest signatures for one target epoch carry the same attestation data. -/
private theorem data_eq_of_signed_of_target_epoch (slots : 0 < config.SLOT_DURATION_MS)
    {n k : ℕ} {first second : Message preset fork} (sentFirst : first ∈ (e.world n).sent)
    (sentSecond : second ∈ (e.world k).sent) {v : ValidatorIndex} {data other : AttestationData}
    (signedFirst : (v, data) ∈ statements config checks anchorState anchorBlock first)
    (signedSecond : (v, other) ∈ statements config checks anchorState anchorBlock second)
    (honest : v ∈ J) (epoch : data.target.epoch = other.target.epoch) : data = other := by
  have nonslashable := e.isSlashableAttestationData_honest slots (max n k) honest
    (e.monotone_sent (Nat.le_max_left n k) sentFirst)
    (e.monotone_sent (Nat.le_max_right n k) sentSecond) signedFirst signedSecond
  by_contra different
  simp [isSlashableAttestationData, different, epoch] at nonslashable

/-- Equal-rank honest latest votes agree before Gloas, even across different stores. -/
private theorem latest_eq_of_rank_eq (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J)
    {n k : ℕ} {first second : LatestMessage fork}
    (firstOk : ((e.world n).state u).latestMessages[v]? = some first)
    (secondOk : ((e.world k).state w).latestMessages[v]? = some second)
    (rank : first.rank = second.rank) : first = second := by
  obtain ⟨a, firstMessage, seenFirst, rfl, signedFirst, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller firstOk
  obtain ⟨b, secondMessage, seenSecond, rfl, signedSecond, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored receiver secondOk
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have epoch : a.data.target.epoch = b.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  have same := data_eq_of_signed_of_target_epoch slots
    (e.view_subset_sent n u seenFirst) (e.view_subset_sent k w seenSecond)
    signedFirst signedSecond honest epoch
  simp only [LatestMessage.ofAttestation, same]

/-- A latest vote at or above a signed vote's rank cannot come from an older slot. -/
private theorem latest_slot_floor_of_signed_rank
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {v : ValidatorIndex} (honest : v ∈ J) {n k : ℕ}
    {message other : Message preset fork}
    (sent : message ∈ (e.world n).sent) (sentOther : other ∈ (e.world k).sent)
    {data : AttestationData} {attestation : Attestation preset fork}
    (signed : (v, data) ∈ statements config checks anchorState anchorBlock message)
    (signedOther : (v, attestation.data) ∈
      statements config checks anchorState anchorBlock other)
    {store : Store preset fork} (origin : store.VoteOrigin config v attestation)
    (epoch : data.target.epoch = computeEpochAtSlot preset data.slot)
    (rank : (LatestMessage.ofAttestation (fork := fork) attestation).rank ≥ data.target.epoch)
    {slot : Slot} (floor : slot ≤ data.slot) : slot ≤ attestation.data.slot := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have targetLe : data.target.epoch ≤ attestation.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  by_cases same : data.target.epoch = attestation.data.target.epoch
  · have dataEq := data_eq_of_signed_of_target_epoch slots sent sentOther
      signed signedOther honest same
    exact dataEq ▸ floor
  · have targetLt := UInt64.lt_of_le_of_ne targetLe same
    have slotLe : data.slot ≤ attestation.data.slot := by
      by_contra h
      have reversed := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt (UInt64.not_le.mp h)))
      rw [epoch, origin.targetEpoch] at targetLt
      have strict := UInt64.lt_iff_toNat_lt.mp targetLt
      simp only [computeEpochAtSlot, UInt64.toNat_div] at strict
      omega
    exact UInt64.le_trans floor slotLe

end Models.Network

end EthLib.Consensus
