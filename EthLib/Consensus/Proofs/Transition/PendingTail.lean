module

public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.RunKept

/-!
# Proofs: registry entries past a boundary stay pending through slots and blocks

A registry entry is pending at an epoch when it becomes eligible for activation only later.

It also has no activation epoch yet.

Suppose every entry from some position on is pending at an epoch at or before the current one.

A block keeps that property.

An epoch keeps it when the finalized epoch after it is at most the given epoch.

The activation queue admits only entries that were eligible by the finalized epoch.

A pending entry is never active, so every active position lies below the boundary position.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- Activity at any queried epoch requires a finite activation epoch. -/
private theorem activationEpoch_ne_farFuture_of_isActiveAt {state : BeaconState preset fork}
    {epoch : Epoch} {position : Nat} (active : isActiveAt state epoch position = true) :
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

/-- Each registry entry from the position on becomes eligible only after the epoch.

None of those entries has an activation epoch. -/
def PendingTail (count : Nat) (epoch : Epoch) (state : BeaconState preset fork) : Prop :=
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
    simp only [UInt64.toNat_one] at sum
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
      simp only [UInt64.toNat_one] at sum
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
  rcases applyPendingDeposit_cases run with rfl | ⟨_, run⟩ | ⟨_, run⟩
  · exact tail
  · exact pendingTail_of_validators (congrArg (·.data) (increaseBalance_validators run)) tail
  · exact pendingTail_addValidator run finite tail

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
  rcases withdrawalRequest_cases run with rfl | ⟨_, _, _, exited⟩ | ⟨_, _, _, _, withdrawn⟩
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
  obtain ⟨_, _, _, written, _, _, _, set, _, rfl⟩ := queueConsolidation_steps run
  rw [setValidator_eq_setValidatorAt] at set
  exact pendingTail_of_validators (state := written) rfl
    (pendingTail_setValidatorAt (old := source)
      (by rw [← getValidator_eq_getValidatorAt]; exact getValidator_eq_ok_iff.mpr found) set rfl
      rfl (pendingTail_of_validators rfl tail))

/-- Every successful consolidation request preserves the pending activation suffix. -/
private theorem pendingTail_processConsolidationRequest {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest} {count : Nat} {epoch : Epoch}
    (run : processConsolidationRequest config state electra request = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  rcases consolidationRequest_cases run with rfl | ⟨_, _, _, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact tail
  · exact pendingTail_switchToCompoundingValidator switched tail
  · exact pendingTail_queueConsolidation accepted.sourceAt queued tail

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
  obtain ⟨validator, found, finite⟩ := activationEpoch_ne_farFuture_of_isActiveAt active
  by_contra outside
  exact finite (tail position validator (Nat.le_of_not_gt outside) found).2

/-- A registry at least as long as the boundary position holds each active position.

The position may be active at any epoch. -/
theorem active_registry_of_pendingTail {state cached : BeaconState preset fork}
    {epoch boundary : Epoch} {count : Nat}
    (tail : PendingTail count boundary state) (contains : count ≤ cached.validators.data.size)
    {position : Nat} (active : isActiveAt state epoch position = true) :
    ∃ validator, cached.validators.data[position]? = some validator := by
  have inside := Nat.lt_of_lt_of_le (active_before_pendingTail tail active) contains
  exact ⟨cached.validators.data[position], Array.getElem?_eq_getElem inside⟩

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

/-- The operations of a block preserve the pending suffix. -/
private theorem pendingTail_processOperations {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {parentSlot : Slot} {boundary : Epoch} {count : Nat}
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
      (fun ok tail => by rw [processPayloadAttestation_eq ok]; exact tail) run
  have proposerTail := foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ held ok => pendingTail_processProposerSlashing ok held) tail proposersOk
  have slashingTail := foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ held ok => pendingTail_processAttesterSlashing ok held) proposerTail slashingsOk
  exact rest (foldlM_ok_invariant (PendingTail count boundary)
    (fun _ _ _ held ok => pendingTail_of_validators
      (congrArg (·.data) (processAttestation_registry ok).1) held) slashingTail attestedOk)

/-- A block transports its input pending tail.

From Gloas the requests of the parent payload run first.

The rest of the execution prefix and the sync aggregate keep the registry.

Boundary applicability remains an input. -/
private theorem pendingTail_processBlock {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {source after : BeaconState preset fork}
    {block : BeaconBlock preset fork} {boundary : Epoch} {count : Nat}
    (run : processBlock config checks engine source block = .ok after)
    (finite : boundary < FAR_FUTURE_EPOCH) (tail : PendingTail count boundary source) :
    PendingTail count boundary after := by
  obtain ⟨input, operated, started, operations, _, synced⟩ := processBlock_operationsInput run
  have inputTail : PendingTail count boundary input :=
    started.step_of (fun s t => PendingTail count boundary s → PendingTail count boundary t)
      (fun _ tail => tail) (fun one two tail => two (one tail))
      (fun _ ok => processParentExecutionPayload_step_of
        (fun s t => PendingTail count boundary s → PendingTail count boundary t)
        (fun _ tail => tail) (fun one two tail => two (one tail))
        (fun _ same tail => pendingTail_of_validators (congrArg (·.data) same) tail)
        (fun ok tail => pendingTail_processWithdrawalRequest ok tail)
        (fun ok tail => pendingTail_processConsolidationRequest ok tail) ok)
      (fun headed tail => by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
        exact tail)
      (fun _ executed tail =>
        pendingTail_of_validators (congrArg (·.data) (processBlockExecution_validators executed))
          tail)
      (fun revealed tail => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        exact tail)
      (fun _ voted tail => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        exact pendingTail_of_validators (by rw [← rest]) tail) tail
  have same : after.validators = operated.validators := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      rfl
    · cases synced; rfl
  exact pendingTail_of_validators (congrArg (·.data) same)
    (pendingTail_processOperations operations finite inputTail)

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

/-- Reduce a slot step to its cache, optional epoch and final slot write. -/
private theorem advanceSlot_transport {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork} (P : BeaconState preset fork → Prop)
    (run : advanceSlot config checks source = .ok after)
    (finish : ∀ next cached epoched, processSlot source = .ok cached →
      after = { epoched with slot := next } →
      (processEpoch config checks cached = .ok epoched ∨ epoched = cached) → P after) :
    P after := by
  obtain ⟨next, cached, epoched, _, cacheOk, epochOk, result⟩ := advanceSlot_ok run
  apply finish next cached epoched cacheOk result
  unfold epochIfLast at epochOk
  split at epochOk
  · exact .inl epochOk
  · exact .inr (Except.ok.inj epochOk).symm

/-- The actual cache, optional epoch and slot increment preserve the pending suffix. -/
private theorem pendingTail_advanceSlot {config : Config} {checks : SignatureChecks}
    {source after : BeaconState preset fork}
    {boundEpoch : Epoch} {count : Nat}
    (run : advanceSlot config checks source = .ok after)
    (boundary : boundEpoch ≤ getCurrentEpoch source)
    (finalized : after.finalizedCheckpoint.epoch ≤ boundEpoch)
    (finite : boundEpoch < FAR_FUTURE_EPOCH) (tail : PendingTail count boundEpoch source) :
    PendingTail count boundEpoch after := by
  apply advanceSlot_transport (PendingTail count boundEpoch) run
  intro next cached epoched cacheOk result epochStep
  subst after
  obtain ⟨_, _, _, _, cacheEq⟩ := processSlot_ok cacheOk
  have cachedTail : PendingTail count boundEpoch cached :=
    pendingTail_of_validators (by rw [cacheEq]) tail
  have epochedTail : PendingTail count boundEpoch epoched := by
    rcases epochStep with epochOk | rfl
    · apply pendingTail_processEpoch epochOk ?_ finalized finite cachedTail
      simpa only [getCurrentEpoch, cacheEq] using boundary
    · exact cachedTail
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

The invariant and the finalized bound are inputs. -/
private theorem pendingTail_stateTransition {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {source after : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validate : Bool}
    {boundary : Epoch} {count : Nat} (holds : Invariant source)
    (run : stateTransition config checks engine source signed validate = .ok after)
    (low : boundary ≤ getCurrentEpoch source)
    (finalized : after.finalizedCheckpoint.epoch ≤ boundary)
    (finite : boundary < FAR_FUTURE_EPOCH) (tail : PendingTail count boundary source) :
    PendingTail count boundary after := by
  obtain ⟨advanced, slots, _, _, block, _⟩ := stateTransition_ok run
  have advancedFinalized : advanced.finalizedCheckpoint.epoch ≤ boundary := by
    simpa only [(frame_processBlock block).finalized] using finalized
  exact pendingTail_processBlock block finite
    (pendingTail_processSlots holds slots low advancedFinalized finite tail)

/-- The second state follows the first without moving the current epoch back.

From an invariant state, the second is invariant and has no lower finalized epoch.

It also keeps each pending tail at an epoch at most the current epoch of the first.

That epoch must be at least the finalized epoch of the second. -/
def PendingTailRun (count : Nat) (epoch : Epoch)
    (s t : BeaconState preset fork) : Prop :=
    getCurrentEpoch s ≤ getCurrentEpoch t ∧
      (Invariant s → Invariant t ∧ s.finalizedCheckpoint.epoch ≤ t.finalizedCheckpoint.epoch ∧
        (epoch ≤ getCurrentEpoch s → t.finalizedCheckpoint.epoch ≤ epoch →
          PendingTail count epoch s → PendingTail count epoch t))

/-- Each state is related to itself. -/
theorem PendingTailRun.refl {count : Nat} {epoch : Epoch}
    (s : BeaconState preset fork) : PendingTailRun count epoch s s :=
  ⟨UInt64.le_refl _, fun inv => ⟨inv, UInt64.le_refl _, fun _ _ tail => tail⟩⟩

/-- Two consecutive related runs give a related run. -/
theorem PendingTailRun.trans {count : Nat} {epoch : Epoch}
    {s m t : BeaconState preset fork}
    (one : PendingTailRun count epoch s m) (two : PendingTailRun count epoch m t) :
    PendingTailRun count epoch s t := by
  refine ⟨UInt64.le_trans one.1 two.1, fun inv => ?_⟩
  obtain ⟨middle, firstFinalized, firstTail⟩ := one.2 inv
  obtain ⟨last, secondFinalized, secondTail⟩ := two.2 middle
  exact ⟨last, UInt64.le_trans firstFinalized secondFinalized, fun low high tail =>
    secondTail (UInt64.le_trans low one.1) high
      (firstTail low (UInt64.le_trans secondFinalized high) tail)⟩

/-- Processing slots relates its input and output, for a finite epoch. -/
theorem pendingTailRun_processSlots {config : Config} {checks : SignatureChecks}
    {s t : BeaconState preset fork} {slot : Slot} {epoch : Epoch} {count : Nat}
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : processSlots config checks s slot = .ok t) : PendingTailRun count epoch s t := by
  refine ⟨(runKept_processSlots ok).later, fun inv => ?_⟩
  obtain ⟨afterInv, ordered⟩ := processSlots_invariant inv ok
  exact ⟨afterInv, ordered, fun low high tail =>
    pendingTail_processSlots inv ok low high finite tail⟩

/-- A block relates its input and output, for a finite epoch. -/
theorem pendingTailRun_processBlock {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork} {epoch : Epoch} {count : Nat}
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : processBlock config checks engine s block = .ok t) : PendingTailRun count epoch s t := by
  have frame := frame_processBlock ok
  refine ⟨(runKept_processBlock ok).later, fun inv =>
    ⟨frame.invariant inv, ?_,
      fun _ _ tail => pendingTail_processBlock ok finite tail⟩⟩
  rw [frame.finalized]
  exact UInt64.le_refl _

/-- A state transition relates its input and output, for a finite epoch. -/
theorem pendingTailRun_stateTransition {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {epoch : Epoch} {count : Nat}
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : stateTransition config checks engine s signed true = .ok t) :
    PendingTailRun count epoch s t := by
  refine ⟨(runKept_stateTransition ok).later, fun inv => ?_⟩
  obtain ⟨afterInv, ordered⟩ := stateTransition_invariant inv ok
  exact ⟨afterInv, ordered, fun low high tail =>
    pendingTail_stateTransition inv ok low high finite tail⟩

end EthLib.Consensus
