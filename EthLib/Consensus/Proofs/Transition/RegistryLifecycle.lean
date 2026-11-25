module

public import EthLib.Consensus.Proofs.Transition.EpochParticipation
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: the lifecycle of a validator, at every fork

A validator keeps its index in the registry for the life of the chain.

An assigned activation or exit epoch stays exactly the same.

The registry also never shrinks.

Block operations leave a validator that they append with no activation or exit epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- One validator, later in its life.

An activation or exit epoch that was assigned stays exactly the same. -/
structure ValidatorLifecycle (validator later : Validator) : Prop where
  activationEpoch : validator.activationEpoch ≠ FAR_FUTURE_EPOCH →
    later.activationEpoch = validator.activationEpoch
  exitEpoch : validator.exitEpoch ≠ FAR_FUTURE_EPOCH → later.exitEpoch = validator.exitEpoch

theorem ValidatorLifecycle.refl (validator : Validator) : ValidatorLifecycle validator validator :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem ValidatorLifecycle.trans {first second third : Validator}
    (one : ValidatorLifecycle first second) (two : ValidatorLifecycle second third) :
    ValidatorLifecycle first third where
  activationEpoch set := by
    have same := one.activationEpoch set
    exact (two.activationEpoch (same ▸ set)).trans same
  exitEpoch set := by
    have same := one.exitEpoch set
    exact (two.exitEpoch (same ▸ set)).trans same

/-- Each validator after a step is the one before it at its index.

It has the same key, effective balance and largest effective balance.

Any assigned epoch is unchanged, and it is unslashed only if it was unslashed. -/
def RegistryEntriesKept (u v : BeaconState preset fork) : Prop :=
  ∀ (i : Nat) (w : Validator), v.validators.data[i]? = some w → ∃ old,
    u.validators.data[i]? = some old ∧ w.pubkey = old.pubkey ∧
      w.effectiveBalance = old.effectiveBalance ∧
      withdrawalMaxEffectiveBalance preset fork w =
        withdrawalMaxEffectiveBalance preset fork old ∧
      (w.slashed = false → old.slashed = false) ∧ ValidatorLifecycle old w

/-- The registry of a later state, which may be of a later fork.

It is at least as long.

Each existing validator remains at its index, with its assigned epochs unchanged. -/
structure RegistryLifecycle {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  validators : ∀ (index : Nat) (validator : Validator),
    state.validators.data[index]? = some validator →
      ∃ later, after.validators.data[index]? = some later ∧ ValidatorLifecycle validator later

namespace RegistryLifecycle

theorem refl (state : BeaconState preset fork) : RegistryLifecycle state state :=
  ⟨Nat.le_refl _, fun _ validator found => ⟨validator, found, .refl validator⟩⟩

theorem trans {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    (one : RegistryLifecycle first second) (two : RegistryLifecycle second third) :
    RegistryLifecycle first third where
  size_le := Nat.le_trans one.size_le two.size_le
  validators index validator found := by
    obtain ⟨middle, middleFound, oneStep⟩ := one.validators index validator found
    obtain ⟨later, laterFound, twoStep⟩ := two.validators index middle middleFound
    exact ⟨later, laterFound, oneStep.trans twoStep⟩

/-- A state with the same validators, of any fork. -/
theorem of_data {fork' : Base.Fork} {after : BeaconState preset fork'}
    (same : after.validators.data = state.validators.data) : RegistryLifecycle state after :=
  ⟨Nat.le_of_eq (by rw [same]), fun index validator found =>
    ⟨validator, by rw [same]; exact found, .refl _⟩⟩

/-- Appending a validator does not change any existing entry. -/
theorem append {validator : Validator}
    (added : after.validators.data = state.validators.data.push validator) :
    RegistryLifecycle state after where
  size_le := by simp [added]
  validators index old found := by
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    refine ⟨old, ?_, .refl _⟩
    simpa [added, Array.getElem?_push, Nat.ne_of_lt inside] using found

/-- A fold whose every step keeps the lifecycle keeps it. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → RegistryLifecycle s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : RegistryLifecycle state after :=
  foldlM_ok_invariant (RegistryLifecycle state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- Replacing a validator by itself later in its life. -/
theorem putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (step : ValidatorLifecycle state.validators.data[index] validator) :
    RegistryLifecycle state (state.putValidator index inside validator) where
  size_le := by simp [BeaconState.putValidator]
  validators other old found := by
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
    split
    · rename_i same
      subst same
      have equal : state.validators.data[index] = old := by
        rw [Array.getElem?_eq_getElem inside] at found
        exact Option.some.inj found
      exact ⟨validator, by simp, equal ▸ step⟩
    · exact ⟨old, found, .refl _⟩

theorem setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (step : ValidatorLifecycle old validator) : RegistryLifecycle state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine putValidator inside ?_
  have read : state.validators.data[index.toNat]? = some old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  rw [Array.getElem?_eq_getElem inside] at read
  exact Option.some.inj read ▸ step

/-- Replacing a validator at its natural-number position. -/
theorem setValidatorAt {position : Nat} {old validator : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after)
    (step : ValidatorLifecycle old validator) :
    RegistryLifecycle state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  exact putValidator inside (oldEq ▸ step)

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : RegistryLifecycle state after :=
  of_data (by rw [increaseBalance_validators computed])

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : RegistryLifecycle state after :=
  of_data (by rw [decreaseBalance_validators computed])

end RegistryLifecycle

/-- Every epoch stage keeps the slot. -/
theorem EpochStage.Edge.slot_eq {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t) : t.slot = s.slot := by
  have computed := EpochStage.action_cases.mpr edge
  by_cases ordinary : stage ≠ .justification ∧ stage ≠ .payments ∧
      stage ≠ .participation ∧ stage ≠ .pendingDeposits
  · exact (mutatorEpochFrameLaws.toEpochStepLaws.epochEdge ordinary computed).toFrame.slot
  cases stage
  case justification => exact processJustificationAndFinalization_slot edge
  case payments =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
    · cases edge; rfl
  case participation =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · cases edge; rfl
    · exact (frame_processParticipationRecordUpdates edge).slot
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact (frame_processPendingDeposits edge).slot
    · cases edge; rfl
  all_goals simp at ordinary

/-- An epoch stage keeps five fields, unless it is one of six stages.

Those are rewards, registry updates, slashings, the two pending stages and effective balances.

The fields are the validators, balances, pending consolidations, deposit carry and slot. -/
theorem EpochStage.Edge.records {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t)
    (other : stage ≠ .rewards ∧ stage ≠ .registry ∧ stage ≠ .slashings ∧
      stage ≠ .pendingDeposits ∧ stage ≠ .pendingConsolidations ∧ stage ≠ .effectiveBalances) :
    t.validators = s.validators ∧ t.balances = s.balances ∧
      t.pendingConsolidations = s.pendingConsolidations ∧
      t.depositBalanceToConsume = s.depositBalanceToConsume ∧ t.slot = s.slot := by
  cases stage <;> simp only [EpochStage.Edge] at edge
  case justification =>
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok edge
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      rw [← rest]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  case inactivity =>
    split at edge
    · rw [processInactivityUpdates_frame edge]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact edge ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩
  case eth1Reset =>
    split at edge
    · rw [processEth1DataReset_frame edge]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact edge ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩
  case payments =>
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact edge ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  case history =>
    split at edge
    · unfold processHistoricalSummariesUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · unfold processHistoricalRootsUpdate at edge
      simp only [bind_ok_iff, liftAccessor_ok] at edge
      obtain ⟨_, _, edge⟩ := edge
      split at edge
      · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at edge
        obtain ⟨_, _, _, _, rfl⟩ := edge
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · cases edge; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  case participation =>
    split at edge
    · subst edge
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rename_i early
      obtain ⟨u, computed, _, _, restored⟩ :=
        processParticipationRecordUpdates_eq (state := s) (Nat.lt_of_not_le early)
      obtain rfl := Except.ok.inj (computed.symm.trans edge)
      exact ⟨congrArg (·.validators) restored, congrArg (·.balances) restored,
        congrArg (·.pendingConsolidations) restored,
        congrArg (·.depositBalanceToConsume) restored, congrArg (·.slot) restored⟩
  case syncCommittees =>
    split at edge
    · unfold processSyncCommitteeUpdates at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact edge ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact edge ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩
  case ptcWindow =>
    split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact edge ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩
  all_goals simp at other

/-- An epoch stage keeps the validators, unless it is one of three stages.

Those are registry updates, pending deposits and effective-balance updates. -/
theorem EpochStage.Edge.validators_eq {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t)
    (other : stage ≠ .registry ∧ stage ≠ .pendingDeposits ∧ stage ≠ .effectiveBalances) :
    t.validators = s.validators := by
  cases stage
  case rewards => rw [processRewardsAndPenalties_frame edge]
  case slashings => rw [processSlashings_frame edge]
  case pendingConsolidations =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact (processPendingConsolidations_kept edge).1
    · exact edge ▸ rfl
  case registry | pendingDeposits | effectiveBalances => simp at other
  all_goals exact (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).1

/-- Every epoch stage other than the registry updates keeps the end of the exit queue.

It also keeps the balance left to consume in that last exit epoch. -/
theorem EpochStage.Edge.exitQueue {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t) (other : stage ≠ .registry) :
    t.earliestExitEpoch = s.earliestExitEpoch ∧
      t.exitBalanceToConsume = s.exitBalanceToConsume := by
  cases stage <;> simp only [EpochStage.Edge] at edge
  case registry => exact absurd rfl other
  case justification => rw [processJustificationAndFinalization_eq edge]; exact ⟨rfl, rfl⟩
  case rewards => rw [processRewardsAndPenalties_frame edge]; exact ⟨rfl, rfl⟩
  case slashings => rw [processSlashings_frame edge]; exact ⟨rfl, rfl⟩
  case effectiveBalances => rw [processEffectiveBalanceUpdates_frame edge]; exact ⟨rfl, rfl⟩
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    exact ⟨rfl, rfl⟩
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    exact ⟨rfl, rfl⟩
  case participation =>
    split at edge
    · subst edge
      exact ⟨rfl, rfl⟩
    · rename_i early
      obtain ⟨u, computed, _, _, restored⟩ :=
        processParticipationRecordUpdates_eq (state := s) (Nat.lt_of_not_le early)
      obtain rfl := Except.ok.inj (computed.symm.trans edge)
      exact ⟨congrArg (·.earliestExitEpoch) restored, congrArg (·.exitBalanceToConsume) restored⟩
  case pendingDeposits =>
    split at edge
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ :=
        processPendingDeposits_applied edge
      refine foldlM_ok_invariant (fun b => b.earliestExitEpoch = s.earliestExitEpoch ∧
        b.exitBalanceToConsume = s.exitBalanceToConsume) (fun _ _ _ prior step => ?_)
        ⟨rfl, rfl⟩ folded
      rcases applyPendingDeposit_cases step with rfl | ⟨_, raised⟩ | ⟨_, added⟩
      · exact prior
      · obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
        exact prior
      · unfold addValidatorToRegistry at added
        split at added
        · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
            pure, Except.pure, Except.ok.injEq] at added
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := added
          exact prior
        · split at added <;> cases added
          exact prior
    · subst edge
      exact ⟨rfl, rfl⟩
  case pendingConsolidations =>
    split at edge
    · exact processPendingConsolidations_exitQueue edge
    · subst edge
      exact ⟨rfl, rfl⟩
  case history =>
    split at edge
    · unfold processHistoricalSummariesUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl⟩
    · unfold processHistoricalRootsUpdate at edge
      simp only [bind_ok_iff, liftAccessor_ok] at edge
      obtain ⟨_, _, edge⟩ := edge
      split at edge
      · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at edge
        obtain ⟨_, _, _, _, rfl⟩ := edge
        exact ⟨rfl, rfl⟩
      · cases edge; exact ⟨rfl, rfl⟩
  case syncCommittees =>
    split at edge
    · unfold processSyncCommitteeUpdates at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl⟩
  all_goals
    split at edge
    · first
        | rw [processInactivityUpdates_frame edge]
        | rw [processEth1DataReset_frame edge]
        | rw [processBuilderPendingPayments_eq edge]
        | (simp only [processProposerLookahead, processPtcWindow, bind_ok_iff, pure,
            Except.pure, Except.ok.injEq] at edge
           obtain ⟨_, _, _, _, rfl⟩ := edge)
      exact ⟨rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl⟩

/-! ## Mutators -/

theorem registryLifecycle_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · have same := (exitQueue_validators queue).1
    -- Only a validator with no exit epoch gets one.
    exact (RegistryLifecycle.of_data (by rw [same])).trans <|
      .setValidator ((getValidator_of_validators_eq same index).trans found) set
        ⟨fun _ => rfl, fun set => absurd far set⟩

theorem registryLifecycle_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    RegistryLifecycle state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  -- Marking the validator slashed does not change its activation or exit epoch.
  exact (registryLifecycle_initiateValidatorExit exitedOk).trans <|
    ((RegistryLifecycle.setValidator found markedOk
      ⟨fun _ => rfl, fun _ => rfl⟩).trans (by exact .of_data rfl)).trans <|
    (RegistryLifecycle.decreaseBalance loweredOk).trans <|
    (RegistryLifecycle.increaseBalance raisedOk).trans <|
    (RegistryLifecycle.increaseBalance lastOk).trans
      (.of_data (by rw [(slashValidator_last done).1]))

/-! ## The steps of a block -/

theorem registryLifecycle_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : RegistryLifecycle state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_data rfl

theorem registryLifecycle_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_data rfl

theorem registryLifecycle_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : RegistryLifecycle state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_data (by rw [← rest])

theorem registryLifecycle_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    RegistryLifecycle state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact registryLifecycle_slashValidator slashed

theorem registryLifecycle_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    RegistryLifecycle step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact registryLifecycle_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem registryLifecycle_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    RegistryLifecycle state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => RegistryLifecycle state step.1)
    (fun _ _ _ before ok => before.trans (registryLifecycle_slashIfSlashable ok))
    (show RegistryLifecycle state (state, false).1 from .refl state) folded

theorem registryLifecycle_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    RegistryLifecycle state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : RegistryLifecycle raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_data rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        RegistryLifecycle state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_data rfl
    exact (flagged _ _).trans ((RegistryLifecycle.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_data (by rw [← rest])

/-- Successful admission appends without replacing any existing validator. -/
private theorem registryLifecycle_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    RegistryLifecycle state after :=
  .append (addValidatorToRegistry_validators_eq_push computed)

theorem registryLifecycle_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    RegistryLifecycle state after := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact .refl _
  · exact .increaseBalance raised
  · exact registryLifecycle_addValidatorToRegistry added

private theorem registryLifecycle_applyDeposit {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    RegistryLifecycle state after := by
  rcases applyDeposit_cases computed with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, computed⟩
  · exact .refl _
  · exact .of_data rfl
  · exact (registryLifecycle_addValidatorToRegistry added).trans (.of_data rfl)
  · exact registryLifecycle_applyPendingDeposit computed

theorem registryLifecycle_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (RegistryLifecycle.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (registryLifecycle_applyDeposit applied)

/-- A successful voluntary exit is the exit call on the state before it. -/
theorem processVoluntaryExit_initiates {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    initiateValidatorExit config state signed.message.validatorIndex = .ok after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact exited

theorem registryLifecycle_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    RegistryLifecycle state after :=
  registryLifecycle_initiateValidatorExit (processVoluntaryExit_initiates computed)

/-! ## Requests of the execution layer -/

theorem registryLifecycle_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨-, -, -, _, _, rfl⟩ := processDepositRequest_ok computed
  exact .of_data rfl

private theorem registryLifecycle_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    RegistryLifecycle state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

private theorem registryLifecycle_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    RegistryLifecycle state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

private theorem registryLifecycle_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    RegistryLifecycle state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (registryLifecycle_computeExitEpochAndUpdateChurn churned).trans (.of_data rfl)
  · cases computed
    exact .refl _

theorem registryLifecycle_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    RegistryLifecycle state after := by
  rcases withdrawalRequest_cases computed with rfl | ⟨_, _, _, exited⟩ | ⟨_, _, _, _, withdrawn⟩
  · exact .refl _
  · exact registryLifecycle_initiateValidatorExit exited
  · exact registryLifecycle_requestPartialWithdrawal withdrawn

private theorem registryLifecycle_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_data rfl
  · cases computed
    exact .refl _

/-- A switch to compounding changes only the withdrawal credentials of the validator. -/
theorem registryLifecycle_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (RegistryLifecycle.setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩).trans
    (registryLifecycle_queueExcessActiveBalance queued)

/-- The source of a consolidation gets an exit epoch, which it did not have. -/
private theorem registryLifecycle_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, _, _, _, churned, _, set, _, rfl⟩ := queueConsolidation_steps computed
  exact (registryLifecycle_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (RegistryLifecycle.setValidator (old := source) (by exact getValidator_eq_ok_iff.mpr found) set
      ⟨fun _ => rfl, fun set => absurd far set⟩).trans (.of_data rfl)

theorem registryLifecycle_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    RegistryLifecycle state after := by
  rcases consolidationRequest_cases computed with rfl | ⟨_, _, _, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact .refl _
  · exact registryLifecycle_switchToCompoundingValidator switched
  · exact registryLifecycle_queueConsolidation accepted.sourceAt accepted.sourceStays queued

/-- From Gloas, successful parent payload processing preserves each existing validator's index.

It also preserves any assigned activation and exit epochs of each existing validator.

Only withdrawal and consolidation requests can change validator records. -/
theorem registryLifecycle_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    RegistryLifecycle state after :=
  processParentExecutionPayload_step_of RegistryLifecycle .refl (fun one two => one.trans two)
    (fun _ same => .of_data (congrArg (·.data) same))
    (fun ok => registryLifecycle_processWithdrawalRequest ok)
    (fun ok => registryLifecycle_processConsolidationRequest ok) computed

theorem registryLifecycle_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    RegistryLifecycle state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDepositRequest ok)
      depositsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok)
      consolidationsOk

/-! ## Withdrawals -/

/-- Withdrawals change balances and withdrawal bookkeeping, never the validators. -/
private theorem processWithdrawals_validators {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    after.validators = state.validators := by
  have expected {expected : ExpectedWithdrawals}
      (ok : applyExpectedWithdrawals state capella expected = .ok after) :
      after.validators = state.validators := by
    exact applyExpectedWithdrawals_of (fun a b => b.validators = a.validators)
      (fun _ => rfl) (fun one two => two.trans one)
      (fun step => by rw [applyWithdrawal_eq step]) (fun _ same => same) ok
  exact processWithdrawals_of (fun a b => b.validators = a.validators) rfl (fun _ => expected)
    computed

/-- The execution part of a block keeps the validators, at every fork. -/
theorem processBlockExecution_validators {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.validators = state.validators :=
  processBlockExecution_step_of (fun a b => b.validators = a.validators) (fun _ => rfl)
    (fun one two => two.trans one) (fun _ same => same) processWithdrawals_validators computed

/-- The sync aggregate changes only the balances. -/
theorem processSyncAggregate_eq {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    ∃ balances, after = { state with balances } := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun t => ∃ balances, t = { state with balances }) ?_
    ⟨_, rfl⟩ folded
  rintro _ _ _ ⟨_, rfl⟩ stepped
  unfold applySyncReward at stepped
  split at stepped
  · simp only [bind_ok_iff, liftAccessor_ok] at stepped
    obtain ⟨_, raised, _, _, paid⟩ := stepped
    obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp paid
    exact ⟨_, rfl⟩
  · obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp (liftAccessor_ok.mp stepped)
    exact ⟨_, rfl⟩

/-- Before Gloas, the steps of a block before its operations keep the validators.

From Gloas the payload of the parent runs first, and its requests can start exits. -/
theorem OperationsInput.validators_eq {block : BeaconBlock preset fork}
    {input : BeaconState preset fork} (early : fork < .glamsterdam)
    (started : OperationsInput config checks engine state block input) :
    input.validators = state.validators :=
  started.step_of (fun a b => b.validators = a.validators) (fun _ => rfl)
    (fun one two => two.trans one) (fun gloas _ => absurd gloas (Nat.not_le_of_lt early))
    (fun headed => by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
      rfl)
    (fun _ executed => processBlockExecution_validators executed)
    (fun revealed => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
      rfl)
    (fun _ voted => by
      obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
      rw [← rest])

/-- A change to an execution address changes only the withdrawal credentials of the validator. -/
theorem registryLifecycle_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## Blocks -/

/-- The operations of a block keep the lifecycle of the registry.

They are its slashings, attestations, deposits, exits, credential changes and requests. -/
theorem registryLifecycle_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of RegistryLifecycle .refl (fun one two => one.trans two)
      (fun ok => registryLifecycle_processDeposit ok)
      (fun ok => registryLifecycle_processVoluntaryExit ok)
      (fun ok => registryLifecycle_processBlsToExecutionChange ok)
      (fun ok => registryLifecycle_processExecutionRequests ok)
      (fun ok => by rw [processPayloadAttestation_eq ok]; exact .refl _) computed
  exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok)
      proposersOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
      slashingsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttestation ok)
      attestedOk).trans rest

theorem registryLifecycle_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  -- From Gloas the payload of the parent runs before the header and applies its requests.
  have head : RegistryLifecycle state input :=
    OperationsInput.step_of RegistryLifecycle .refl (fun one two => one.trans two)
      (fun _ ok => registryLifecycle_processParentExecutionPayload ok)
      registryLifecycle_processBlockHeader
      (fun _ ok => .of_data (congrArg (·.data) (processBlockExecution_validators ok)))
      registryLifecycle_processRandao (fun _ ok => registryLifecycle_processEth1Data ok) started
  have tail : RegistryLifecycle last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact .of_data rfl
    · cases synced
      exact .refl _
  exact head.trans ((registryLifecycle_processOperations operated).trans tail)

/-! ## The steps of an epoch -/

/-- Joining the activation queue changes only the eligibility epoch. -/
private theorem validatorLifecycle_queueForActivation {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    ValidatorLifecycle validator queued := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

private theorem registryLifecycle_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    RegistryLifecycle state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := RegistryLifecycle.setValidatorAt found markedOk
    (validatorLifecycle_queueForActivation queuedOk)
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, exited⟩ := computed
    exact set.trans (registryLifecycle_initiateValidatorExit exited)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- A validator eligible for activation has no activation epoch yet. -/
theorem activationEpoch_of_isEligibleForActivation {validator : Validator}
    (eligible : isEligibleForActivation state validator = true) :
    validator.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
  exact eligible.2

/-- Activating a validator that has no activation epoch yet. -/
private theorem registryLifecycle_activateValidator {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (far : validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : activateValidator state index = .ok after) : RegistryLifecycle state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldFound, _, _, set⟩ := computed
  have same := Except.ok.inj (oldFound.symm.trans found)
  subst same
  exact .setValidator oldFound set ⟨fun set => absurd far set, fun _ => rfl⟩

/-- Each index in the activation queue is that of a validator eligible for activation. -/
theorem mem_activationQueue {index : ValidatorIndex}
    (member : index ∈ activationQueue state) :
    ∃ (position : Nat) (validator : Validator), position.toUInt64 = index ∧
      state.validators.data[position]? = some validator ∧
      isEligibleForActivation state validator = true := by
  simp only [activationQueue, List.mem_map, List.mem_mergeSort] at member
  obtain ⟨⟨eligibleEpoch, queuedIndex⟩, member, equal⟩ := member
  simp only [List.mem_filterMap] at member
  obtain ⟨⟨validator, position⟩, positionOk, selected⟩ := member
  split at selected
  · rename_i eligible
    simp only [Option.some.injEq, Prod.mk.injEq] at selected
    obtain ⟨_, rfl⟩ := selected
    refine ⟨position, validator, equal, ?_, eligible⟩
    simpa only [Array.getElem?_toList] using (List.mem_zipIdx_iff_getElem?.mp positionOk)
  · cases selected

/-- Each index put back into the queue is that of a validator with no activation epoch. -/
theorem preActivation_waiting {f : Fork} {s : BeaconState preset f} (early : f < .glamsterdam)
    {index : ValidatorIndex} (member : index ∈ preActivationIndices s) :
    ∃ validator, s.validators.data[index.toNat]? = some validator ∧
      validator.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [preActivationIndices, List.mem_map, List.mem_mergeSort, List.mem_filter] at member
  obtain ⟨⟨validator, position⟩, ⟨located, waiting⟩, rfl⟩ := member
  have read : s.validators.data[position]? = some validator := by
    simpa using List.mem_zipIdx_iff_getElem?.mp located
  have small : position < 2 ^ 64 := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp read).1
    (Nat.le_trans (s.validators.bound early)
      (Nat.le_of_lt preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt))
  refine ⟨validator, ?_, by simpa using waiting⟩
  rw [Uint64.toNat_toUInt64 small]
  exact read

/-- The activation queue holds each index at most once, while the registry is below `2^64`. -/
theorem activationQueue_nodup (small : state.validators.data.size < 2 ^ 64) :
    (activationQueue state).Nodup := by
  let entries := state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isEligibleForActivation state validator then
      some (validator.activationEligibilityEpoch, index.toUInt64)
    else none
  -- The positions of the registry increase, and below `2^64` their indices of 64 bits differ.
  have base : state.validators.data.toList.zipIdx.Pairwise (fun a b => a.2 < b.2) := by
    have := List.pairwise_lt_range' (s := 0) (n := state.validators.data.toList.length)
    rw [← List.zipIdx_map_snd 0] at this
    exact List.pairwise_map.mp this
  have distinct : entries.Pairwise (fun a b => a.2 ≠ b.2) := by
    apply List.Pairwise.filterMap _ ?_ (List.Pairwise.and_mem.mp base)
    rintro ⟨v, i⟩ ⟨w, j⟩ ⟨mi, mj, lt⟩ a ha b hb
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at ha hb
    obtain ⟨_, rfl⟩ := ha
    obtain ⟨_, rfl⟩ := hb
    have hi : i < state.validators.data.size := by simpa using (List.mem_zipIdx' mi).1
    have hj : j < state.validators.data.size := by simpa using (List.mem_zipIdx' mj).1
    intro equal
    dsimp only at equal lt
    have equalNat := congrArg UInt64.toNat equal
    rw [Uint64.toNat_toUInt64 (by omega), Uint64.toNat_toUInt64 (by omega)] at equalNat
    omega
  have unique : (entries.map (·.2)).Nodup := List.pairwise_map.mpr distinct
  exact ((List.mergeSort_perm entries _).map (·.2)).nodup_iff.mpr unique

private theorem foldActivateValidator_of_predicate
    (R : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ s, R s s)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (P : ValidatorIndex → Validator → Prop)
    (activate : ∀ {s t : BeaconState preset fork} {i : ValidatorIndex} {v : Validator},
      P i v → getValidator s i = .ok v → v.activationEpoch = FAR_FUTURE_EPOCH →
      activateValidator s i = .ok t → R s t) :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
        validator.activationEpoch = FAR_FUTURE_EPOCH ∧ P index validator) →
      indices.foldlM activateValidator state = .ok after → R state after
  | [], state, after, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ refl state
  | index :: rest, state, after, unique, eligible, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨validator, found, far, property⟩ := eligible index List.mem_cons_self
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    refine trans (activate property found far first)
      (foldActivateValidator_of_predicate R refl trans P activate restUnique
        (fun other member => ?_) tail)
    -- The other validators of the queue are not touched by this activation.
    have distinct : other ≠ index := fun same => absent (same ▸ member)
    obtain ⟨otherValidator, otherFound, otherFar, otherProperty⟩ :=
      eligible other (List.mem_cons_of_mem _ member)
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨_, _, _, _, set⟩ := first
    exact ⟨otherValidator, (getValidator_setValidator_of_ne set distinct).trans otherFound,
      otherFar, otherProperty⟩

/-- Fold distinct activations through a relation using their initially unassigned validators.

The relation supplies its own activation invariant; the fold retains the untouched tail. -/
private theorem foldActivateValidator_of_unassigned
    (R : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ s, R s s)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (activate : ∀ {s t : BeaconState preset fork} {i : ValidatorIndex} {v : Validator},
      getValidator s i = .ok v → v.activationEpoch = FAR_FUTURE_EPOCH →
      activateValidator s i = .ok t → R s t) :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
        validator.activationEpoch = FAR_FUTURE_EPOCH) →
      indices.foldlM activateValidator state = .ok after → R state after := by
  intro indices state after unique eligible computed
  apply foldActivateValidator_of_predicate R refl trans (fun _ _ => True)
    (fun _ found far ok => activate found far ok) unique ?_ computed
  intro index member
  obtain ⟨v, found, far⟩ := eligible index member
  exact ⟨v, found, far, trivial⟩

/-- The activation callback can read the original queue record's eligibility epoch. -/
theorem foldActivateValidator_of_queue
    (R : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ s, R s s)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    {indices : List ValidatorIndex} {state after : BeaconState preset fork}
    (activate : ∀ {s t : BeaconState preset fork} {i : ValidatorIndex} {v original : Validator},
      i ∈ indices → getValidator state i = .ok original →
      v.activationEligibilityEpoch = original.activationEligibilityEpoch →
      getValidator s i = .ok v → v.activationEpoch = FAR_FUTURE_EPOCH →
      activateValidator s i = .ok t → R s t)
    (unique : indices.Nodup)
    (eligible : ∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
      validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : indices.foldlM activateValidator state = .ok after) : R state after := by
  let P := fun i (v : Validator) => i ∈ indices ∧ ∃ original,
    getValidator state i = .ok original ∧
      v.activationEligibilityEpoch = original.activationEligibilityEpoch
  apply foldActivateValidator_of_predicate R refl trans P ?_ unique ?_ computed
  · intro s t i v property found far ok
    obtain ⟨member, original, located, epoch⟩ := property
    exact activate member located epoch found far ok
  · intro index member
    obtain ⟨v, found, far⟩ := eligible index member
    exact ⟨v, found, far, member, v, found, rfl⟩

theorem registryLifecycle_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    RegistryLifecycle state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine RegistryLifecycle.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact registryLifecycle_initiateValidatorExit exited
    split at ok
    · rename_i eligible
      rw [liftAccessor_ok] at ok
      have far := activationEpoch_of_isEligibleForActivation eligible
      exact .setValidatorAt found ok ⟨fun set => absurd far set, fun _ => rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  rename_i notElectra
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  -- Before Electra the registry is within its limit, far below `2^64`.
  have before : fork < .glamsterdam := Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound before) (UInt64.toNat_lt _)
  refine (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_updateRegistryEntry ok)
    updatedOk).trans (foldActivateValidator_of_unassigned RegistryLifecycle RegistryLifecycle.refl
      (fun one two => one.trans two)
      (fun found far ok => registryLifecycle_activateValidator found far ok)
      (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
      (fun index member => ?_) activated)
  obtain ⟨position, validator, equal, found, eligible⟩ :=
    mem_activationQueue (List.mem_of_mem_take member)
  refine ⟨validator, ?_, activationEpoch_of_isEligibleForActivation eligible⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : index.toNat = position := by
    rw [← equal, Uint64.toNat_toUInt64 (by omega)]
  simp [getValidator, exact, found]

/-- An update of effective balances changes only the effective balances. -/
theorem registryLifecycle_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    RegistryLifecycle state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, _, _, _, _, set⟩ := ok
  exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## The steps of an epoch from Altair -/

theorem registryLifecycle_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} {deposits : List PendingDeposit} {state : BeaconState preset fork}
    {processed : Gwei} {count : Nat} {postponed : Array PendingDeposit} {pass}
    (computed : passPendingDeposits config checks stop nextEpoch available state processed count
      postponed deposits = .ok pass) : RegistryLifecycle state pass.1.state :=
  passPendingDeposits_of RegistryLifecycle .refl (fun one two => one.trans two)
    (fun ok => registryLifecycle_applyPendingDeposit ok) computed

theorem registryLifecycle_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    RegistryLifecycle state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (registryLifecycle_passPendingDeposits ‹_›).trans (.of_data rfl)

/-- Every epoch stage preserves assigned activation and exit epochs. -/
theorem EpochStage.Edge.registryLifecycle {k : EpochStage}
    (edge : EpochStage.Edge config checks k state after) : RegistryLifecycle state after := by
  cases k
  case registry => exact registryLifecycle_processRegistryUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact registryLifecycle_processPendingDeposits edge
    · exact edge ▸ .refl _
  case effectiveBalances => exact registryLifecycle_processEffectiveBalanceUpdates edge
  all_goals exact .of_data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

/-- The epoch step keeps the lifecycle, stage by stage of the epoch schedule. -/
theorem registryLifecycle_processEpoch
    (computed : processEpoch config checks state = .ok after) : RegistryLifecycle state after := by
  apply (processEpoch_trace computed).transport RegistryLifecycle .refl (fun a b => a.trans b)
  intro k _ a b ok
  exact (EpochStage.action_cases.mp ok).registryLifecycle

/-! ## Slots, upgrades and chains -/

theorem registryLifecycle_advanceSlot
    (computed : advanceSlot config checks state = .ok after) :
    RegistryLifecycle state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedKept : RegistryLifecycle state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_data rfl
  have epochedKept : RegistryLifecycle cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact registryLifecycle_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ .refl _
  exact cachedKept.trans (epochedKept.trans (.of_data rfl))

/-- Queueing a validator that is not yet active changes its eligibility and effective balance. -/
private theorem registryLifecycle_queuePreActivation {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  have reset := RegistryLifecycle.setValidator (old := validator) (by exact found) set₂
    ⟨fun _ => rfl, fun _ => rfl⟩
  exact RegistryLifecycle.trans (by exact .of_data rfl) (reset.trans (.of_data rfl))

theorem registryLifecycle_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    RegistryLifecycle pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToAltair_spec upgraded).1
  · subst computed
    exact .of_data rfl
  · subst computed
    exact .of_data rfl
  · subst computed
    exact .of_data rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    have compoundedKept := RegistryLifecycle.foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact registryLifecycle_queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok
          exact .refl _
      · cases ok
        exact .refl _) compounded
    have queuedKept := RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_queuePreActivation ok) queued
    exact RegistryLifecycle.trans (by exact .of_data rfl) (queuedKept.trans compoundedKept)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain rfl := upgradeToHeze_ok_iff.mp upgraded
    exact .of_data (upgradeHezeFields_lists _).1

/-- Every step of a chain keeps the lifecycle of the validators. -/
theorem RegistryLifecycle.chainStep {first last : ForkedBeaconState preset}
    (step : ChainStep config checks first last) : RegistryLifecycle first.state last.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have rest := processUpgrades_induction
      (property := fun post => RegistryLifecycle advanced post.state)
      (fun before ok => before.trans (registryLifecycle_upgradeNext ok)) (.refl advanced) upgrades
    exact (registryLifecycle_advanceSlot slotOk).trans rest
  | block engine signed validate ok =>
    exact registryLifecycle_processBlock (applySignedBlock_ok ok).2.1

/-- A run preserves the assigned epochs of every existing registry entry. -/
theorem Run.registryLifecycle {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : RegistryLifecycle first.state last.state := by
  -- Each chain step preserves assigned epochs.
  --
  -- Composition gives the same result for a run.
  induction run with
  | nil => exact .refl _
  | snoc pre step ih => exact ih.trans (RegistryLifecycle.chainStep step.chainStep)

/-! ## Admissions within one step -/

/-- A validator with neither an activation epoch nor an exit epoch assigned.

Keeping both unassigned lets activity checks exclude a later exit request. -/
def Unassigned (v : Validator) : Prop :=
  v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH

/-- Every validator at position `n` or later is unassigned. -/
def UnassignedFrom (n : Nat) {fork : Fork} (s : BeaconState preset fork) : Prop :=
  ∀ i v, n ≤ i → s.validators.data[i]? = some v → Unassigned v

/-- No validator lies past the end of the registry, so the registry size is unassigned from. -/
theorem unassignedFrom_size (s : BeaconState preset fork) :
    UnassignedFrom s.validators.data.size s := by
  intro i v large found
  have := (Array.getElem?_eq_some_iff.mp found).1
  omega

/-- Each position from which the earlier registry is unassigned stays so in the later one. -/
def UnassignedKept {f g : Fork} (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop :=
  ∀ n, UnassignedFrom n s → UnassignedFrom n t

namespace UnassignedKept

private theorem refl (s : BeaconState preset fork) : UnassignedKept s s := fun _ => id

private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : UnassignedKept s t) (two : UnassignedKept t u) :
    UnassignedKept s u := fun n => two n ∘ one n

private theorem of_data {g : Fork} {t : BeaconState preset g}
    (same : t.validators.data = state.validators.data := by rfl) : UnassignedKept state t := by
  intro n h i v hi found
  exact h i v hi (same ▸ found)

private theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → UnassignedKept s t) {xs : List α}
    (ok : xs.foldlM step state = .ok after) : UnassignedKept state after :=
  foldlM_ok_invariant (UnassignedKept state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (refl state) ok

private theorem setValidatorAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old)
    (set : state.setValidatorAt i v = .ok after)
    (keeps : Unassigned old → Unassigned v) : UnassignedKept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro n h j w large read
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set] at read
  split at read
  · rename_i same
    subst j
    cases read
    apply keeps (h i old large ?_)
    simp [Array.getElem?_eq_getElem inside, oldEq]
  · exact h j w large read

private theorem setValidator {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old)
    (set : state.setValidator i v = .ok after)
    (keeps : Unassigned old → Unassigned v) : UnassignedKept state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) keeps

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v)
    (pending : Unassigned v) : UnassignedKept state after := by
  intro n h i w large found
  rw [added, Array.getElem?_push] at found
  split at found
  · cases found; exact pending
  · exact h i w large found

private theorem increaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state i amount = .ok after) : UnassignedKept state after :=
  of_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    UnassignedKept state after := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · exact refl _
  · exact increaseBalance ok
  · exact append (addValidatorToRegistry_validators_eq_push ok) ⟨rfl, rfl⟩

private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : UnassignedKept state after := by
  rcases applyDeposit_cases ok with rfl | ⟨_, middle, _, rfl | added, rfl⟩ | ⟨_, ok⟩
  · exact refl _
  · exact of_data
  · exact (append (addValidatorToRegistry_validators_eq_push added) ⟨rfl, rfl⟩).trans
      (of_data (state := middle))
  · exact applyPendingDeposit ok

theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    UnassignedKept state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_data (state := state)
    (t := { state with eth1DepositIndex := fun _ => next })).trans (applyDeposit credited)

private theorem inactive {v : Validator} (pending : Unassigned v) (e : Epoch) :
    isActiveValidator v e = false := by
  simp only [isActiveValidator, pending.1, pending.2, Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  by_cases h : FAR_FUTURE_EPOCH ≤ e
  · exact Or.inr (UInt64.not_lt.mpr h)
  · exact Or.inl h

private theorem initiateValidatorExit {i : ValidatorIndex} {v : Validator}
    (found : getValidator state i = .ok v) (notPending : ¬Unassigned v)
    (ok : Consensus.initiateValidatorExit config state i = .ok after) :
    UnassignedKept state after := by
  obtain ⟨old, read, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have equal := Except.ok.inj (read.symm.trans found)
    have same := (exitQueue_validators queue).1
    exact (of_data (congrArg (·.data) same)).trans <|
      setValidator ((getValidator_of_validators_eq same i).trans read) set
        (fun h => False.elim (notPending (equal ▸ h)))

private theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨v, found, _, active, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit found (fun h => by rw [inactive h] at active; cases active) exited

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    UnassignedKept state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  apply setValidator found set
  rintro ⟨activation, exit⟩
  exact ⟨activation, exit⟩

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    UnassignedKept state after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact of_data
  · cases ok; exact refl _

private theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    UnassignedKept state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  refine (setValidator found set (fun h => h)).trans (queueExcessActiveBalance queued)

private theorem requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) : UnassignedKept state after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    have same := (computeExitEpochAndUpdateChurn_earliest churned).2.1
    exact (of_data (by rw [same])).trans of_data
  · cases ok; exact refl _

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    UnassignedKept state after := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, _, accepted, exited⟩ |
    ⟨_, _, _, _, withdrawn⟩
  · exact refl _
  · exact initiateValidatorExit (config := config) (getValidator_eq_ok_iff.mpr accepted.found)
      (fun pending => Bool.false_ne_true ((inactive pending _).symm.trans
        (isActiveValidator_of_canRequest accepted.allowed))) exited
  · exact requestPartialWithdrawal withdrawn

private theorem queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (notPending : ¬Unassigned source)
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : UnassignedKept state after := by
  obtain ⟨_, _, _, _, _, _, _, set, _, rfl⟩ := queueConsolidation_steps ok
  exact (of_data rfl).trans <| (setValidator (by exact getValidator_eq_ok_iff.mpr found) set
    (fun h => False.elim (notPending h))).trans of_data

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    UnassignedKept state after := by
  rcases consolidationRequest_cases ok with rfl | ⟨_, _, _, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact refl _
  · exact switchToCompoundingValidator switched
  · exact queueConsolidation accepted.sourceAt
      (fun pending => Bool.false_ne_true ((inactive pending _).symm.trans accepted.sourceActive))
      queued

private theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    UnassignedKept state after :=
  of_data (congrArg (·.data) (processDepositRequest_ok ok).2.1)

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    UnassignedKept state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations)

private theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} {deposits : List PendingDeposit} {processed : Gwei} {count : Nat}
    {postponed : Array PendingDeposit} {pass}
    (computed : Consensus.passPendingDeposits config checks stop nextEpoch available state
      processed count postponed deposits = .ok pass) : UnassignedKept state pass.1.state :=
  passPendingDeposits_of UnassignedKept refl (fun one two => one.trans two)
    (fun ok => applyPendingDeposit ok) computed

private theorem processPendingDeposits {electra : .pectra ≤ fork}
    (computed : Consensus.processPendingDeposits config checks state electra = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (passPendingDeposits ‹_›).trans of_data

private theorem processEffectiveBalanceUpdates
    (computed : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.processEffectiveBalanceUpdates at computed
  refine foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact setValidatorAt found set id

/-- Every epoch stage but the registry updates keeps the unassigned suffixes. -/
private theorem edge {k : EpochStage} (edge : EpochStage.Edge config checks k state after)
    (other : k ≠ .registry) : UnassignedKept state after := by
  cases k
  case registry => exact absurd rfl other
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits edge
    · exact edge ▸ refl _
  case effectiveBalances => exact processEffectiveBalanceUpdates edge
  all_goals exact of_data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

end UnassignedKept

/-- Block operations append validators with no assigned epoch.

The three folds before the deposits keep the registry size, so the suffix is empty after them.

The remaining operations keep that suffix unassigned, one fold at a time. -/
private theorem newUnassigned_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot} (ok : processOperations config checks state body parentSlot = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  obtain ⟨_, _, attested, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of UnassignedKept UnassignedKept.refl (fun one two => one.trans two)
      UnassignedKept.processDeposit UnassignedKept.processVoluntaryExit
      UnassignedKept.processBlsToExecutionChange UnassignedKept.processExecutionRequests
      (fun paid => by rw [processPayloadAttestation_eq paid]; exact UnassignedKept.refl _) ok
  have sizes {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (keeps : ∀ a b c, step a b = .ok c → SameSizes a c) {xs : List α}
      {a b : BeaconState preset fork} (ok : xs.foldlM step a = .ok b) : SameSizes a b :=
    foldlM_ok_invariant (SameSizes a)
      (fun _ _ _ prior ok => prior.trans (keeps _ _ _ ok)) (SameSizes.refl _) ok
  have before := (sizes (fun _ _ _ => sameSizes_processProposerSlashing) proposersOk).trans
    ((sizes (fun _ _ _ => sameSizes_processAttesterSlashing) slashingsOk).trans
      (sizes (fun _ _ _ => sameSizes_processAttestation) attestedOk))
  apply rest
  rw [← before.1]
  exact unassignedFrom_size attested

/-- A withdrawal request retains unassigned activation and exit epochs. -/
theorem processWithdrawalRequest_epochs_unassigned {n : Nat} {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after)
    (pending : ∀ i v, n ≤ i → state.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH) :
    ∀ i v, n ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  UnassignedKept.processWithdrawalRequest ok n pending

/-- A consolidation request retains unassigned activation and exit epochs. -/
theorem processConsolidationRequest_epochs_unassigned {n : Nat} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : processConsolidationRequest config state electra request = .ok after)
    (pending : ∀ i v, n ≤ i → state.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH) :
    ∀ i v, n ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  UnassignedKept.processConsolidationRequest ok n pending

/-- The epoch step appends validators with no assigned epoch.

The stages before the pending deposits keep the registry size, so the suffix is empty there.

The registry updates are among them, so a new validator gets no activation in the same epoch.

The pending deposits append unassigned validators, and the later stages keep them so. -/
private theorem newUnassigned_processEpoch
    (computed : processEpoch config checks state = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, consolidated,
    settled, updated, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
    depositedOk, consolidatedOk, settledOk, updatedOk, rest⟩ :=
    (processEpoch_trace computed).through_effectiveBalances
  have keeps {k : EpochStage} {a b : BeaconState preset fork}
      (ok : EpochStage.action config checks k a = .ok b) (other : k ≠ .registry) :
      UnassignedKept a b :=
    UnassignedKept.edge (EpochStage.action_cases.mp ok) other
  have same {k : EpochStage} {a b : BeaconState preset fork}
      (ok : EpochStage.action config checks k a = .ok b)
      (other : k ≠ .registry ∧ k ≠ .pendingDeposits ∧ k ≠ .effectiveBalances) :
      b.validators.data.size = a.validators.data.size := by
    rw [(EpochStage.action_cases.mp ok).validators_eq other]
  have registrySize := (sameSizes_processRegistryUpdates
    (EpochStage.action_cases.mp registeredOk)).1
  have sizes : reset.validators.data.size = state.validators.data.size := by
    have one := same justifiedOk ⟨nofun, nofun, nofun⟩
    have two := same scoredOk ⟨nofun, nofun, nofun⟩
    have three := same rewardedOk ⟨nofun, nofun, nofun⟩
    have five := same slashedOk ⟨nofun, nofun, nofun⟩
    have six := same resetOk ⟨nofun, nofun, nofun⟩
    omega
  have start : UnassignedFrom state.validators.data.size reset :=
    sizes ▸ unassignedFrom_size reset
  have tail := rest.transport UnassignedKept UnassignedKept.refl (fun one two => one.trans two)
    (fun k member _ _ ok => keeps ok (by rintro rfl; simp at member))
  exact tail _ (keeps updatedOk nofun _ (keeps settledOk nofun _ (keeps consolidatedOk nofun _
    (keeps depositedOk nofun _ start))))

/-- A slot appends validators with no assigned epoch, through its epoch step if it has one. -/
private theorem newUnassigned_advanceSlot
    (computed : advanceSlot config checks state = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedSize : cached.validators.data.size = state.validators.data.size := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have epochedFrom : UnassignedFrom state.validators.data.size epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact cachedSize ▸ newUnassigned_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact cachedSize ▸ unassignedFrom_size _
  exact UnassignedKept.of_data (same := rfl) _ epochedFrom

/-- Block operations leave newly admitted validators with both epochs unassigned. -/
theorem processOperations_new_validator_epochs_unassigned {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after) :
    ∀ i v, state.validators.data.size ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  newUnassigned_processOperations ok

/-- Before Gloas, a block appends validators with no assigned epoch, in its operations only. -/
private theorem newUnassigned_processBlock {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork} (early : fork < .glamsterdam)
    (computed : processBlock config checks engine state block = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  have kept : UnassignedFrom state.validators.data.size last := by
    rw [← congrArg (·.data.size) (started.validators_eq early)]
    exact processOperations_new_validator_epochs_unassigned operated
  split at synced
  · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
    exact UnassignedKept.of_data (same := rfl) _ kept
  · cases synced
    exact kept

/-- From Electra and before Gloas, a step leaves the validators it appends with no assigned epoch.

A block appends them in its operations.

A slot appends them in the pending deposits of its epoch step, after the registry updates.

The later stages of the epoch step and the upgrades keep them unassigned. -/
theorem Step.new_validators_unassigned {m n : ForkedBeaconState preset}
    (step : Step config checks m n) (early : n.fork < .glamsterdam)
    (electra : .pectra ≤ m.fork) :
    ∀ (i : Nat) (w : Validator), m.state.validators.data.size ≤ i →
      n.state.validators.data[i]? = some w →
      w.activationEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch = FAR_FUTURE_EPOCH := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact (processUpgrades_induction (forked := ⟨m.fork, advanced⟩)
      (property := fun post => .pectra ≤ post.fork ∧
        UnassignedFrom m.state.validators.data.size post.state)
      (fun {pre post} held next => ⟨Nat.le_trans held.1 (Nat.le_of_lt post.2),
        UnassignedKept.of_data (upgradeNext_validators_of_electra held.1 next) _ held.2⟩)
      ⟨electra, newUnassigned_advanceSlot slotOk⟩ upgrades).2
  | block engine signed due ok =>
    exact newUnassigned_processBlock early (applySignedBlock_ok ok).2.1

/-- Once the exit of a validator is set, its withdrawable epoch only rises.

It moves only when the later record is slashed.

The states may be of different forks. -/
def WithdrawableKept {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) : Prop :=
  ∀ (i : Nat) (v w : Validator), s.validators.data[i]? = some v → t.validators.data[i]? = some w →
    v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.withdrawableEpoch ≤ w.withdrawableEpoch ∧
        (w.slashed = true ∨ w.withdrawableEpoch = v.withdrawableEpoch)

end EthLib.Consensus
