module

public import EthLib.Consensus.Proofs.Transition.ValidatorStep

import EthLib.Consensus.Proofs.Churn
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Slashed validators keep an assigned exit

A slashing assigns an exit epoch, so every slashed validator has one.

Each step keeps it, and a slashed validator stays slashed.

Its withdrawable epoch never decreases.

A slashed validator with an assigned exit keeps its withdrawable epoch.

A newly slashed validator withdraws at least a slashings vector after the slashing.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Every slashed validator of the state has an assigned exit epoch. -/
def SlashedExitAssigned {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v → v.slashed = true →
    v.exitEpoch ≠ FAR_FUTURE_EPOCH

/-- A state with the same registry has the same slashed exits. -/
theorem SlashedExitAssigned.of_validators_eq {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  simpa only [SlashedExitAssigned, same] using held

private theorem Internal.CapStep.slashed_exit_assigned {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (step : CapStep config s t)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  intro i w after flag
  by_cases inside : i < s.validators.data.size
  · have before := Array.getElem?_eq_getElem inside
    cases oldFlag : s.validators.data[i].slashed with
    | false => exact ((step.withdrawal i _ w before after).2 delay oldFlag flag).1
    | true => exact ((step.withdrawal i _ w before after).1 oldFlag
        (held i _ before oldFlag)).2.1
  · exact step.appended delay i w (by omega) after flag

/-- Proposer and attester slashings keep the exit of every slashed validator assigned. -/
theorem processSlashing_slashed_exit_assigned
    {f : Fork} {s t : BeaconState preset f}
    (step : (∃ sl : ProposerSlashing,
      processProposerSlashing config checks s sl = .ok t) ∨
      (∃ sl : AttesterSlashing preset f,
        processAttesterSlashing config checks s sl = .ok t))
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  rcases step with ⟨sl, ok⟩ | ⟨sl, ok⟩
  · exact (CapStep.proposerSlashing ok).1.slashed_exit_assigned delay held
  · exact (CapStep.attesterSlashing ok).1.slashed_exit_assigned delay held

/-- Setting one validator keeps the slashed exits, when it keeps the slashed flag.

A validator that was slashed must keep an assigned exit. -/
theorem SlashedExitAssigned.of_setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v w : Validator}
    (set : s.setValidator i w = .ok t) (flag : w.slashed = v.slashed)
    (kept : v.slashed = true → w.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  intro j z read slashed
  by_cases eq : j = i.toNat
  · subst j
    have same : z = w := by
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] using read.symm
    subst z
    exact kept (flag ▸ slashed)
  · apply held j z ?_ slashed
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, eq, Ne.symm eq] using read

/-- Initiating an exit keeps the exit of every slashed validator assigned. -/
theorem initiateValidatorExit_slashed_exit_assigned {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  obtain ⟨v, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · exact held
  · obtain ⟨_, _, shape⟩ := exitQueue_eq queue
    have data : queued.validators.data = s.validators.data := by rw [shape]
    have read : s.validators.data[i.toNat]? = some v := getValidator_eq_ok_iff.mp found
    -- The exiting validator had no exit, so it was not slashed.
    exact (held.of_validators_eq data).of_setValidator set rfl
      (fun flag => absurd far (held _ v read flag))

/-- A change to execution credentials keeps the exit of every slashed validator assigned. -/
theorem processBlsToExecutionChange_slashed_exit_assigned {f : Fork}
    {s t : BeaconState preset f} {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  obtain ⟨v, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact held.of_setValidator set rfl (fun flag => held _ v (getValidator_eq_ok_iff.mp found) flag)

private theorem switchToCompoundingValidator_slashed_exit_assigned {f : Fork}
    {s t : BeaconState preset f} {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra i = .ok t)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨v, found, _, set, queued⟩ := ok
  exact (held.of_setValidator set rfl
    (fun flag => held _ v (getValidator_eq_ok_iff.mp found) flag)).of_validators_eq
      (congrArg (·.data) (queueExcessActiveBalance_validators queued))

private theorem queueConsolidation_slashed_exit_assigned {f : Fork}
    {s t : BeaconState preset f} {electra : .pectra ≤ f} {i target : ValidatorIndex}
    {source : Validator}
    (found : getValidator s i = .ok source) (unset : source.exitEpoch = FAR_FUTURE_EPOCH)
    (ok : queueConsolidation config s electra i source target = .ok t)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  -- The source has no exit, so it is not slashed.
  have clean : source.slashed = false := by
    cases flag : source.slashed with
    | false => rfl
    | true => exact (held _ source (getValidator_eq_ok_iff.mp found) flag unset).elim
  obtain ⟨_, _, _, _, _, _, _, set, _, rfl⟩ := queueConsolidation_steps ok
  have kept := (held.of_validators_eq rfl).of_setValidator set rfl
    (fun (flag : source.slashed = true) => by simp [clean] at flag)
  exact kept

/-- A consolidation request keeps the exit of every slashed validator assigned. -/
theorem processConsolidationRequest_slashed_exit_assigned {f : Fork}
    {s t : BeaconState preset f} {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (held : SlashedExitAssigned s) : SlashedExitAssigned t := by
  rcases consolidationRequest_cases ok with rfl | ⟨_, _, _, switched⟩ |
      ⟨_, _, _, _, accepted, queued⟩
  · exact held
  · exact switchToCompoundingValidator_slashed_exit_assigned switched held
  · exact queueConsolidation_slashed_exit_assigned (getValidator_eq_ok_iff.mpr accepted.sourceAt)
      accepted.sourceStays queued held

/-- Along a run from genesis, every slashed validator has an assigned exit.

The withdrawal delay must be positive, so a slashing assigns an exit. -/
theorem run_slashed_exit_assigned {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (i : Nat) (w : Validator) (found : x.state.validators.data[i]? = some w)
    (slashed : w.slashed = true) : w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  have kept := (CapStep.run run caps).1
  obtain ⟨_, _, _, _, initialized⟩ := genesis
  have clean := initializeBeaconStateFromEth1_unslashed initialized
  by_cases inside : i < g.state.validators.data.size
  · have before : g.state.validators.data[i]? = some g.state.validators.data[i] :=
      Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
    exact ((kept.withdrawal i _ w before found).2 delay
      (clean _ (Array.mem_of_getElem? before)) slashed).1
  · exact kept.appended delay i w (by omega) found slashed

/-- Before the epoch sentinel, a slashed validator has an assigned activation epoch. -/
theorem Run.slashed_activation_assigned {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .glamsterdam)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (slashed : v.slashed = true) : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  intro pending
  have unslashed := ((run_unassigned_eligible_balance run genesis caps
    aligned early finite) i v found pending).2.2
  simp [slashed] at unslashed

/-- A newly slashed key that had exited at the start was not yet withdrawable there. -/
theorem Run.newly_slashed_initial_exited_unwithdrawable {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (caps : CapOrder preset)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (unslashed : v.slashed = false) (slashed : w.slashed = true)
    (exited : v.exitEpoch ≤ getCurrentEpoch x.state) :
    getCurrentEpoch x.state < v.withdrawableEpoch := by
  apply UInt64.not_le.mp
  intro withdrawn
  have flag := ((CapStep.run run caps).1.retired
    i v w before after exited unslashed withdrawn).1
  simp [slashed] at flag

/-- New slashings delay withdrawal by the slashings-vector length from the run's start epoch.

Its exit epoch is assigned. -/
theorem Run.newly_slashed_withdrawableEpoch {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (unslashed : v.slashed = false) (slashed : w.slashed = true) :
    w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
      (getCurrentEpoch x.state).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat :=
  ((CapStep.run run caps).1.withdrawal i v w before after).2
    delay unslashed slashed

/-- Before the slashings stage, a slashed validator with an assigned exit keeps that exit.

Its withdrawable epoch cannot decrease across the preceding epoch stages. -/
theorem EpochTrace.slashed_withdrawableEpoch_mono
    {fork : Fork} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards, .registry] s t)
    (i : Nat) (v w : Validator)
    (before : s.validators.data[i]? = some v)
    (after : t.validators.data[i]? = some w)
    (slashed : v.slashed = true) (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    w.slashed = true ∧ w.exitEpoch = v.exitEpoch ∧
      v.withdrawableEpoch ≤ w.withdrawableEpoch := by
  cases trace with | cons justified rest =>
    cases rest with | cons inactivity rest =>
      cases rest with | cons rewarded rest =>
        cases rest with | cons registered rest =>
          cases rest
          have one := (EpochStage.action_cases.mp justified).validators_eq
            ⟨nofun, nofun, nofun⟩
          have two := (EpochStage.action_cases.mp inactivity).validators_eq
            ⟨nofun, nofun, nofun⟩
          have three := (EpochStage.action_cases.mp rewarded).validators_eq
            ⟨nofun, nofun, nofun⟩
          have atRegistry := before
          rw [← one, ← two, ← three] at atRegistry
          have ok := EpochStage.action_cases.mp registered
          have kept := ((CapStep.registry ok).1.withdrawal i v w atRegistry after).1
            slashed assigned
          obtain ⟨last, located, life⟩ :=
            (registryLifecycle_processRegistryUpdates ok).validators i v atRegistry
          obtain rfl : last = w := Option.some.inj (located.symm.trans after)
          exact ⟨kept.1, life.exitEpoch assigned, by rw [kept.2.2]; exact UInt64.le_refl _⟩

/-- A slashed validator with an assigned exit stays slashed, with an assigned exit.

Its withdrawable epoch cannot decrease.

This holds along a run, then the cache step of the next slot, then any stages of the next epoch. -/
theorem Run.slashed_withdrawableEpoch_mono_epoch
    {x outer : ForkedBeaconState preset} {s t : BeaconState preset outer.fork}
    {stages : List EpochStage}
    (run : Run config checks x outer)
    (caps : CapOrder preset)
    (cached : processSlot outer.state = .ok s)
    (trace : EpochTrace (EpochStage.action config checks) stages s t)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v) (after : t.validators.data[i]? = some w)
    (slashed : v.slashed = true) (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
      v.withdrawableEpoch ≤ w.withdrawableEpoch := by
  have runStep := (CapStep.run run caps).1
  -- The cache step keeps the registry, the slot and the proposer lookahead.
  have cacheStep : CapStep config outer.state s := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cached
    exact CapStep.data
  have span := (runStep.trans cacheStep).trans (CapStep.epochTrace trace)
  obtain ⟨flag, exit, same⟩ := (span.withdrawal i v w before after).1 slashed assigned
  exact ⟨flag, exit, by rw [same]; exact UInt64.le_refl _⟩

/-- A slashed validator with an assigned exit keeps its withdrawable epoch along a run.

It stays slashed.

A slashing sets the withdrawable epoch once, so a validator that is already slashed keeps it. -/
theorem Run.slashed_withdrawable_eq {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (caps : CapOrder preset)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (slashed : v.slashed = true) (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    w.slashed = true ∧ w.withdrawableEpoch = v.withdrawableEpoch := by
  obtain ⟨flag, -, same⟩ := ((CapStep.run run caps).1.withdrawal i v w
    before after).1 slashed assigned
  exact ⟨flag, same⟩

/-- A slot step keeps the slashed flag at each registry position. -/
private theorem slot_slashedFlag {m n : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks m = .ok n) (i : Nat) :
    (slashedFlagAt n.state i).getD false = (slashedFlagAt m.state i).getD false := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  have same := processUpgrades_induction
    (property := fun z => (slashedFlagAt z.state i).getD false =
      (slashedFlagAt advanced i).getD false)
    (fun {pre post} held stepOk => by
      rw [(upgradeFrame_upgradeNext stepOk).slashed i]
      exact held)
    (forked := (⟨_, advanced⟩ : ForkedBeaconState preset)) rfl upgraded
  exact same.trans (slashedFlagAt_advanceSlot advancedOk i)

/-- From Electra, a key that a step newly slashes was activated by the epoch of its start.

The key is unslashed at the start, or absent from the registry there. -/
theorem Step.slashed_activated {a b : ForkedBeaconState preset} (step : Step config checks a b)
    (electra : .pectra ≤ a.fork) (early : b.fork < .glamsterdam)
    (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (finite : getCurrentEpoch a.state < FAR_FUTURE_EPOCH) (i : Nat)
    -- A key that has begun to exit at the start is activated there.
    (exited : ∀ v, a.state.validators.data[i]? = some v → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.activationEpoch ≤ getCurrentEpoch a.state)
    (flip : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    ∃ v, a.state.validators.data[i]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
      v.activationEpoch.toNat ≤ (getCurrentEpoch a.state).toNat := by
  have capped := (CapStep.run (Run.nil.snoc step) caps).1
  have chain := step.chainStep
  obtain ⟨before, after⟩ : (a.state.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (b.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    simpa only [Bool.and_eq_true, Bool.not_eq_true'] using flip
  obtain ⟨w, later, slashed⟩ : ∃ w, b.state.validators.data[i]? = some w ∧ w.slashed = true := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at after
    | some w => exact ⟨w, rfl, by simpa [found] using after⟩
  cases step with
  -- A slot step sets no flag.
  | slot ok =>
    have := slot_slashedFlag ok i
    simp only [slashedFlagAt, before, after] at this
    cases this
  | @block fork s t engine signed due ok =>
    cases found : s.validators.data[i]? with
    -- A block appends its new keys unassigned, so it does not append a slashed key.
    | none =>
      have outside := Array.getElem?_eq_none_iff.mp found
      have assigned := capped.appended delay i w outside later slashed
      obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok ok
      obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput blockOk
      have same : last.validators.data = t.validators.data := by
        split at synced
        · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
          rfl
        · cases synced
          rfl
      have size := congrArg (·.data.size) (OperationsInput.validators_eq early started)
      exact absurd (processOperations_new_validator_epochs_unassigned operated i w
        (by simp only at size outside ⊢; omega) (by rw [same]; exact later)).2 assigned
    | some v =>
      have unslashed : v.slashed = false := by simpa [found] using before
      have set := ((capped.withdrawal i v w found later).2 delay unslashed slashed).1
      have reached : v.activationEpoch ≤ getCurrentEpoch s := by
        by_cases unset : v.exitEpoch = FAR_FUTURE_EPOCH
        -- A step can assign an exit only to a key already activated by its starting epoch.
        · exact chain.exit_assigned_activated electra found later unset set
        -- A key that has begun to exit at the start is activated there, by the hypothesis.
        · exact exited v found unset
      have bound : (getCurrentEpoch s).toNat < FAR_FUTURE_EPOCH.toNat :=
        UInt64.lt_iff_toNat_lt.mp finite
      refine ⟨v, rfl, fun far => ?_, UInt64.le_iff_toNat_le.mp reached⟩
      have := UInt64.le_iff_toNat_le.mp reached
      rw [far] at this
      change 18446744073709551615 ≤ _ at this
      change _ < 18446744073709551615 at bound
      omega

end EthLib.Consensus
