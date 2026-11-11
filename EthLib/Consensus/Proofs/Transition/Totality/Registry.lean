module

public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Consensus.Proofs.Time
public import EthLib.Consensus.Proofs.Transition.EpochUpdates

/-!
# Proofs: registry updates before Electra succeed

The registry step queues activations, ejects low-balance validators and activates a queue prefix.

Let a ceiling bound the first activation epoch and every finite exit epoch before the step.

Each ejection increases that ceiling by at most one.

Room for the registry length and the withdrawability delay then excludes every checked overflow.

The theorem applies to the state that the earlier epoch steps return, without their full invariant.

The positivity of pure divisors remains a separate condition for agreement with the specification.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

private def ExitsBelow (state : BeaconState preset fork) (ceiling : Nat) : Prop :=
  ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
    validator.exitEpoch.toNat ≤ ceiling

private theorem ExitsBelow.mono {state : BeaconState preset fork} {ceiling later : Nat}
    (exits : ExitsBelow state ceiling) (le : ceiling ≤ later) : ExitsBelow state later :=
  fun validator member finite => Nat.le_trans (exits validator member finite) le

private theorem ExitsBelow.putValidator {state : BeaconState preset fork} {ceiling : Nat}
    {index : Nat} (inside : index < state.validators.data.size) {validator : Validator}
    (exits : ExitsBelow state ceiling)
    (newExit : validator.exitEpoch ≠ FAR_FUTURE_EPOCH → validator.exitEpoch.toNat ≤ ceiling) :
    ExitsBelow (state.putValidator index inside validator) ceiling := by
  intro other member finite
  simp only [BeaconState.putValidator, RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact exits other old finite
  · exact newExit finite

private theorem activationExitEpoch_exists_ok (state : BeaconState preset fork) (ceiling : Nat)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (room : ceiling < 2 ^ 64) :
    ∃ epoch, computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch ∧
      epoch.toNat ≤ ceiling := by
  let epoch := ((getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat).toUInt64
  have value : epoch.toNat =
      (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat := by
    change (_ % 2 ^ 64) = _
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨epoch, computeActivationExitEpoch_ok_iff.mpr ⟨by omega, value⟩, by omega⟩

private theorem foldl_maxExitEpoch_le {validators : List Validator} {start : Epoch} {ceiling : Nat}
    (first : start.toNat ≤ ceiling)
    (exits : ∀ validator ∈ validators, validator.exitEpoch.toNat ≤ ceiling) :
    (validators.foldl (fun latest validator => max latest validator.exitEpoch) start).toNat ≤
      ceiling := by
  induction validators generalizing start with
  | nil => exact first
  | cons validator rest ih =>
    rw [List.foldl_cons]
    apply ih
    · have current := exits validator List.mem_cons_self
      simp only [UInt64.max_def]
      split <;> assumption
    · exact fun other member => exits other (List.mem_cons_of_mem validator member)

/-- A pre-Electra exit queue adds at most one to the ceiling of its existing exit epochs. -/
private theorem exitQueueEpoch_exists_ok {config : Config} {state : BeaconState preset fork}
    {ceiling : Nat}
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ExitsBelow state ceiling) (room : ceiling + 1 < 2 ^ 64) :
    ∃ epoch, exitQueueEpoch config state = .ok epoch ∧ epoch.toNat ≤ ceiling + 1 := by
  obtain ⟨earliest, earliestOk, earliestLe⟩ := activationExitEpoch_exists_ok state ceiling first
    (by omega)
  let validators := state.validators.data.toList
  let latest := (validators.filter (·.exitEpoch != FAR_FUTURE_EPOCH)).foldl
    (fun latest validator => max latest validator.exitEpoch) earliest
  have latestLe : latest.toNat ≤ ceiling := by
    apply foldl_maxExitEpoch_le earliestLe
    intro validator member
    obtain ⟨member, finite⟩ := List.mem_filter.mp member
    exact exits validator (by simpa [validators] using member) (by simpa using finite)
  have form : exitQueueEpoch config state =
      (if (getValidatorChurnLimit config state).toNat ≤
          (validators.filter (·.exitEpoch == latest)).length then
        liftArith (addChecked latest 1) else .ok latest) := by
    simp only [exitQueueEpoch, earliestOk, liftArith, Except.mapError, bind, Except.bind]; rfl
  rw [form]
  by_cases full : (getValidatorChurnLimit config state).toNat ≤
      (validators.filter (·.exitEpoch == latest)).length
  · have fits : latest.toNat + (1 : UInt64).toNat < 2 ^ 64 := by simp; omega
    refine ⟨latest + 1, ?_, ?_⟩
    · simp only [full, ↓reduceIte, liftArith, addChecked_of_lt fits, Except.mapError]
    · rw [toNat_add_of_lt fits]
      simp only [UInt64.toNat_one]
      omega
  · refine ⟨latest, ?_, by omega⟩
    simp only [full, ↓reduceIte]

private theorem initiateValidatorExit_exists_ok {config : Config} {state : BeaconState preset fork}
    {index : ValidatorIndex} {ceiling : Nat} (before : fork < .pectra)
    (inside : index.toNat < state.validators.data.size)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ExitsBelow state ceiling)
    (room : ceiling + 1 + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64) :
    ∃ after, initiateValidatorExit config state index = .ok after ∧
      after.slot = state.slot ∧ after.validators.data.size = state.validators.data.size ∧
      ExitsBelow after (ceiling + 1) := by
  let validator := state.validators.data[index.toNat]
  have found : getValidator state index = .ok validator := by
    simp [getValidator, Array.getElem?_eq_getElem inside, validator]
  by_cases started : validator.exitEpoch ≠ FAR_FUTURE_EPOCH
  · exact ⟨state, by simp [initiateValidatorExit, found, started, bind, Except.bind,
      pure, Except.pure], rfl, rfl,
      exits.mono (by omega)⟩
  · obtain ⟨epoch, epochOk, epochLe⟩ :=
      exitQueueEpoch_exists_ok (config := config) first exits (by omega)
    have delayFits : epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64 :=
      by omega
    let changed : Validator :=
      { validator with
        exitEpoch := epoch
        withdrawableEpoch := epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY }
    have written : state.setValidator index changed =
        .ok (state.putValidator index.toNat inside changed) := by
      simp [BeaconState.setValidator, inside]
    refine ⟨state.putValidator index.toNat inside changed, ?_, rfl,
      (sameSizes_putValidator state inside changed).1, ?_⟩
    · have far : validator.exitEpoch = FAR_FUTURE_EPOCH := by simpa using started
      have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
      simp only [initiateValidatorExit, found, far, bne_self_eq_false, exitQueue,
        notElectra, ↓reduceDIte, epochOk, liftArith, addChecked_of_lt delayFits,
        Except.mapError, bind, Except.bind, pure, Except.pure]
      exact written
    · exact (exits.mono (by omega)).putValidator inside (fun _ => epochLe)

private theorem updateRegistryEntry_exists_ok {config : Config} {state : BeaconState preset fork}
    {index : Nat} {ceiling : Nat} (before : fork < .pectra)
    (inside : index < state.validators.data.size)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ExitsBelow state ceiling)
    (room : ceiling + 1 + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64) :
    ∃ after, updateRegistryEntry config state index = .ok after ∧
      after.slot = state.slot ∧ after.validators.data.size = state.validators.data.size ∧
      ExitsBelow after (ceiling + 1) := by
  let validator := state.validators.data[index]
  have found : getValidatorAt state index = .ok validator := by
    simp [getValidatorAt, Array.getElem?_eq_getElem inside, validator]
  obtain ⟨queued, queuedOk, sameExit⟩ : ∃ queued, queueForActivation state validator = .ok queued ∧
      queued.exitEpoch = validator.exitEpoch := by
    by_cases eligible : isEligibleForActivationQueue preset fork validator
    · have fits : (getCurrentEpoch state).toNat + (1 : UInt64).toNat < 2 ^ 64 := by simp; omega
      refine ⟨{ validator with activationEligibilityEpoch := getCurrentEpoch state + 1 }, ?_, rfl⟩
      simp only [queueForActivation, eligible, ↓reduceIte, addChecked_of_lt fits,
        liftAccessor, liftArith, Except.mapError, bind, Except.bind, pure, Except.pure]
    · exact ⟨validator, by simp [queueForActivation, eligible, pure, Except.pure], rfl⟩
  let updated := state.putValidator index inside queued
  have written : state.setValidatorAt index queued = .ok updated := by
    simp [BeaconState.setValidatorAt, inside, updated]
  have updatedExits : ExitsBelow updated ceiling := by
    apply exits.putValidator inside
    intro finite
    rw [sameExit] at finite ⊢
    exact exits validator (Array.getElem_mem inside) finite
  by_cases eject : isActiveValidator queued (getCurrentEpoch updated) &&
      queued.effectiveBalance ≤ config.EJECTION_BALANCE
  · have within := BeaconState.registryWithinLimit_of_lt
      (Nat.lt_trans before (by decide)) state
    have indexFits : index < 2 ^ 64 := Nat.lt_of_lt_of_le inside
      (Nat.le_trans within (Nat.le_of_lt preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt))
    have converted : ofNatChecked index = .ok index.toUInt64 := ofNatChecked_of_lt indexFits
    have indexValue : index.toUInt64.toNat = index := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt indexFits]
    obtain ⟨after, exited, slot, size, bounds⟩ :=
      initiateValidatorExit_exists_ok (config := config) before
        (state := updated) (index := index.toUInt64)
        (by simpa [updated, BeaconState.putValidator, indexValue] using inside)
        first updatedExits room
    refine ⟨after, ?_, slot, ?_, bounds⟩
    · simp only [updateRegistryEntry, liftAccessor, found, queuedOk, written, liftArith,
        converted, Except.mapError, bind, Except.bind]
      simp only [eject, ↓reduceIte, exited]
    · exact size.trans (sameSizes_putValidator state inside queued).1
  · refine ⟨updated, ?_, rfl, (sameSizes_putValidator state inside queued).1,
      updatedExits.mono (by omega)⟩
    simp only [updateRegistryEntry, liftAccessor, found, queuedOk, written,
      Except.mapError, bind, Except.bind]
    simp only [eject]; rfl

private theorem foldlM_updateRegistryEntry_exists_ok {config : Config} {ceiling : Nat}
    (before : fork < .pectra) (indices : List Nat) (state : BeaconState preset fork)
    (inside : ∀ index ∈ indices, index < state.validators.data.size)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ExitsBelow state ceiling)
    (room : ceiling + indices.length + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64) :
    ∃ after, indices.foldlM (updateRegistryEntry config) state = .ok after ∧
      after.slot = state.slot ∧ after.validators.data.size = state.validators.data.size ∧
      ExitsBelow after (ceiling + indices.length) := by
  induction indices generalizing state ceiling with
  | nil => exact ⟨state, rfl, rfl, rfl, by simpa using exits⟩
  | cons index rest ih =>
    obtain ⟨middle, step, slot, size, bounds⟩ :=
      updateRegistryEntry_exists_ok (config := config) before
        (inside index List.mem_cons_self) first exits
        (by simp only [List.length_cons] at room; omega)
    have current : getCurrentEpoch middle = getCurrentEpoch state := by simp [getCurrentEpoch, slot]
    obtain ⟨after, folded, lastSlot, lastSize, lastBounds⟩ := ih middle
      (ceiling := ceiling + 1) (fun i member => by rw [size]; exact inside i (by simp [member]))
      (by rw [current]; omega) bounds (by simp only [List.length_cons] at room; omega)
    refine ⟨after, ?_, lastSlot.trans slot, lastSize.trans size, ?_⟩
    · simp only [List.foldlM_cons, step, folded, bind, Except.bind]
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using lastBounds

private theorem activateValidator_exists_ok {state : BeaconState preset fork}
    {index : ValidatorIndex} {ceiling : Nat} (inside : index.toNat < state.validators.data.size)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ExitsBelow state ceiling) (room : ceiling < 2 ^ 64) :
    ∃ after, activateValidator state index = .ok after ∧
      after.slot = state.slot ∧ after.validators.data.size = state.validators.data.size ∧
      ExitsBelow after ceiling := by
  let validator := state.validators.data[index.toNat]
  have found : getValidator state index = .ok validator := by
    simp [getValidator, Array.getElem?_eq_getElem inside, validator]
  obtain ⟨epoch, epochOk, -⟩ := activationExitEpoch_exists_ok state ceiling first room
  let changed := { validator with activationEpoch := epoch }
  have written : state.setValidator index changed =
      .ok (state.putValidator index.toNat inside changed) := by
    simp [BeaconState.setValidator, inside]
  refine ⟨state.putValidator index.toNat inside changed, ?_, rfl,
    (sameSizes_putValidator state inside changed).1, ?_⟩
  · simp only [activateValidator, liftAccessor, found, liftArith, epochOk,
      Except.mapError, bind, Except.bind]
    change liftAccessor (state.setValidator index changed) = .ok _
    rw [written]
    rfl
  · exact exits.putValidator inside
      (fun finite => exits validator (Array.getElem_mem inside) finite)

private theorem foldlM_activateValidator_exists_ok (indices : List ValidatorIndex)
    (state : BeaconState preset fork) {ceiling : Nat}
    (inside : ∀ index ∈ indices, index.toNat < state.validators.data.size)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ExitsBelow state ceiling) (room : ceiling < 2 ^ 64) :
    ∃ after, indices.foldlM activateValidator state = .ok after ∧ ExitsBelow after ceiling := by
  induction indices generalizing state with
  | nil => exact ⟨state, rfl, exits⟩
  | cons index rest ih =>
    obtain ⟨middle, step, slot, size, bounds⟩ := activateValidator_exists_ok
      (inside index List.mem_cons_self) first exits room
    have current : getCurrentEpoch middle = getCurrentEpoch state := by simp [getCurrentEpoch, slot]
    obtain ⟨after, folded, lastBounds⟩ := ih middle
      (fun i member => by rw [size]; exact inside i (by simp [member]))
      (by rwa [current]) bounds
    exact ⟨after, by simp only [List.foldlM_cons, step, folded, bind, Except.bind], lastBounds⟩

/-- Before Electra, registry updates succeed with room for one epoch per validator and the delay.

The ceiling bounds both the first activation epoch and every existing finite exit epoch.

A finite exit epoch means a value other than `FAR_FUTURE_EPOCH`.

The step keeps each finite exit epoch at most the ceiling plus the registry size. -/
theorem processRegistryUpdates_total_of_lt_electra {config : Config}
    (state : BeaconState preset fork) (before : fork < .pectra) (ceiling : Nat)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (room : ceiling + state.validators.data.size +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64) :
    ∃ after, processRegistryUpdates config state = .ok after ∧
      ∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch.toNat ≤ ceiling + state.validators.data.size := by
  obtain ⟨registered, registeredOk, slot, -, bounds⟩ :=
    foldlM_updateRegistryEntry_exists_ok (config := config)
      before (List.range state.validators.data.size) state
      (fun _ member => List.mem_range.mp member) first exits (by simpa using room)
  have within := BeaconState.registryWithinLimit_of_lt
    (Nat.lt_trans before (by decide)) registered
  have queuedInside : ∀ index ∈ activationQueue registered,
      index.toNat < registered.validators.data.size := by
    intro index member
    have queued := activationEpochAt_of_mem_activationQueue within member
    unfold activationEpochAt at queued
    cases read : getValidator registered index with
    | error error => simp [read, Except.map] at queued
    | ok validator => exact (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp read)).1
  let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config registered
    else getValidatorChurnLimit config registered
  obtain ⟨after, activated, lastBounds⟩ := foldlM_activateValidator_exists_ok
    ((activationQueue registered).take limit.toNat) registered
    (fun index member => queuedInside index (List.mem_of_mem_take member))
    (ceiling := ceiling + state.validators.data.size)
    (by have current : getCurrentEpoch registered = getCurrentEpoch state := by
          simp [getCurrentEpoch, slot]
        rw [current]
        omega)
    (by simpa using bounds) (by omega)
  refine ⟨after, ?_, lastBounds⟩
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simp only [processRegistryUpdates, notElectra, ↓reduceIte, registeredOk, bind, Except.bind]
  exact activated

end EthLib.Consensus
