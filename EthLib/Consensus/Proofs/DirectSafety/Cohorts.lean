module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import Mathlib.Order.Interval.Finset.Nat

/-!
# Count bounds for pre-Electra cohorts

The count cap uses the whole registry, so it does not decrease along a run.

Along a run, activation cohorts change only at the registry pass, which fills one scheduled epoch.

Before Electra, keys that join over a window therefore weigh at most one capped cohort per epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}
  {fork : Fork} {state after : BeaconState preset fork}

open DirectSafety (cohortCap validatorChurnLimit_le_cohortCap)

private theorem cohortCap_mono {n m : Nat} (le : n ≤ m) :
    cohortCap config n ≤ cohortCap config m := by
  unfold cohortCap
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.div_le_div_right le) (Nat.le_max_right _ _)⟩

/-- Count validators whose selected epoch equals a finite cohort epoch. -/
def validatorCohort (field : Validator → Epoch) (state : BeaconState preset fork)
    (epoch : Epoch) : Nat :=
  state.validators.data.toList.countP fun v => field v == epoch

private theorem count_set_le {α : Type} (test : α → Bool) (xs : List α)
    (i : Nat) (value : α) (inside : i < xs.length) :
    (xs.set i value).countP test ≤ xs.countP test + 1 := by
  rw [List.countP_set inside]
  split <;> split <;> omega

private theorem validatorCohort_setValidatorAt_le {field : Validator → Epoch} {i : Nat}
    {v : Validator} (ok : state.setValidatorAt i v = .ok after) (epoch : Epoch) :
    validatorCohort field after epoch ≤ validatorCohort field state epoch + 1 := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  simp only [validatorCohort, BeaconState.putValidator,
    Serialization.Ssz.RootedForkList.data_set, Array.toList_set]
  exact count_set_le _ _ _ _ (by simpa using inside)

private theorem validatorCohort_setValidatorAt_eq {field : Validator → Epoch}
    {i : Nat} {old v : Validator} (found : getValidatorAt state i = .ok old)
    (ok : state.setValidatorAt i v = .ok after) (epoch : Epoch)
    (same : (field v == epoch) = (field old == epoch)) :
    validatorCohort field after epoch = validatorCohort field state epoch := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  have read : state.validators.data[i] = old := by
    simpa [getValidatorAt, inside] using found
  simp only [validatorCohort, BeaconState.putValidator,
    Serialization.Ssz.RootedForkList.data_set, Array.toList_set]
  rw [List.countP_set (by simpa using inside)]
  simp only [Array.getElem_toList, read, same]
  split
  · have positive : 0 < state.validators.data.toList.countP (fun v => field v == epoch) := by
      have member : old ∈ state.validators.data.toList := by
        simpa using read ▸ Array.getElem_mem inside
      have nonzero : state.validators.data.toList.countP (fun v => field v == epoch) ≠ 0 := by
        intro zero
        exact List.countP_eq_zero.mp zero old member (by assumption)
      omega
    omega
  · omega

private structure CohortsKept (s t : BeaconState preset fork) : Prop where
  activations : ∀ e, e ≠ FAR_FUTURE_EPOCH →
    validatorCohort Validator.activationEpoch t e = validatorCohort Validator.activationEpoch s e

private theorem CohortsKept.refl (s : BeaconState preset fork) :
    CohortsKept s s := ⟨fun _ _ => rfl⟩

private theorem CohortsKept.trans {s t u : BeaconState preset fork}
    (first : CohortsKept s t) (second : CohortsKept t u) :
    CohortsKept s u :=
  ⟨fun e finite => (second.activations e finite).trans (first.activations e finite)⟩

private theorem CohortsKept.of_data {s t : BeaconState preset fork}
    (same : t.validators.data = s.validators.data := by rfl) :
    CohortsKept s t := by
  constructor
  intro e _
  simp [validatorCohort, same]

private theorem CohortsKept.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    {xs : List α} (keeps : ∀ s a t, step s a = .ok t → CohortsKept s t)
    (ok : xs.foldlM step state = .ok after) : CohortsKept state after :=
  foldlM_ok_invariant (CohortsKept state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (.refl state) ok

private theorem CohortsKept.setValidatorAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old) (ok : state.setValidatorAt i v = .ok after)
    (activation : v.activationEpoch = old.activationEpoch) : CohortsKept state after :=
  ⟨fun e _ => validatorCohort_setValidatorAt_eq found ok e (by rw [activation])⟩

private theorem CohortsKept.setValidator {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old) (ok : state.setValidator i v = .ok after)
    (activation : v.activationEpoch = old.activationEpoch) : CohortsKept state after :=
  .setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) activation

private theorem CohortsKept.increaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance state i amount = .ok after) :
    CohortsKept state after :=
  .of_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem CohortsKept.decreaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance state i amount = .ok after) :
    CohortsKept state after :=
  .of_data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem cohorts_exit {i : ValidatorIndex}
    (ok : initiateValidatorExit config state i = .ok after) :
    CohortsKept state after := by
  constructor
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawable, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]
    exact fun _ _ => rfl
  · have same := (exitQueue_validators queue).1
    intro e _
    rw [validatorCohort_setValidatorAt_eq
      (field := Validator.activationEpoch) (old := v) (i := i.toNat)
      (v := { v with exitEpoch := epoch, withdrawableEpoch := withdrawable })
      (by rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]; exact found)
      (by rwa [← setValidator_eq_setValidatorAt]) e rfl]
    simp [validatorCohort, same]

private theorem cohorts_slash {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state i whistleblower = .ok after) :
    CohortsKept state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at ok
  obtain ⟨exited, exitedOk, v, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk, proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := ok
  have tail := (CohortsKept.decreaseBalance loweredOk).trans <|
    (CohortsKept.increaseBalance raisedOk).trans <|
    (CohortsKept.increaseBalance lastOk).trans
      (CohortsKept.of_data (t := after) (by rw [(slashValidator_last done).1]))
  refine (cohorts_exit exitedOk).trans <|
    (CohortsKept.setValidator found markedOk rfl).trans (CohortsKept.trans ?_ tail)
  exact .of_data rfl

private theorem cohorts_proposerSlashing {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    CohortsKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact cohorts_slash slashed

private theorem cohorts_slashIf
    {s t : BeaconState preset fork × Bool} {i : ValidatorIndex}
    (ok : slashIfSlashable config s i = .ok t) : CohortsKept s.1 t.1 := by
  rcases s with ⟨s, changed⟩
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact cohorts_slash slashed
  · cases ok
    exact .refl _

private theorem cohorts_attesterSlashing
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    CohortsKept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun s => CohortsKept state s.1)
    (fun _ _ _ h ok => h.trans (cohorts_slashIf ok)) (.refl state) folded

private theorem CohortsKept.append {v : Validator}
    (added : after.validators.data = state.validators.data.push v)
    (activation : v.activationEpoch = FAR_FUTURE_EPOCH) :
    CohortsKept state after := by
  have counts (field : Validator → Epoch) (pending : field v = FAR_FUTURE_EPOCH)
      (e : Epoch) (finite : e ≠ FAR_FUTURE_EPOCH) :
      validatorCohort field after e = validatorCohort field state e := by
    simp only [validatorCohort, added, Array.toList_push, List.countP_append, List.countP_cons,
      List.countP_nil, pending]
    have different : (FAR_FUTURE_EPOCH == e) = false := by
      simp only [beq_eq_false_iff_ne]
      exact Ne.symm finite
    simp [different]
  exact ⟨counts _ activation⟩

private theorem cohorts_admit {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} (ok : addValidatorToRegistry state key credentials amount = .ok after) :
    CohortsKept state after := by
  exact CohortsKept.append (addValidatorToRegistry_validators_eq_push ok) rfl

private theorem cohorts_deposit (early : fork < .pectra) {before : fork < .hegota}
    {deposit : Deposit} (ok : processDeposit config checks before state deposit = .ok after) :
    CohortsKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  refine (CohortsKept.of_data (s := state)
    (t := { state with eth1DepositIndex := fun _ => next }) rfl).trans ?_
  rcases applyDeposit_cases early applied with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact .refl _
  · exact .increaseBalance raised
  · exact cohorts_admit added

private theorem cohorts_attestation {parentSlot : Slot} {attestation : Attestation preset fork}
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    CohortsKept state after :=
  .of_data (congrArg (·.data) (processAttestation_registry ok).1)

private theorem cohorts_updateEntry {i : Nat}
    (ok : updateRegistryEntry config state i = .ok after) :
    CohortsKept state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, rest⟩ := ok
  have activation : queued.activationEpoch = v.activationEpoch := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      rfl
    · cases queue
      rfl
  have kept := CohortsKept.setValidatorAt found set activation
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok] at rest
    obtain ⟨_, _, exited⟩ := rest
    exact kept.trans (cohorts_exit exited)
  · cases rest
    exact kept

private theorem cohorts_credentials {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    CohortsKept state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact .setValidator found set rfl

/-- A pre-Electra block keeps the cohorts, read through master's decomposition of a block.

Cohorts depend only on the validators, so every step that keeps them keeps the cohorts. -/
private theorem cohorts_block (early : fork < .pectra) {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) :
    CohortsKept state after := by
  have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  have before : fork < .glamsterdam := Nat.lt_trans early (by decide)
  have noGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt before
  let Kept (a b : BeaconState preset fork) : Prop := CohortsKept a b
  have trans {a b c : BeaconState preset fork} (one : CohortsKept a b)
      (two : CohortsKept b c) : CohortsKept a c :=
    one.trans two
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : CohortsKept state input :=
    .of_data (congrArg (·.data) (OperationsInput.validators_eq before started))
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of Kept .refl trans (cohorts_deposit early)
      (fun exited => cohorts_exit (processVoluntaryExit_initiates exited))
      cohorts_credentials
      (fun {_ _ _ electra} _ => absurd electra.1 noElectra)
      (fun {_ _ gloas} _ => absurd gloas noGloas) operated
  have tail : CohortsKept last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact .of_data rfl
    · cases synced
      exact .refl _
  exact head.trans <|
    (CohortsKept.foldlM (fun _ _ _ ok => cohorts_proposerSlashing ok) proposersOk).trans <|
    (CohortsKept.foldlM (fun _ _ _ ok => cohorts_attesterSlashing ok) slashingsOk).trans <|
    (CohortsKept.foldlM (fun _ _ _ ok => cohorts_attestation ok) attestedOk).trans <|
    rest.trans tail

private theorem cohorts_effective (ok : processEffectiveBalanceUpdates state = .ok after) :
    CohortsKept state after := by
  unfold processEffectiveBalanceUpdates at ok
  refine CohortsKept.foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact .setValidatorAt found set rfl

/-- The next registry pass can only assign this activation epoch. -/
def scheduledActivationEpoch (state : BeaconState preset fork) : Nat :=
  (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat

/-- Non-genesis activation cohorts are bounded and precede the next registry pass. -/
private structure ActivationCohortBound (config : Config) (state : BeaconState preset fork) : Prop where
  count : ∀ e, e ≠ FAR_FUTURE_EPOCH → e ≠ GENESIS_EPOCH →
    validatorCohort Validator.activationEpoch state e ≤
      cohortCap config state.validators.data.size
  scheduled : ∀ v ∈ state.validators.data, v.activationEpoch ≠ FAR_FUTURE_EPOCH →
    v.activationEpoch.toNat < scheduledActivationEpoch state

private theorem cohorts_activate {i : ValidatorIndex}
    (ok : activateValidator state i = .ok after) (e : Epoch) :
    validatorCohort Validator.activationEpoch after e ≤
      validatorCohort Validator.activationEpoch state e +
        if e.toNat = scheduledActivationEpoch state then 1 else 0 := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at ok
  obtain ⟨v, found, epoch, epochOk, set⟩ := ok
  have assigned := (computeActivationExitEpoch_ok_iff.mp epochOk).2
  have write := set
  rw [setValidator_eq_setValidatorAt] at write
  by_cases same : e.toNat = scheduledActivationEpoch state
  · simp only [same, ↓reduceIte]
    exact validatorCohort_setValidatorAt_le write e
  · simp only [same, ↓reduceIte, Nat.add_zero]
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok write
    have different : epoch ≠ e := by
      intro equal
      apply same
      rw [← equal, assigned]
      rfl
    simp only [validatorCohort, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, Array.toList_set]
    rw [List.countP_set (by simpa using inside)]
    have no : (epoch == e) = false := by simpa only [beq_eq_false_iff_ne] using different
    simp only [no, Bool.false_eq_true, ↓reduceIte]
    split <;> omega

private theorem cohorts_activate_many :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.foldlM activateValidator state = .ok after → ∀ e,
        validatorCohort Validator.activationEpoch after e ≤
          validatorCohort Validator.activationEpoch state e +
            if e.toNat = scheduledActivationEpoch state then indices.length else 0
  | [], _, _, ok => by
    cases ok
    exact fun _ => by simp
  | i :: rest, state, after, ok => by
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, tail⟩ := ok
    have same : scheduledActivationEpoch middle = scheduledActivationEpoch state := by
      unfold scheduledActivationEpoch getCurrentEpoch
      rw [(frame_activateValidator first).slot]
    intro e
    have h := cohorts_activate_many tail e
    rw [same] at h
    have k := cohorts_activate first e
    split at h <;> simp_all only [↓reduceIte, List.length_cons] <;> omega

/-- A registry pass only increases the scheduled activation cohort, by at most count churn. -/
private theorem activationCohort_processRegistryUpdates (early : fork < .pectra)
    (ok : processRegistryUpdates config state = .ok after) (e : Epoch)
    (finite : e ≠ FAR_FUTURE_EPOCH) :
    validatorCohort Validator.activationEpoch after e ≤
      validatorCohort Validator.activationEpoch state e +
        if e.toNat = scheduledActivationEpoch state then
          cohortCap config state.validators.data.size else 0 := by
  have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  simp only [processRegistryUpdates, noElectra, ↓reduceIte, bind_ok_iff] at ok
  obtain ⟨updated, pass, activated⟩ := ok
  have kept := CohortsKept.foldlM
    (fun _ _ _ ok => cohorts_updateEntry ok) pass
  have sizes := foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_updateRegistryEntry step))
    (SameSizes.refl state) pass
  have slot := foldlM_ok_invariant (fun next : BeaconState preset fork => next.slot = state.slot)
    (fun _ _ _ h step => (updateRegistryEntry_activationEpochs step).1.trans h) rfl pass
  have same : scheduledActivationEpoch updated = scheduledActivationEpoch state := by
    simp only [scheduledActivationEpoch, getCurrentEpoch, slot]
  have bound := cohorts_activate_many activated e
  rw [kept.activations e finite, same] at bound
  have limit : (if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
      else getValidatorChurnLimit config updated).toNat ≤
      cohortCap config state.validators.data.size := by
    have churn := validatorChurnLimit_le_cohortCap (config := config) updated _
      (Nat.le_of_eq sizes.1)
    split
    · exact Nat.le_trans (getValidatorActivationChurnLimit_le).2 churn
    · exact churn
  have taken := List.length_take_le
    (if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
      else getValidatorChurnLimit config updated).toNat
    (activationQueue updated)
  split at bound <;> simp_all only [↓reduceIte]
  omega

/-- The activation pass fills an empty future cohort; its count cap needs no positivity. -/
private theorem activationCohortBound_registry_count (early : fork < .pectra)
    (ok : processRegistryUpdates config state = .ok after)
    (bounded : ActivationCohortBound config state) (e : Epoch)
    (finite : e ≠ FAR_FUTURE_EPOCH) (nonGenesis : e ≠ GENESIS_EPOCH) :
    validatorCohort Validator.activationEpoch after e ≤
      cohortCap config after.validators.data.size := by
  have bound := activationCohort_processRegistryUpdates early ok e finite
  rw [(sameSizes_processRegistryUpdates ok).1]
  by_cases scheduled : e.toNat = scheduledActivationEpoch state
  · have empty : validatorCohort Validator.activationEpoch state e = 0 := by
      apply List.countP_eq_zero.mpr
      intro v member
      have member' : v ∈ state.validators.data := by simpa using member
      simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
      intro equal
      have before := bounded.scheduled v member' (equal ▸ finite)
      rw [equal, scheduled] at before
      exact Nat.lt_irrefl _ before
    simpa only [scheduled, ↓reduceIte, empty, Nat.zero_add] using bound
  · simp only [scheduled, ↓reduceIte, Nat.add_zero] at bound
    exact Nat.le_trans bound (bounded.count e finite nonGenesis)

/-- Registry activation reaches, but never passes, the epoch reserved for this pass. -/
private theorem activationCohortBound_registry_scheduled (early : fork < .pectra)
    (ok : processRegistryUpdates config state = .ok after)
    (bounded : ActivationCohortBound config state) {v : Validator}
    (member : v ∈ after.validators.data) (finite : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    v.activationEpoch.toNat ≤ scheduledActivationEpoch state := by
  apply Classical.byContradiction
  intro beyond
  have empty : validatorCohort Validator.activationEpoch state v.activationEpoch = 0 := by
    apply List.countP_eq_zero.mpr
    intro w present
    simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
    intro equal
    have h := bounded.scheduled w (by simpa using present) (equal ▸ finite)
    rw [equal] at h
    omega
  have bound := activationCohort_processRegistryUpdates early ok v.activationEpoch finite
  have different : v.activationEpoch.toNat ≠ scheduledActivationEpoch state := by omega
  simp only [different, ↓reduceIte, empty, Nat.add_zero, Nat.le_zero] at bound
  have absent := List.countP_eq_zero.mp bound v (by simpa using member)
  exact absent (by simp)

/-- An epoch is cut at its registry updates, the only stage that assigns cohort epochs.

The three stages before them keep the validators and the slot.

After them, every stage keeps the cohorts, and the registry does not shrink. -/
private theorem cohorts_epoch (early : fork < .pectra)
    (ok : processEpoch config checks state = .ok after) :
    ∃ before registered : BeaconState preset fork,
      CohortsKept state before ∧
      processRegistryUpdates config before = .ok registered ∧
      CohortsKept registered after ∧
      before.slot = state.slot ∧ before.validators.data.size = state.validators.data.size ∧
      registered.validators.data.size ≤ after.validators.data.size := by
  have trace := processEpoch_trace ok
  change EpochTrace _ ([.justification, .inactivity, .rewards] ++ (.registry ::
    ([.slashings, .eth1Reset, .pendingDeposits, .pendingConsolidations] ++
      EpochStage.middleStages ++ EpochStage.tailStages))) _ _ at trace
  obtain ⟨before, head, tail⟩ := EpochTrace.append_iff.mp trace
  cases tail
  rename_i registered registeredOk tail
  have first : before.validators = state.validators ∧ before.slot = state.slot := by
    refine EpochTrace.transport
      (R := fun a b : BeaconState preset fork => b.validators = a.validators ∧ b.slot = a.slot)
      (fun _ => ⟨rfl, rfl⟩) (fun one two => ⟨two.1.trans one.1, two.2.trans one.2⟩) ?_ head
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    cases k
    case justification =>
      refine ⟨edge.validators_eq ⟨nofun, nofun, nofun⟩, ?_⟩
      obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok edge
      · subst same; rfl
      · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
        rw [← rest]
    case inactivity =>
      refine ⟨edge.validators_eq ⟨nofun, nofun, nofun⟩, ?_⟩
      simp only [EpochStage.Edge] at edge
      split at edge
      · exact (frame_processInactivityUpdates edge).slot
      · exact edge ▸ rfl
    case rewards =>
      exact ⟨edge.validators_eq ⟨nofun, nofun, nofun⟩, (frame_processRewardsAndPenalties edge).slot⟩
    all_goals simp at member
  have last : CohortsKept registered after ∧
      registered.validators.data.size ≤ after.validators.data.size := by
    refine EpochTrace.transport (R := fun a b : BeaconState preset fork =>
        CohortsKept a b ∧ a.validators.data.size ≤ b.validators.data.size)
      (fun a => ⟨.refl a, Nat.le_refl _⟩)
      (fun one two => ⟨one.1.trans two.1, Nat.le_trans one.2 two.2⟩)
      ?_ tail
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    cases k
    case justification | inactivity | rewards | registry =>
      simp [EpochStage.middleStages, EpochStage.tailStages] at member
    -- Pending deposits start at Electra, so before it they are the identity.
    case pendingDeposits =>
      have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
      simp only [EpochStage.Edge, noElectra, ↓reduceDIte] at edge
      exact edge ▸ ⟨.refl _, Nat.le_refl _⟩
    case effectiveBalances =>
      exact ⟨cohorts_effective edge,
        (registryLifecycle_processEffectiveBalanceUpdates edge).size_le⟩
    all_goals
      have same := edge.validators_eq ⟨nofun, nofun, nofun⟩
      exact ⟨.of_data (congrArg (·.data) same), Nat.le_of_eq (congrArg (·.data.size) same).symm⟩
  exact ⟨before, registered, .of_data (congrArg (·.data) first.1),
    EpochStage.action_cases.mp registeredOk, last.1, first.2, congrArg (·.data.size) first.1,
    last.2⟩

private theorem activationScheduled_of_counts {s t : BeaconState preset fork} {bound : Nat}
    (counts : ∀ e, e ≠ FAR_FUTURE_EPOCH →
      validatorCohort Validator.activationEpoch t e = validatorCohort Validator.activationEpoch s e)
    (scheduled : ∀ v ∈ s.validators.data, v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      v.activationEpoch.toNat < bound) :
    ∀ v ∈ t.validators.data, v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      v.activationEpoch.toNat < bound := by
  intro v member finite
  apply Classical.byContradiction
  intro late
  have empty : validatorCohort Validator.activationEpoch s v.activationEpoch = 0 := by
    apply List.countP_eq_zero.mpr
    intro w present
    simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
    intro equal
    have h := scheduled w (by simpa using present) (equal ▸ finite)
    rw [equal] at h
    exact late h
  have zero := (counts v.activationEpoch finite).trans empty
  exact List.countP_eq_zero.mp zero v (by simpa using member) (by simp)

/-- An epoch pass keeps the activation cap and fills at most the next scheduled epoch. -/
private theorem activationCohortBound_processEpoch (early : fork < .pectra)
    (ok : processEpoch config checks state = .ok after)
    (bounded : ActivationCohortBound config state) :
    (∀ e, e ≠ FAR_FUTURE_EPOCH → e ≠ GENESIS_EPOCH →
      validatorCohort Validator.activationEpoch after e ≤
        cohortCap config after.validators.data.size) ∧
    (∀ v ∈ after.validators.data, v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      v.activationEpoch.toNat ≤ scheduledActivationEpoch state) := by
  obtain ⟨before, registered, head, registeredOk, tail, slot, size, grow⟩ :=
    cohorts_epoch early ok
  have same : scheduledActivationEpoch before = scheduledActivationEpoch state := by
    simp only [scheduledActivationEpoch, getCurrentEpoch, slot]
  have atRegistry : ActivationCohortBound config before := by
    constructor
    · intro e finite nonGenesis
      rw [head.activations e finite, size]
      exact bounded.count e finite nonGenesis
    · rw [same]
      exact activationScheduled_of_counts head.activations bounded.scheduled
  constructor
  · intro e finite nonGenesis
    rw [tail.activations e finite]
    have bound :=
      activationCohortBound_registry_count early registeredOk atRegistry e finite nonGenesis
    exact Nat.le_trans bound (cohortCap_mono grow)
  · have scheduled : ∀ v ∈ registered.validators.data,
        v.activationEpoch ≠ FAR_FUTURE_EPOCH →
        v.activationEpoch.toNat < scheduledActivationEpoch state + 1 := by
      intro v member finite
      have h := activationCohortBound_registry_scheduled early registeredOk atRegistry member finite
      rw [same] at h
      omega
    intro v member finite
    have h := activationScheduled_of_counts tail.activations scheduled v member finite
    omega

/-- Slot advancement restores the strict scheduling bound after an epoch pass. -/
private theorem activationCohortBound_advanceSlot (early : fork < .pectra)
    (ok : advanceSlot config checks state = .ok after)
    (bounded : ActivationCohortBound config state) : ActivationCohortBound config after := by
  obtain ⟨next, cached, epoched, nextOk, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have cachedData : cached.validators.data = state.validators.data := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have cachedSlot : cached.slot = state.slot := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have atCached : ActivationCohortBound config cached := by
    constructor
    · simpa only [validatorCohort, cachedData] using bounded.count
    · simpa only [scheduledActivationEpoch, getCurrentEpoch, cachedData, cachedSlot]
        using bounded.scheduled
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have result := activationCohortBound_processEpoch early epochedOk atCached
    constructor
    · exact result.1
    · intro v member finite
      have h := result.2 v member finite
      have epochs := nextSlot_epoch_of_boundary nextOk boundary
      simp only [scheduledActivationEpoch, getCurrentEpoch, computeEpochAtSlot,
        UInt64.toNat_div, cachedSlot] at h ⊢
      omega
  · rename_i inside
    cases epochedOk
    constructor
    · exact atCached.count
    · intro v member finite
      have h := atCached.scheduled v member finite
      have epochs := nextSlot_epoch_of_inside nextOk inside
      simp only [scheduledActivationEpoch, getCurrentEpoch, computeEpochAtSlot,
        UInt64.toNat_div, cachedSlot] at h ⊢
      omega

/-- Blocks leave finite activation cohorts unchanged, while the registry may grow. -/
private theorem activationCohortBound_processBlock (early : fork < .pectra)
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after)
    (bounded : ActivationCohortBound config state) : ActivationCohortBound config after := by
  have kept := cohorts_block early ok
  have frame := frame_processBlock ok
  constructor
  · intro e finite nonGenesis
    rw [kept.activations e finite]
    exact Nat.le_trans (bounded.count e finite nonGenesis)
      (cohortCap_mono frame.registryGrows)
  · have same : scheduledActivationEpoch after = scheduledActivationEpoch state := by
      simp only [scheduledActivationEpoch, getCurrentEpoch, frame.slot]
    rw [same]
    exact activationScheduled_of_counts kept.activations bounded.scheduled

private theorem ActivationCohortBound.of_data {f h : Fork}
    {s : BeaconState preset f} {t : BeaconState preset h}
    (same : t.validators.data = s.validators.data) (slot : t.slot = s.slot)
    (bounded : ActivationCohortBound config s) : ActivationCohortBound config t := by
  constructor
  · simpa only [validatorCohort, same] using bounded.count
  · simpa only [scheduledActivationEpoch, getCurrentEpoch, same, slot] using bounded.scheduled

private theorem activationCohortBound_upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .pectra)
    (bounded : ActivationCohortBound config s.state) :
    ActivationCohortBound config t.val.state := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact .of_data (s := state) (upgradeToAltair_spec upgraded).1
      (upgradeFrame_upgradeToAltair upgraded).slot bounded
  · subst ok; exact .of_data (s := state) rfl rfl bounded
  · subst ok; exact .of_data (s := state) rfl rfl bounded
  · subst ok; exact .of_data (s := state) rfl rfl bounded
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.fusaka < Fork.pectra) early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.glamsterdam < Fork.pectra) early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.pectra) early)

private theorem activationCohortBound_upgrades {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .pectra)
    (bounded : ActivationCohortBound config s.state) : ActivationCohortBound config t.state := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact ih next rest early (activationCohortBound_upgrade nextOk
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early) bounded)
  | case2 s notDue => cases ok; exact bounded

/-- A concrete pre-Electra step keeps activation counts and their scheduling bound. -/
private theorem Step.activationCohortBound {s t : ForkedBeaconState preset}
    (step : Step config checks s t) (early : t.fork < .pectra)
    (bounded : ActivationCohortBound config s.state) : ActivationCohortBound config t.state := by
  cases step with
  | block engine signed due ok =>
    exact activationCohortBound_processBlock early (applySignedBlock_ok ok).2.1 bounded
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact activationCohortBound_upgrades upgrades early (activationCohortBound_advanceSlot
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le upgrades) early) slotOk bounded)

/-- A pre-Electra run bounds activation cohorts even when count churn is zero. -/
private theorem Run.activationCohortBound {s t : ForkedBeaconState preset}
    (run : Run config checks s t) (early : t.fork < .pectra)
    (bounded : ActivationCohortBound config s.state) : ActivationCohortBound config t.state := by
  induction run with
  | nil => exact bounded
  | snoc pre step ih =>
    exact step.activationCohortBound early (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early))

/-- Genesis activates validators only at epoch zero; all other finite cohorts are empty. -/
private theorem Genesis.activationCohortBound {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ActivationCohortBound config g.state := by
  obtain ⟨hash, time, deposits, ok⟩ := genesis
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    equal⟩ := initializeBeaconStateFromEth1_ok ok
  have first := CohortsKept.foldlM (fun s entry t computed => by
    simp only [genesisDeposit, bind_ok_iff] at computed
    obtain ⟨root, _, deposited⟩ := computed
    exact (CohortsKept.of_data (s := s)
      (t := { s with eth1Data := fun _ => { s.eth1Data (Nat.lt_trans before (by decide)) with
        depositRoot := root } }) rfl).trans
      (cohorts_deposit (Nat.lt_trans before (by decide)) deposited)) depositedOk
  have initial : ∀ e, e ≠ FAR_FUTURE_EPOCH → e ≠ GENESIS_EPOCH →
      validatorCohort Validator.activationEpoch deposited e = 0 := by
    intro e finite _
    rw [first.activations e finite]
    simp [validatorCohort, emptyGenesisState]
  have last := foldlM_ok_invariant
    (fun s : BeaconState preset g.fork => ∀ e, e ≠ FAR_FUTURE_EPOCH → e ≠ GENESIS_EPOCH →
      validatorCohort Validator.activationEpoch s e = 0)
    (fun s i t bounded computed => by
      simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨v, found, _, _, set⟩ := computed
      intro e finite nonGenesis
      have absent : (v.activationEpoch == e) = false := by
        have zero := bounded e finite nonGenesis
        have mem := mem_of_getValidatorAt found
        exact Bool.eq_false_iff.mpr (List.countP_eq_zero.mp zero v (by simpa using mem))
      rw [validatorCohort_setValidatorAt_eq (field := Validator.activationEpoch) found set e
        (by
          split
          · rw [absent]
            exact beq_eq_false_iff_ne.mpr (Ne.symm nonGenesis)
          · rfl)]
      exact bounded e finite nonGenesis) initial activatedOk
  rw [equal]
  constructor
  · intro e finite nonGenesis
    exact Nat.le_trans (Nat.le_of_eq (last e finite nonGenesis)) (Nat.zero_le _)
  · intro v member finite
    have genesisEpoch : v.activationEpoch = GENESIS_EPOCH := by
      apply Classical.byContradiction
      intro other
      exact List.countP_eq_zero.mp (last v.activationEpoch finite other) v
        (by simpa using member) (by simp)
    simp only [genesisEpoch, GENESIS_EPOCH, UInt64.toNat_zero, scheduledActivationEpoch]
    omega

/-! ## The joining stake before Electra -/

namespace DirectSafety

private theorem effectiveWeight_le_cap {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (early : x.fork < .pectra) (key : Cryptography.Bls.BLSPubkey) :
    effectiveWeight x.state key ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
  have capped := run.effectiveBalance_capped genesis caps.activation caps.compounding
    (Nat.lt_trans early (by decide))
  unfold effectiveWeight
  cases found : x.state.validators.data.toList.find? (fun v => v.pubkey == key) with
  | none => simp
  | some v =>
    have member := List.mem_of_find?_eq_some found
    have bound := capped v (by simpa using member)
    have noElectra : ¬ Fork.pectra ≤ x.fork := Nat.not_le_of_lt early
    simpa [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, noElectra] using
      (UInt64.le_iff_toNat_le.mp bound)

private theorem count_epoch_window (vs : List Validator) (field : Validator → Epoch)
    (lo hi cap : Nat)
    (bounded : ∀ n ∈ Finset.Ioc lo hi, vs.countP (fun v => (field v).toNat == n) ≤ cap) :
    (vs.filter fun v => lo < (field v).toNat && (field v).toNat ≤ hi).length ≤ (hi - lo) * cap := by
  classical
  have partition : ∀ xs : List Validator,
      (xs.filter fun v => lo < (field v).toNat && (field v).toNat ≤ hi).length =
        ∑ n ∈ Finset.Ioc lo hi, xs.countP (fun v => (field v).toNat == n) := by
    intro xs
    induction xs with
    | nil => simp
    | cons v xs ih =>
      simp only [List.countP_cons, Finset.sum_add_distrib]
      have singleton : (∑ n ∈ Finset.Ioc lo hi, if (field v).toNat == n then 1 else 0) =
          if lo < (field v).toNat ∧ (field v).toNat ≤ hi then 1 else 0 := by
        by_cases member : (field v).toNat ∈ Finset.Ioc lo hi
        · rw [Finset.sum_eq_single (field v).toNat]
          · simp [Finset.mem_Ioc.mp member]
          · intro n _ different
            simp [Ne.symm different]
          · exact fun absent => False.elim (absent member)
        · rw [Finset.sum_eq_zero (fun n inside => by
            have different : (field v).toNat ≠ n := fun same => member (same ▸ inside)
            simp [different])]
          simp only [Finset.mem_Ioc] at member
          simp [member]
      rw [singleton]
      by_cases inside : lo < (field v).toNat ∧ (field v).toNat ≤ hi
      · simp [inside.1, inside.2, ih, Nat.add_comm]
      · have no : ¬ (lo < (field v).toNat && (field v).toNat ≤ hi) := by simpa using inside
        simp [no, ih, inside]
  rw [partition]
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc lo hi, cap := Finset.sum_le_sum bounded
    _ = (hi - lo) * cap := by simp

private theorem new_recent_key_activation {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .pectra)
    {key : Cryptography.Bls.BLSPubkey} (member : key ∈ recentKeys y.state \ recentKeys x.state) :
    ∃ v ∈ y.state.validators.data.toList, v.pubkey = key ∧
      (getCurrentEpoch x.state).toNat < v.activationEpoch.toNat ∧
      v.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat := by
  classical
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨recent, absent⟩ := Finset.mem_sdiff.mp member
  obtain ⟨recent, unslashed⟩ := Finset.mem_filter.mp recent
  -- A key slashed at the reference would still be slashed now, so it is unslashed there too.
  have unslashedX : ¬ SlashedAt x.state key := fun slashed =>
    unslashed (slashedAt_forward tail slashed)
  have witness : ∃ (i : Nat) (w : Validator), y.state.validators.data[i]? = some w ∧
      w.pubkey = key ∧ (isActiveValidator w (getCurrentEpoch y.state) = true ∨
        isActiveValidator w (getPreviousEpoch y.state) = true) := by
    rcases Finset.mem_union.mp recent with h | h
    · obtain ⟨i, w, found, same, active⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact ⟨i, w, found, same, Or.inl active⟩
    · obtain ⟨i, w, found, same, active⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact ⟨i, w, found, same, Or.inr active⟩
  obtain ⟨i, v, found, keyEq, active⟩ := witness
  have inactive (e : Epoch) (le : e ≤ getCurrentEpoch x.state)
      (selected : e = getCurrentEpoch x.state ∨ e = getPreviousEpoch x.state) :
      ¬ isActiveValidator v e = true := by
    intro h
    have kept := activeKept_of_chainSteps tail.chainSteps e
      (UInt64.le_trans le (getCurrentEpoch_le_activityFixedEpoch _)) i
    have oldActive : isActiveAt x.state e i = true := by
      rw [← kept]
      simp [isActiveAt, found, h]
    obtain ⟨old, oldFound, oldActive⟩ := isActiveAt_eq_true_iff.mp oldActive
    obtain ⟨later, laterFound, same⟩ := validators_getElem?_of_validatorKeys_prefix
      (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 oldFound
    have equal : later = v := Option.some.inj (laterFound.symm.trans found)
    have member := (mem_keysAt_epoch (Nat.lt_trans xEarly (by decide)) e key).mpr
      ⟨i, old, oldFound, same.symm.trans (equal ▸ keyEq), oldActive⟩
    apply absent
    refine Finset.mem_filter.mpr ⟨?_, unslashedX⟩
    rcases selected with rfl | rfl
    · exact Finset.mem_union_left _ member
    · exact Finset.mem_union_right _ member
  have now := inactive _ (UInt64.le_refl _) (Or.inl rfl)
  have prev := inactive _ (getPreviousEpoch_le _) (Or.inr rfl)
  have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have px := getPreviousEpoch_toNat x.state
  have py := getPreviousEpoch_toNat y.state
  refine ⟨v, by simpa using Array.mem_of_getElem? found, keyEq, ?_⟩
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active now prev
  rcases active with h | h <;> omega

private theorem carry_key_same_epoch {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .pectra)
    {key : Cryptography.Bls.BLSPubkey}
    (member : key ∈ (recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) :
    getCurrentEpoch y.state = getCurrentEpoch x.state := by
  have ⟨_, _, _, initialized⟩ := genesis
  classical
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨both, absent⟩ := Finset.mem_sdiff.mp member
  obtain ⟨⟨i, old, found, keyEq, activation, exit⟩, _⟩ :=
    (mem_boundary_iff x.state (Nat.lt_trans xEarly (by decide))
      ((validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
      shared.chainSteps).2) key).mp
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp both).2, absent⟩)
  obtain ⟨v, current, kept⟩ := tail.registryLifecycle.validators i old found
  have assigned : old.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro h
    exact getCurrentEpoch_ne_farFuture twoSlots x.state
      ((UInt64.toNat_inj.mp exit).symm.trans h)
  have exitSame := kept.exitEpoch assigned
  obtain ⟨w, wFound, wKey⟩ := validators_getElem?_of_validatorKeys_prefix
      (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 found
  have equal : w = v := Option.some.inj (wFound.symm.trans current)
  have vKey : v.pubkey = key := equal ▸ wKey.trans keyEq
  have active : isActiveValidator v (getCurrentEpoch y.state) = true ∨
      isActiveValidator v (getPreviousEpoch y.state) = true := by
    have recent := (Finset.mem_filter.mp (Finset.mem_inter.mp both).1).1
    have unique := (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
      (shared.append tail).chainSteps).2
    have identify {j : Nat} {z : Validator} (zFound : y.state.validators.data[j]? = some z)
        (zKey : z.pubkey = key) : z = v := by
      obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp current
      obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp zFound
      have eq : j = i := unique.eq_of_getElem_eq
        (by simpa [validatorKeys] using hj) (by simpa [validatorKeys] using hi)
        (by simpa [validatorKeys] using zKey.trans vKey.symm)
      subst j
      rfl
    rcases Finset.mem_union.mp recent with h | h
    · obtain ⟨j, z, zFound, zKey, h⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact Or.inl (identify zFound zKey ▸ h)
    · obtain ⟨j, z, zFound, zKey, h⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact Or.inr (identify zFound zKey ▸ h)
  have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have py := getPreviousEpoch_toNat y.state
  have exitNat := congrArg UInt64.toNat exitSame
  apply UInt64.toNat_inj.mp
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
  rcases active with h | h <;> omega

/-- New recent keys use only activation cohorts, including when their count cap is zero. -/
private theorem new_recent_before_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (early : y.fork < .pectra) :
    Models.stake (effectiveWeight y.state) (recentKeys y.state \ recentKeys x.state) ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        cohortCap config y.state.validators.data.size * preset.MAX_EFFECTIVE_BALANCE.toNat := by
  classical
  let activated := y.state.validators.data.toList.filter fun v =>
    (getCurrentEpoch x.state).toNat < v.activationEpoch.toNat &&
      v.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat
  have subset : recentKeys y.state \ recentKeys x.state ⊆
      (activated.map (·.pubkey)).toFinset := by
    intro key member
    obtain ⟨v, present, keyEq, lower, upper⟩ := new_recent_key_activation tail early member
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨v, List.mem_filter.mpr ⟨present, by simp [lower, upper]⟩, keyEq⟩)
  have cohorts := (shared.append tail).activationCohortBound early genesis.activationCohortBound
  have count : activated.length ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        cohortCap config y.state.validators.data.size := by
    apply count_epoch_window
    intro n member
    obtain ⟨lower, upper⟩ := Finset.mem_Ioc.mp member
    have small : n < 2 ^ 64 := lt_of_le_of_lt upper (UInt64.toNat_lt _)
    have numeric : n.toUInt64.toNat = n := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
    have finite : n.toUInt64 ≠ FAR_FUTURE_EPOCH := by
      intro equal
      have far : n = 2 ^ 64 - 1 := by
        have h := congrArg UInt64.toNat equal
        rw [numeric] at h
        exact h
      have current := getCurrentEpoch_ne_farFuture twoSlots y.state
      have currentNat := UInt64.toNat_lt (getCurrentEpoch y.state)
      apply current
      apply UInt64.toNat_inj.mp
      change _ = 2 ^ 64 - 1
      omega
    have nonzero : n.toUInt64 ≠ GENESIS_EPOCH := by
      intro equal
      have h := congrArg UInt64.toNat equal
      rw [numeric] at h
      change n = 0 at h
      omega
    have bound := cohorts.count n.toUInt64 finite nonzero
    have predicates : (fun v : Validator => v.activationEpoch.toNat == n) =
        (fun v => v.activationEpoch == n.toUInt64) := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, ← UInt64.toNat_inj, numeric]
    simpa only [predicates, validatorCohort] using bound
  have cards := (Finset.card_le_card subset).trans
    (List.toFinset_card_le (activated.map (·.pubkey)))
  simp only [List.length_map] at cards
  unfold Models.stake
  calc
    _ ≤ ∑ _key ∈ recentKeys y.state \ recentKeys x.state,
        preset.MAX_EFFECTIVE_BALANCE.toNat :=
      Finset.sum_le_sum (fun key _ =>
        effectiveWeight_le_cap (shared.append tail) genesis caps early key)
    _ = (recentKeys y.state \ recentKeys x.state).card *
        preset.MAX_EFFECTIVE_BALANCE.toNat := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (cards.trans count)

/-- Separate new activation cohorts from reference previous-only stake without a positive cap. -/
theorem joining_before_electra_split {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (early : y.fork < .pectra) :
    Models.stake (effectiveWeight y.state) (recentKeys y.state \ recentKeys x.state) ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        cohortCap config y.state.validators.data.size * preset.MAX_EFFECTIVE_BALANCE.toNat ∧
    Models.stake (effectiveWeight y.state)
      ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) ≤ boundaryStake x := by
  have ⟨_, _, _, initialized⟩ := genesis
  classical
  refine ⟨new_recent_before_electra shared tail genesis twoSlots caps early, ?_⟩
  have uniqueX := (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
      shared.chainSteps).2
  have uniqueY := (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
      (shared.append tail).chainSteps).2
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have pointwise (key : Cryptography.Bls.BLSPubkey)
      (member : key ∈ (recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) :
      effectiveWeight y.state key ≤ effectiveWeight x.state key := by
    have same := carry_key_same_epoch shared tail genesis twoSlots early member
    obtain ⟨both, absent⟩ := Finset.mem_sdiff.mp member
    obtain ⟨⟨i, old, found, keyEq, _⟩, _⟩ :=
      (mem_boundary_iff x.state (Nat.lt_trans xEarly (by decide)) uniqueX key).mp
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp both).2, absent⟩)
    obtain ⟨v, current, vKey⟩ := validators_getElem?_of_validatorKeys_prefix
      (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 found
    have bound := tail.effectiveAt_le_of_same_epoch early same i
      (Array.getElem?_eq_some_iff.mp found).1
    have oldWeight := effectiveWeight_of_member uniqueX
      (by simpa using Array.mem_of_getElem? found)
    have newWeight := effectiveWeight_of_member uniqueY
      (by simpa using Array.mem_of_getElem? current)
    rw [keyEq] at oldWeight
    rw [vKey, keyEq] at newWeight
    rw [oldWeight, newWeight]
    simpa [effectiveAt, found, current] using bound
  unfold boundaryStake Models.stake
  exact (Finset.sum_le_sum pointwise).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro key member
        exact Finset.mem_sdiff.mpr
          ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp member).1).2,
            (Finset.mem_sdiff.mp member).2⟩)
      (by intros; exact Nat.zero_le _))

end DirectSafety

end EthLib.Consensus
