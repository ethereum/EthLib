module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Count bounds for pre-Electra cohorts

The count cap uses the whole registry, so it does not decrease along a run.

Along a run, activation cohorts change only at the registry pass, which fills one scheduled epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}
  {fork : Fork} {state after : BeaconState preset fork}

/-- A registry-size bound on the validator-count churn limit. -/
def registryChurnCap (config : Config) (size : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT.toNat (size / config.CHURN_LIMIT_QUOTIENT.toNat)

private theorem registryChurnCap_mono {n m : Nat} (le : n ≤ m) :
    registryChurnCap config n ≤ registryChurnCap config m := by
  unfold registryChurnCap
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.div_le_div_right le) (Nat.le_max_right _ _)⟩

private theorem validatorChurnLimit_le_registryChurnCap :
    (getValidatorChurnLimit config state).toNat ≤
      registryChurnCap config state.validators.data.size := by
  have count : (getActiveValidatorIndices state (getCurrentEpoch state)).length ≤
      state.validators.data.size := by
    exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)
  have converted : (getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64.toNat ≤
      state.validators.data.size := by
    change _ % 2 ^ 64 ≤ _
    exact Nat.le_trans (Nat.mod_le _ _) count
  unfold getValidatorChurnLimit registryChurnCap
  rw [Uint64.toNat_max, UInt64.toNat_div]
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.div_le_div_right converted) (Nat.le_max_right _ _)⟩

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

private theorem cohorts_pendingDeposit {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks state deposit = .ok after) :
    CohortsKept state after := by
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok
      exact .refl _
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · exact cohorts_admit ok
      · cases ok
        exact .refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact .increaseBalance ok

private theorem cohorts_deposit (early : fork < .pectra) {before : fork < .hegota}
    {deposit : Deposit} (ok : processDeposit config checks before state deposit = .ok after) :
    CohortsKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  simp only [applyDeposit, noElectra, ↓reduceDIte] at applied
  exact (CohortsKept.of_data (s := state)
    (t := { state with eth1DepositIndex := fun _ => next }) rfl).trans
      (cohorts_pendingDeposit applied)

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
structure ActivationCohortBound (config : Config) (state : BeaconState preset fork) : Prop where
  count : ∀ e, e ≠ FAR_FUTURE_EPOCH → e ≠ GENESIS_EPOCH →
    validatorCohort Validator.activationEpoch state e ≤
      registryChurnCap config state.validators.data.size
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
          registryChurnCap config state.validators.data.size else 0 := by
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
      registryChurnCap config state.validators.data.size := by
    have churn := validatorChurnLimit_le_registryChurnCap (config := config) (state := updated)
    rw [sizes.1] at churn
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
      registryChurnCap config after.validators.data.size := by
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
        registryChurnCap config after.validators.data.size) ∧
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
    exact Nat.le_trans bound (registryChurnCap_mono grow)
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
      (registryChurnCap_mono frame.registryGrows)
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
theorem Run.activationCohortBound {s t : ForkedBeaconState preset}
    (run : Run config checks s t) (early : t.fork < .pectra)
    (bounded : ActivationCohortBound config s.state) : ActivationCohortBound config t.state := by
  induction run with
  | nil => exact bounded
  | snoc pre step ih =>
    exact step.activationCohortBound early (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early))

/-- Genesis activates validators only at epoch zero; all other finite cohorts are empty. -/
theorem Genesis.activationCohortBound {g : ForkedBeaconState preset}
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

end EthLib.Consensus
