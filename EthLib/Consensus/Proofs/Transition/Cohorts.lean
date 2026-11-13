module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Count bounds for pre-Electra cohorts

The count cap uses the whole registry, so it does not decrease along a run.

An exit assignment fills a cohort with room, including cohorts scheduled before the run.
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

/-- Finite exit cohorts are bounded even when the configured churn limit is zero. -/
def ExitCohortBound (config : Config) (state : BeaconState preset fork) : Prop :=
  ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
    validatorCohort Validator.exitEpoch state epoch ≤
      max 1 (registryChurnCap config state.validators.data.size)

private theorem ExitCohortBound.initiateValidatorExit (early : fork < .pectra)
    (bounded : ExitCohortBound config state) {index : ValidatorIndex}
    (ok : initiateValidatorExit config state index = .ok after) :
    ExitCohortBound config after := by
  obtain ⟨old, found, unchanged | assigned⟩ := initiateValidatorExit_ok ok
  · rw [unchanged.2]
    exact bounded
  · obtain ⟨pending, queued, epoch, withdrawable, queue, _, set⟩ := assigned
    have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
    simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq] at queue
    obtain ⟨placed, allocated, equal⟩ := queue
    cases equal
    have size := (setValidator_ok set)
    obtain ⟨inside, final⟩ := size
    have sameSize : after.validators.data.size = state.validators.data.size := by
      rw [final]
      simp [BeaconState.putValidator]
    intro cohort finite
    rw [sameSize]
    by_cases same : epoch = cohort
    · have room := exitQueueEpoch_churn allocated (same ▸ finite)
      rw [← List.countP_eq_length_filter] at room
      have cap := validatorChurnLimit_le_registryChurnCap (config := config) (state := state)
      have added := validatorCohort_setValidatorAt_le (field := Validator.exitEpoch)
        (by rwa [← setValidator_eq_setValidatorAt]) cohort
      change validatorCohort Validator.exitEpoch state epoch < _ at room
      rw [same] at room
      exact Nat.le_trans added (by omega)
    · have unchanged := validatorCohort_setValidatorAt_eq
        (field := Validator.exitEpoch) (by rwa [← getValidator_eq_getValidatorAt])
        (by rwa [← setValidator_eq_setValidatorAt]) cohort (by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq, pending]
          exact iff_of_false same (Ne.symm finite))
      rw [unchanged]
      exact bounded cohort finite

private structure CohortsKept (s t : BeaconState preset fork) : Prop where
  exits : ExitCohortBound config s → ExitCohortBound config t
  activations : ∀ e, e ≠ FAR_FUTURE_EPOCH →
    validatorCohort Validator.activationEpoch t e = validatorCohort Validator.activationEpoch s e

private theorem CohortsKept.refl (s : BeaconState preset fork) :
    CohortsKept (config := config) s s := ⟨id, fun _ _ => rfl⟩

private theorem CohortsKept.trans {s t u : BeaconState preset fork}
    (first : CohortsKept (config := config) s t) (second : CohortsKept (config := config) t u) :
    CohortsKept (config := config) s u :=
  ⟨second.exits ∘ first.exits,
    fun e finite => (second.activations e finite).trans (first.activations e finite)⟩

private theorem CohortsKept.of_data {s t : BeaconState preset fork}
    (same : t.validators.data = s.validators.data := by rfl) :
    CohortsKept (config := config) s t := by
  constructor
  · intro h e finite
    simpa [validatorCohort, same] using h e finite
  · intro e _
    simp [validatorCohort, same]

private theorem CohortsKept.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    {xs : List α} (keeps : ∀ s a t, step s a = .ok t → CohortsKept (config := config) s t)
    (ok : xs.foldlM step state = .ok after) : CohortsKept (config := config) state after :=
  foldlM_ok_invariant (CohortsKept (config := config) state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (.refl state) ok

private theorem CohortsKept.setValidatorAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old) (ok : state.setValidatorAt i v = .ok after)
    (exit : v.exitEpoch = old.exitEpoch) (activation : v.activationEpoch = old.activationEpoch) :
    CohortsKept (config := config) state after := by
  have size : after.validators.data.size = state.validators.data.size := by
    obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
    simp [BeaconState.putValidator]
  constructor
  · intro h e finite
    rw [validatorCohort_setValidatorAt_eq found ok e (by rw [exit]), size]
    exact h e finite
  · intro e _
    exact validatorCohort_setValidatorAt_eq found ok e (by rw [activation])

private theorem CohortsKept.setValidator {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old) (ok : state.setValidator i v = .ok after)
    (exit : v.exitEpoch = old.exitEpoch) (activation : v.activationEpoch = old.activationEpoch) :
    CohortsKept (config := config) state after :=
  .setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) exit activation

private theorem CohortsKept.increaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance state i amount = .ok after) :
    CohortsKept (config := config) state after :=
  .of_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem CohortsKept.decreaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance state i amount = .ok after) :
    CohortsKept (config := config) state after :=
  .of_data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem cohorts_exit (early : fork < .pectra) {i : ValidatorIndex}
    (ok : initiateValidatorExit config state i = .ok after) :
    CohortsKept (config := config) state after := by
  refine ⟨fun h => h.initiateValidatorExit early ok, ?_⟩
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

private theorem cohorts_slash (early : fork < .pectra) {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state i whistleblower = .ok after) :
    CohortsKept (config := config) state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at ok
  obtain ⟨exited, exitedOk, v, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk, proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := ok
  have tail := (CohortsKept.decreaseBalance (config := config) loweredOk).trans <|
    (CohortsKept.increaseBalance raisedOk).trans <|
    (CohortsKept.increaseBalance lastOk).trans
      (CohortsKept.of_data (t := after) (by rw [(slashValidator_last done).1]))
  refine (cohorts_exit early exitedOk).trans <|
    (CohortsKept.setValidator found markedOk rfl rfl).trans (CohortsKept.trans ?_ tail)
  exact .of_data rfl

private theorem cohorts_proposerSlashing (early : fork < .pectra) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    CohortsKept (config := config) state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact cohorts_slash early slashed

private theorem cohorts_slashIf (early : fork < .pectra)
    {s t : BeaconState preset fork × Bool} {i : ValidatorIndex}
    (ok : slashIfSlashable config s i = .ok t) : CohortsKept (config := config) s.1 t.1 := by
  rcases s with ⟨s, changed⟩
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact cohorts_slash early slashed
  · cases ok
    exact .refl _

private theorem cohorts_attesterSlashing (early : fork < .pectra)
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    CohortsKept (config := config) state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun s => CohortsKept (config := config) state s.1)
    (fun _ _ _ h ok => h.trans (cohorts_slashIf early ok)) (.refl state) folded

private theorem cohorts_voluntaryExit (early : fork < .pectra) {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks state signed = .ok after) :
    CohortsKept (config := config) state after := by
  simp only [processVoluntaryExit, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact cohorts_exit early exited

private theorem CohortsKept.append {v : Validator}
    (added : after.validators.data = state.validators.data.push v)
    (exit : v.exitEpoch = FAR_FUTURE_EPOCH)
    (activation : v.activationEpoch = FAR_FUTURE_EPOCH) :
    CohortsKept (config := config) state after := by
  have counts (field : Validator → Epoch) (pending : field v = FAR_FUTURE_EPOCH)
      (e : Epoch) (finite : e ≠ FAR_FUTURE_EPOCH) :
      validatorCohort field after e = validatorCohort field state e := by
    simp only [validatorCohort, added, Array.toList_push, List.countP_append, List.countP_cons,
      List.countP_nil, pending]
    have different : (FAR_FUTURE_EPOCH == e) = false := by
      simp only [beq_eq_false_iff_ne]
      exact Ne.symm finite
    simp [different]
  refine ⟨fun h e finite => ?_, counts _ activation⟩
  rw [counts _ exit e finite]
  exact Nat.le_trans (h e finite) (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (registryChurnCap_mono (by simp [added])) (Nat.le_max_right _ _)⟩)

private theorem cohorts_admit {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} (ok : addValidatorToRegistry state key credentials amount = .ok after) :
    CohortsKept (config := config) state after := by
  apply CohortsKept.append (addValidatorToRegistry_validators_eq_push ok) <;> rfl

private theorem cohorts_pendingDeposit {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks state deposit = .ok after) :
    CohortsKept (config := config) state after := by
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
    CohortsKept (config := config) state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  simp only [applyDeposit, noElectra, ↓reduceDIte] at applied
  exact (CohortsKept.of_data (s := state)
    (t := { state with eth1DepositIndex := fun _ => next }) rfl).trans
      (cohorts_pendingDeposit applied)

private theorem cohorts_attestation {parentSlot : Slot} {attestation : Attestation preset fork}
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    CohortsKept (config := config) state after :=
  .of_data (congrArg (·.data) (processAttestation_registry ok).1)

private theorem cohorts_updateEntry (early : fork < .pectra) {i : Nat}
    (ok : updateRegistryEntry config state i = .ok after) :
    CohortsKept (config := config) state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, rest⟩ := ok
  have fields : queued.exitEpoch = v.exitEpoch ∧ queued.activationEpoch = v.activationEpoch := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      exact ⟨rfl, rfl⟩
    · cases queue
      exact ⟨rfl, rfl⟩
  have kept := CohortsKept.setValidatorAt (config := config) found set fields.1 fields.2
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok] at rest
    obtain ⟨_, _, exited⟩ := rest
    exact kept.trans (cohorts_exit early exited)
  · cases rest
    exact kept

private theorem cohorts_withdrawal {withdrawal : Withdrawal}
    (ok : applyWithdrawal state withdrawal = .ok after) :
    CohortsKept (config := config) state after := by
  unfold applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl
  · exact .decreaseBalance ok

private theorem cohorts_expectedWithdrawals (early : fork < .pectra)
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (ok : applyExpectedWithdrawals state capella expected = .ok after) :
    CohortsKept (config := config) state after := by
  have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  have noGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt (Nat.lt_trans early (by decide))
  simp only [applyExpectedWithdrawals, noElectra, noGloas, ↓reduceDIte,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, rfl, last⟩ := ok
  have withdrawals : CohortsKept (config := config) state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact .foldlM (fun _ _ _ ok => cohorts_withdrawal ok) appliedOk
  have indices : CohortsKept (config := config) applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_data rfl
    · cases indexedOk
      exact .refl _
  refine withdrawals.trans (indices.trans ?_)
  simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at last
  obtain ⟨_, _, last⟩ := last
  split at last
  · cases last
  · cases last
    exact .of_data rfl

private theorem cohorts_withdrawals (early : fork < .pectra) {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals state capella payload = .ok after) :
    CohortsKept (config := config) state after := by
  have noGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt (Nat.lt_trans early (by decide))
  simp only [processWithdrawals, noGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, applied⟩ := ok
  exact cohorts_expectedWithdrawals early applied

private theorem cohorts_execution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionPayload config engine state body bellatrix = .ok after) :
    CohortsKept (config := config) state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact .of_data rfl

private theorem cohorts_blockExecution (early : fork < .pectra)
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    CohortsKept (config := config) state after := by
  have noGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt (Nat.lt_trans early (by decide))
  simp only [processBlockExecution, noGloas, ↓reduceDIte] at ok
  split at ok
  · obtain ⟨_, withdrawn, executed⟩ := bind_ok_iff.mp ok
    exact (cohorts_withdrawals early withdrawn).trans (cohorts_execution executed)
  · split at ok
    · exact cohorts_execution ok
    · cases ok
      exact .refl _

private theorem cohorts_sync {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks state altair aggregate = .ok after) :
    CohortsKept (config := config) state after := by
  simp only [processSyncAggregate, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine CohortsKept.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (CohortsKept.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

private theorem cohorts_credentials {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    CohortsKept (config := config) state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact .setValidator found set rfl rfl

private theorem cohorts_operations (early : fork < .pectra)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after) :
    CohortsKept (config := config) state after := by
  have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  have noGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt (Nat.lt_trans early (by decide))
  simp only [processOperations, noElectra, noGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changes, rfl⟩ := ok
  have credentials : CohortsKept (config := config) exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact .foldlM (fun _ _ _ ok => cohorts_credentials ok) changes
    · cases changes
      exact .refl _
  exact (CohortsKept.foldlM (fun _ _ _ ok => cohorts_proposerSlashing early ok) proposers).trans <|
    (CohortsKept.foldlM (fun _ _ _ ok => cohorts_attesterSlashing early ok) attesters).trans <|
    (CohortsKept.foldlM (fun _ _ _ ok => cohorts_attestation ok) attestations).trans <|
    (CohortsKept.foldlM (fun _ _ _ ok => cohorts_deposit early ok) deposits).trans <|
    (CohortsKept.foldlM (fun _ _ _ ok => cohorts_voluntaryExit early ok) exits).trans credentials

private theorem cohorts_header {block : BeaconBlock preset fork}
    (ok : processBlockHeader state block = .ok after) :
    CohortsKept (config := config) state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact .of_data rfl

private theorem cohorts_randao {body : BeaconBlockBody preset fork}
    (ok : processRandao config checks state body = .ok after) :
    CohortsKept (config := config) state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact .of_data rfl

private theorem cohorts_eth1 {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : processEth1Data before state body = .ok after) :
    CohortsKept (config := config) state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  exact .of_data (by rw [← rest])

private theorem cohorts_block (early : fork < .pectra) {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) :
    CohortsKept (config := config) state after := by
  unfold processBlock at ok
  split at ok
  · have noGloas : ¬ Fork.glamsterdam ≤ fork :=
      Nat.not_le_of_lt (Nat.lt_trans early (by decide))
    simp only [processBlockAltair, noGloas, ↓reduceDIte, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, rfl, headed, header, executed, execution, revealed, randao, voted,
      vote, _, operations, sync⟩ := ok
    have executionKept : CohortsKept (config := config) headed executed := by
      split at execution
      · exact cohorts_blockExecution early execution
      · cases execution
        exact .refl _
    have voteKept : CohortsKept (config := config) revealed voted := by
      split at vote
      · exact cohorts_eth1 vote
      · cases vote
        exact .refl _
    exact (cohorts_header header).trans <| executionKept.trans <| (cohorts_randao randao).trans <|
      voteKept.trans <| (cohorts_operations early operations).trans (cohorts_sync sync)
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, header, _, randao, _, vote, operations⟩ := ok
    exact (cohorts_header header).trans <| (cohorts_randao randao).trans <|
      (cohorts_eth1 vote).trans (cohorts_operations early operations)

/-- A validated pre-Electra block preserves finite activation cohorts and the exit count bound. -/
private theorem exitCohortBound_processBlock (early : fork < .pectra)
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after)
    (bounded : ExitCohortBound config state) : ExitCohortBound config after :=
  (cohorts_block early ok).exits bounded

private theorem cohorts_effective (ok : processEffectiveBalanceUpdates state = .ok after) :
    CohortsKept (config := config) state after := by
  unfold processEffectiveBalanceUpdates at ok
  refine CohortsKept.foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact .setValidatorAt found set rfl rfl

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
    (ok : activateValidator state i = .ok after) :
    (ExitCohortBound config state → ExitCohortBound config after) ∧
    (∀ e, validatorCohort Validator.activationEpoch after e ≤
      validatorCohort Validator.activationEpoch state e +
        if e.toNat = scheduledActivationEpoch state then 1 else 0) := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at ok
  obtain ⟨v, found, epoch, epochOk, set⟩ := ok
  have assigned := (computeActivationExitEpoch_ok_iff.mp epochOk).2
  have size : after.validators.data.size = state.validators.data.size := by
    obtain ⟨_, rfl⟩ := setValidator_ok set
    simp [BeaconState.putValidator]
  have read : getValidatorAt state i.toNat = .ok v := by rwa [← getValidator_eq_getValidatorAt]
  have write := set
  rw [setValidator_eq_setValidatorAt] at write
  constructor
  · intro h e finite
    rw [validatorCohort_setValidatorAt_eq (field := Validator.exitEpoch) read write e rfl, size]
    exact h e finite
  · intro e
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
      indices.foldlM activateValidator state = .ok after →
      (ExitCohortBound config state → ExitCohortBound config after) ∧
      (∀ e, validatorCohort Validator.activationEpoch after e ≤
        validatorCohort Validator.activationEpoch state e +
          if e.toNat = scheduledActivationEpoch state then indices.length else 0)
  | [], _, _, ok => by
    cases ok
    exact ⟨id, fun _ => by simp⟩
  | i :: rest, state, after, ok => by
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, tail⟩ := ok
    have one := cohorts_activate (config := config) first
    have many := cohorts_activate_many tail
    have same : scheduledActivationEpoch middle = scheduledActivationEpoch state := by
      unfold scheduledActivationEpoch getCurrentEpoch
      rw [(frame_activateValidator first).slot]
    refine ⟨many.1 ∘ one.1, fun e => ?_⟩
    have h := many.2 e
    rw [same] at h
    have k := one.2 e
    split at h <;> simp_all only [↓reduceIte, List.length_cons] <;> omega

/-- A pre-Electra registry pass preserves the bound on every inherited exit cohort. -/
private theorem exitCohortBound_processRegistryUpdates (early : fork < .pectra)
    (ok : processRegistryUpdates config state = .ok after)
    (bounded : ExitCohortBound config state) :
    ExitCohortBound config after := by
  have noElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  simp only [processRegistryUpdates, noElectra, ↓reduceIte, bind_ok_iff] at ok
  obtain ⟨updated, pass, activated⟩ := ok
  exact (cohorts_activate_many activated).1
    ((CohortsKept.foldlM (fun _ _ _ ok => cohorts_updateEntry early ok) pass).exits bounded)

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
  have kept := CohortsKept.foldlM (config := config)
    (fun _ _ _ ok => cohorts_updateEntry early ok) pass
  have sizes := foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_updateRegistryEntry step))
    (SameSizes.refl state) pass
  have slot := foldlM_ok_invariant (fun next : BeaconState preset fork => next.slot = state.slot)
    (fun _ _ _ h step => (updateRegistryEntry_activationEpochs step).1.trans h) rfl pass
  have same : scheduledActivationEpoch updated = scheduledActivationEpoch state := by
    simp only [scheduledActivationEpoch, getCurrentEpoch, slot]
  have bound := (cohorts_activate_many (config := config) activated).2 e
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
      CohortsKept (config := config) state before ∧
      processRegistryUpdates config before = .ok registered ∧
      CohortsKept (config := config) registered after ∧
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
  have last : CohortsKept (config := config) registered after ∧
      registered.validators.data.size ≤ after.validators.data.size := by
    refine EpochTrace.transport (R := fun a b : BeaconState preset fork =>
        CohortsKept (config := config) a b ∧ a.validators.data.size ≤ b.validators.data.size)
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

/-- An epoch transition preserves all finite exit cohort bounds, including old schedules. -/
private theorem exitCohortBound_processEpoch (early : fork < .pectra)
    (ok : processEpoch config checks state = .ok after) (bounded : ExitCohortBound config state) :
    ExitCohortBound config after := by
  obtain ⟨_, _, head, registered, tail, _, _, _⟩ := cohorts_epoch early ok
  exact tail.exits (exitCohortBound_processRegistryUpdates early registered (head.exits bounded))

/-- Advancing a pre-Electra slot preserves inherited exit schedules. -/
private theorem exitCohortBound_advanceSlot (early : fork < .pectra)
    (ok : advanceSlot config checks state = .ok after) (bounded : ExitCohortBound config state) :
    ExitCohortBound config after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := ok
  have cachedKept : CohortsKept (config := config) state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_data rfl
  have epochedBound : ExitCohortBound config epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact exitCohortBound_processEpoch early epochedOk (cachedKept.exits bounded)
    · cases epochedOk
      exact cachedKept.exits bounded
  exact epochedBound

private theorem exitCohortBound_upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .pectra)
    (bounded : ExitCohortBound config s.state) : ExitCohortBound config t.val.state := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simpa only [ExitCohortBound, validatorCohort, (upgradeToAltair_spec upgraded).1] using bounded
  · subst ok
    exact bounded
  · subst ok
    exact bounded
  · subst ok
    exact bounded
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.fusaka < Fork.pectra) early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.glamsterdam < Fork.pectra) early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.pectra) early)

private theorem exitCohortBound_upgrades {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .pectra)
    (bounded : ExitCohortBound config s.state) : ExitCohortBound config t.state := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact ih next rest early (exitCohortBound_upgrade nextOk
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early) bounded)
  | case2 s notDue => cases ok; exact bounded

/-- A concrete pre-Electra step preserves the bound on scheduled exit cohorts. -/
private theorem Step.exitCohortBound {s t : ForkedBeaconState preset}
    (step : Step config checks s t) (early : t.fork < .pectra)
    (bounded : ExitCohortBound config s.state) : ExitCohortBound config t.state := by
  cases step with
  | block engine signed due ok =>
    exact exitCohortBound_processBlock early (applySignedBlock_ok ok).2.1 bounded
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact exitCohortBound_upgrades upgrades early (exitCohortBound_advanceSlot
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le upgrades) early) slotOk bounded)

/-- The bound carries inherited exit cohorts through a whole pre-Electra run. -/
theorem Run.exitCohortBound {s t : ForkedBeaconState preset}
    (run : Run config checks s t) (early : t.fork < .pectra)
    (bounded : ExitCohortBound config s.state) : ExitCohortBound config t.state := by
  induction run with
  | nil => exact bounded
  | snoc pre step ih =>
    exact step.exitCohortBound early (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early))

/-- Genesis has bounded exit cohorts: deposits and genesis activation schedule no exits. -/
theorem Genesis.exitCohortBound {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ExitCohortBound config g.state := by
  obtain ⟨hash, time, deposits, ok⟩ := genesis
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    equal⟩ := initializeBeaconStateFromEth1_ok ok
  have first := CohortsKept.foldlM (config := config) (fun s entry t computed => by
    simp only [genesisDeposit, bind_ok_iff] at computed
    obtain ⟨root, _, deposited⟩ := computed
    exact (CohortsKept.of_data (s := s)
      (t := { s with eth1Data := fun _ => { s.eth1Data (Nat.lt_trans before (by decide)) with
        depositRoot := root } }) rfl).trans
      (cohorts_deposit (Nat.lt_trans before (by decide)) deposited)) depositedOk
  have initial : ExitCohortBound config deposited := first.exits (by
    intro e finite
    simp [validatorCohort, emptyGenesisState])
  have last := foldlM_ok_invariant (ExitCohortBound config)
    (fun s i t bounded computed => by
      simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨v, found, _, _, set⟩ := computed
      have sizes := sameSizes_setValidatorAt set
      intro e finite
      rw [validatorCohort_setValidatorAt_eq (field := Validator.exitEpoch) found set e
        (by split <;> rfl), sizes.1]
      exact bounded e finite) initial activatedOk
  rw [equal]
  exact last

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
  have first := CohortsKept.foldlM (config := config) (fun s entry t computed => by
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
