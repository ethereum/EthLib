module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Proofs: activity up to the current epoch plus `MAX_SEED_LOOKAHEAD` stays fixed along a chain

A validator is active in an epoch from its activation epoch, up to its exit epoch.

The state transition sets an activation or an exit epoch only after a bound.

That bound is the current epoch plus `MAX_SEED_LOOKAHEAD`.

An activation lands at the first epoch an activation may take, `MAX_SEED_LOOKAHEAD + 1` epochs on.

An exit lands there or later, by the exit queue or the consolidation queue.

From Electra, the exit and consolidation queues of [EIP-7251] give no epoch before that one.

A new validator has no activation epoch yet, so it is active in no epoch.

So each step of a chain keeps which validators are active in each epoch up to that bound.

That holds at every fork, for slots, epochs, blocks and upgrades.

From Electra, a step also assigns an exit only to a validator that is already activated.

The current epoch never decreases along a chain.

So that bound never decreases either.

So along a run of steps, the active sets stay fixed in each epoch up to the bound of its start.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Steps that keep activity -/

/-- A step that never shrinks the registry.

It keeps the slot and activity. -/
def StepKeeps (state after : BeaconState preset fork) : Prop :=
  state.validators.data.size ≤ after.validators.data.size ∧
    ActiveStep state after

theorem StepKeeps.refl (state : BeaconState preset fork) : StepKeeps state state :=
  ⟨Nat.le_refl _, ActiveStep.refl state⟩

theorem StepKeeps.trans {first second third : BeaconState preset fork}
    (one : StepKeeps first second) (two : StepKeeps second third) : StepKeeps first third :=
  ⟨Nat.le_trans one.1 two.1, one.2.trans two.2⟩

private theorem StepKeeps.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x s', step s x = .ok s' → StepKeeps s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : StepKeeps state after :=
  foldlM_ok_invariant (StepKeeps state) (fun _ _ _ before ok => before.trans (keeps _ _ _ ok))
    (StepKeeps.refl state) computed

private theorem StepKeeps.of_step (grows : state.validators.data.size ≤ after.validators.data.size)
    (step : ActiveStep state after) : StepKeeps state after :=
  ⟨grows, step⟩

theorem StepKeeps.of_validators
    (validators : after.validators.data = state.validators.data := by rfl)
    (slot : after.slot = state.slot := by rfl) : StepKeeps state after :=
  ⟨Nat.le_of_eq (congrArg Array.size validators).symm,
    ActiveStep.of_validators validators slot⟩

/-! ## Exits start from activity -/

/-- Each exit that a step assigns is of a validator whose activation epoch has come at its start. -/
private def ExitsStart {f g : Fork} (state : BeaconState preset f) (after : BeaconState preset g) :
    Prop :=
  ∀ (i : Nat) (v w : Validator), state.validators.data[i]? = some v →
    after.validators.data[i]? = some w → v.exitEpoch = FAR_FUTURE_EPOCH →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH → v.activationEpoch ≤ getCurrentEpoch state

private theorem ExitsStart.of_data {f g : Fork} {state : BeaconState preset f}
    {after : BeaconState preset g}
    (same : after.validators.data = state.validators.data := by rfl) : ExitsStart state after := by
  intro i v w found read far assigned
  rw [same] at read
  obtain rfl := Option.some.inj (found.symm.trans read)
  exact absurd far assigned

/-- A step that keeps the slot, and activity up to the fixed epoch.

From Electra it also starts exits only of activated validators. -/
private def BlockKeeps (state after : BeaconState preset fork) : Prop :=
  StepKeeps state after ∧ (Fork.pectra ≤ fork → ExitsStart state after)

private theorem BlockKeeps.refl (state : BeaconState preset fork) : BlockKeeps state state :=
  ⟨StepKeeps.refl state, fun _ => ExitsStart.of_data⟩

private theorem BlockKeeps.trans {first second third : BeaconState preset fork}
    (one : BlockKeeps first second) (two : BlockKeeps second third) : BlockKeeps first third := by
  refine ⟨one.1.trans two.1, fun electra i v w found read far assigned => ?_⟩
  have inside : i < second.validators.data.size :=
    Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 one.1.1
  obtain ⟨z, middle⟩ : ∃ z, second.validators.data[i]? = some z :=
    ⟨_, Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
  by_cases still : z.exitEpoch = FAR_FUTURE_EPOCH
  · have activated := two.2 electra i z w middle read still assigned
    have epoch : getCurrentEpoch second = getCurrentEpoch first := by
      simp only [getCurrentEpoch, one.1.2.1]
    rw [epoch] at activated
    by_cases late : getCurrentEpoch first = FAR_FUTURE_EPOCH
    · rw [late]
      exact UInt64.le_iff_toNat_le.mpr (by
        have := v.activationEpoch.toNat_lt
        change _ ≤ 18446744073709551615
        omega)
    · have bound := one.1.2.2 (getCurrentEpoch first) (getCurrentEpoch_le_activityFixedEpoch first)
        i
      have secondActive : isActiveAt second (getCurrentEpoch first) i = true := by
        refine isActiveAt_eq_true_iff.mpr ⟨z, middle, ?_⟩
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨activated, ?_⟩
        rw [still, UInt64.lt_iff_toNat_lt]
        have := UInt64.toNat_lt (getCurrentEpoch first)
        have ne : (getCurrentEpoch first).toNat ≠ FAR_FUTURE_EPOCH.toNat := fun eq =>
          late (UInt64.toNat_inj.mp eq)
        change _ < 18446744073709551615
        change _ ≠ 18446744073709551615 at ne
        omega
      rw [bound] at secondActive
      obtain ⟨u, found', active⟩ := isActiveAt_eq_true_iff.mp secondActive
      obtain rfl := Option.some.inj (found.symm.trans found')
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
      exact active.1
  · exact one.2 electra i v z found middle far still

/-- An active validator was activated at or before the epoch. -/
theorem activationLe_of_active {v : Validator} {e : Epoch}
    (active : isActiveValidator v e = true) : v.activationEpoch ≤ e := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact active.1

/-- A slashable validator was activated at or before the epoch. -/
theorem activationLe_of_slashable {v : Validator} {e : Epoch}
    (slashable : isSlashableValidator v e = true) : v.activationEpoch ≤ e := by
  simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at slashable
  exact slashable.1.2

private theorem BlockKeeps.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x s', step s x = .ok s' → BlockKeeps s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : BlockKeeps state after :=
  foldlM_ok_invariant (BlockKeeps state) (fun _ _ _ before ok => before.trans (keeps _ _ _ ok))
    (BlockKeeps.refl state) computed

private theorem BlockKeeps.of_step (grows : state.validators.data.size ≤ after.validators.data.size)
    (step : ActiveStep state after) (validators : after.validators.data = state.validators.data) :
    BlockKeeps state after :=
  ⟨StepKeeps.of_step grows step, fun _ => ExitsStart.of_data validators⟩

private theorem BlockKeeps.of_validators
    (validators : after.validators.data = state.validators.data := by rfl)
    (slot : after.slot = state.slot := by rfl) : BlockKeeps state after :=
  ⟨StepKeeps.of_validators validators slot, fun _ => ExitsStart.of_data validators⟩

/-! ## Mutators -/

private theorem stepKeeps_setValidatorAt {index : Nat} {validator old : Validator}
    (found : getValidatorAt state index = .ok old)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidatorAt index validator = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (Nat.le_of_eq (sameSizes_setValidatorAt set).1.symm)
    (activeStep_setValidatorAt found same set)

theorem stepKeeps_setValidator {index : ValidatorIndex} {validator old : Validator}
    (found : getValidator state index = .ok old)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidator index validator = .ok after) : StepKeeps state after :=
  stepKeeps_setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) same
    (by rwa [← setValidator_eq_setValidatorAt])

private theorem stepKeeps_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (frame_increaseBalance computed).registryGrows
    (activeStep_increaseBalance computed)

theorem stepKeeps_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (frame_decreaseBalance computed).registryGrows
    (activeStep_decreaseBalance computed)

theorem stepKeeps_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (frame_initiateValidatorExit computed).registryGrows
    (activeStep_initiateValidatorExit computed)

theorem stepKeeps_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    StepKeeps state after :=
  StepKeeps.of_step (frame_slashValidator computed).registryGrows
    (activeStep_slashValidator computed)

private theorem stepKeeps_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    StepKeeps state after :=
  StepKeeps.of_step (by rw [addValidatorToRegistry_validators_eq_push computed]; simp)
    (activeStep_addValidatorToRegistry computed)

private theorem ExitsStart.setValidatorAt {index : Nat} {validator old : Validator}
    (found : getValidatorAt state index = .ok old)
    (starts : old.exitEpoch = FAR_FUTURE_EPOCH → validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      old.activationEpoch ≤ getCurrentEpoch state)
    (set : state.setValidatorAt index validator = .ok after) : ExitsStart state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[index] = old := by simpa [getValidatorAt, inside] using found
  intro j v w read later far assigned
  by_cases same : j = index
  · subst same
    obtain rfl : v = old := by simpa [Array.getElem?_eq_getElem inside, oldEq] using read.symm
    obtain rfl : w = validator := by
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, inside] using
        later.symm
    exact starts far assigned
  · simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, Ne.symm same, ↓reduceIte] at later
    obtain rfl := Option.some.inj (read.symm.trans later)
    exact absurd far assigned

private theorem blockKeeps_setValidatorAt {index : Nat} {validator old : Validator}
    (found : getValidatorAt state index = .ok old)
    (set : state.setValidatorAt index validator = .ok after)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (starts : old.exitEpoch = FAR_FUTURE_EPOCH → validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      old.activationEpoch ≤ getCurrentEpoch state) : BlockKeeps state after :=
  ⟨stepKeeps_setValidatorAt found same set, fun _ => ExitsStart.setValidatorAt found starts set⟩

private theorem blockKeeps_setValidator {index : ValidatorIndex} {validator old : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (starts : old.exitEpoch = FAR_FUTURE_EPOCH → validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      old.activationEpoch ≤ getCurrentEpoch state) : BlockKeeps state after :=
  blockKeeps_setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) same starts

private theorem blockKeeps_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : BlockKeeps state after :=
  ⟨stepKeeps_increaseBalance computed,
    fun _ => ExitsStart.of_data (congrArg (·.data) (increaseBalance_validators computed))⟩

private theorem blockKeeps_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : BlockKeeps state after :=
  ⟨stepKeeps_decreaseBalance computed,
    fun _ => ExitsStart.of_data (congrArg (·.data) (decreaseBalance_validators computed))⟩

/-- The exit of a validator that has not started to exit starts at an activated validator. -/
private theorem blockKeeps_initiateValidatorExit {index : ValidatorIndex}
    (active : ∀ v, getValidator state index = .ok v → v.exitEpoch = FAR_FUTURE_EPOCH →
      v.activationEpoch ≤ getCurrentEpoch state)
    (computed : initiateValidatorExit config state index = .ok after) : BlockKeeps state after := by
  refine ⟨stepKeeps_initiateValidatorExit computed, fun _ => ?_⟩
  obtain ⟨old, read, unchanged | ⟨far, queued, exitEpoch, withdrawable, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · rw [unchanged.2]
    exact ExitsStart.of_data
  · have same := (exitQueue_validators queue).1
    have found : getValidatorAt queued index.toNat = .ok old := by
      rw [← getValidator_eq_getValidatorAt]
      exact (getValidator_of_validators_eq same index).trans read
    rw [setValidator_eq_setValidatorAt] at set
    have epoch : getCurrentEpoch queued = getCurrentEpoch state := by
      simp only [getCurrentEpoch, (frame_exitQueue queue).slot]
    have starts := ExitsStart.setValidatorAt (state := queued) found
      (fun _ _ => epoch ▸ active old read far) set
    intro j v w before after far' assigned
    have moved : queued.validators.data[j]? = some v := by rw [same]; exact before
    rw [← epoch]
    exact starts j v w moved after far' assigned

private theorem ExitsStart.append {validator : Validator}
    (added : after.validators.data = state.validators.data.push validator) :
    ExitsStart state after := by
  intro j a b before later far assigned
  rw [added] at later
  have inside := (Array.getElem?_eq_some_iff.mp before).1
  rw [Array.getElem?_push_lt inside, ← Array.getElem?_eq_getElem inside] at later
  obtain rfl := Option.some.inj (before.symm.trans later)
  exact absurd far assigned

private theorem blockKeeps_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    BlockKeeps state after :=
  ⟨stepKeeps_addValidatorToRegistry computed,
    fun _ => ExitsStart.append (addValidatorToRegistry_validators_eq_push computed)⟩

/-- Slashing a validator that has not started to exit starts its exit at an activated validator. -/
private theorem blockKeeps_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (active : ∀ v, getValidator state slashedIndex = .ok v → v.exitEpoch = FAR_FUTURE_EPOCH →
      v.activationEpoch ≤ getCurrentEpoch state)
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    BlockKeeps state after := by
  obtain ⟨exited, validator, _, marked, _, _, slashings, lowered, _, _, raised, last, exitedOk,
    found, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok computed
  -- Marking the validator slashed keeps its activation and exit epochs.
  refine (blockKeeps_initiateValidatorExit active exitedOk).trans <|
    (blockKeeps_setValidator
      (validator := { validator with slashed := true, withdrawableEpoch := _ })
      found markedOk (fun _ _ => rfl) (fun far assigned => absurd far assigned)).trans <|
    (BlockKeeps.of_validators : BlockKeeps marked { marked with slashings }).trans <|
    (blockKeeps_decreaseBalance loweredOk).trans <| (blockKeeps_increaseBalance raisedOk).trans <|
    (blockKeeps_increaseBalance lastOk).trans ?_
  subst done
  split <;> exact BlockKeeps.refl _

/-! ## Deposits -/

private theorem blockKeeps_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    BlockKeeps state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact BlockKeeps.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact blockKeeps_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ BlockKeeps.refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact blockKeeps_increaseBalance computed

private theorem blockKeeps_applyDepositElectra {electra : .pectra ≤ fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {withdrawalCredentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    BlockKeeps state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (blockKeeps_addValidatorToRegistry added).trans BlockKeeps.of_validators
    · cases computed
      exact BlockKeeps.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact BlockKeeps.of_validators

private theorem blockKeeps_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    BlockKeeps state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine (BlockKeeps.of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })).trans ?_
  unfold applyDeposit at applied
  split at applied
  · exact blockKeeps_applyDepositElectra applied
  · exact blockKeeps_applyPendingDeposit applied

theorem stepKeeps_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processDeposit computed).1

/-! ## Requests of the execution layer -/

private theorem blockKeeps_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    BlockKeeps state after := by
  obtain ⟨-, -, -, start, pending, rfl⟩ := processDepositRequest_ok computed
  exact BlockKeeps.of_validators

private theorem blockKeeps_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    BlockKeeps state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    obtain ⟨-, validators, -⟩ := computeExitEpochAndUpdateChurn_earliest churned
    exact BlockKeeps.of_validators (by rw [validators])
      (frame_computeExitEpochAndUpdateChurn churned).slot
  · cases computed
    exact BlockKeeps.refl _

private theorem blockKeeps_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    BlockKeeps state after := by
  rcases withdrawalRequest_cases computed with rfl | ⟨_, _, accepted, exited⟩ |
    ⟨_, _, _, _, withdrawn⟩
  · exact BlockKeeps.refl _
  · refine blockKeeps_initiateValidatorExit (fun v read _ => ?_) exited
    rw [getValidator_eq_ok_iff.mpr accepted.found] at read
    obtain rfl := Except.ok.inj read
    -- The request is accepted only for a validator that is active.
    exact activationLe_of_active (isActiveValidator_of_canRequest accepted.allowed)
  · exact blockKeeps_requestPartialWithdrawal withdrawn

private theorem blockKeeps_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    BlockKeeps state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact BlockKeeps.of_validators
  · cases computed
    exact BlockKeeps.refl _

/-- Compounding credentials keep the activation and the exit epoch. -/
private theorem blockKeeps_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    BlockKeeps state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (blockKeeps_setValidator found set (fun _ _ => by rfl)
    (fun far assigned => absurd far assigned)).trans
    (blockKeeps_queueExcessActiveBalance queued)

/-- A consolidation from Electra takes effect after the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
private theorem consolidationEpoch_lt {electra : .pectra ≤ fork} {balance : Gwei}
    {churned : BeaconState preset fork} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (churned, epoch)) :
    (getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < epoch.toNat := by
  cases first : computeActivationExitEpoch preset (getCurrentEpoch state) with
  | error =>
    simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError, bind,
      Except.bind] at computed
  | ok firstEpoch =>
    have early := UInt64.le_iff_toNat_le.mp
      (computeConsolidationEpochAndUpdateChurn_first first computed).1
    have firstEq := (computeActivationExitEpoch_ok_iff.mp first).2
    omega

/-- The source of a consolidation had not started to exit, and exits after the fixed epoch.

It must be the validator at its index. -/
private theorem blockKeeps_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (active : isActiveValidator source (getCurrentEpoch state) = true)
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    BlockKeeps state after := by
  obtain ⟨_, _, _, _, _, churned, _, set, _, rfl⟩ := queueConsolidation_steps computed
  have later := consolidationEpoch_lt churned
  refine BlockKeeps.trans BlockKeeps.of_validators ((blockKeeps_setValidator
    (by exact getValidator_eq_ok_iff.mpr found) set (fun _ le => ?_)
    (fun _ _ => activationLe_of_active active)).trans BlockKeeps.of_validators)
  exact isActiveValidator_eq_of_exit rfl far (activityFixedEpoch_lt_of_toNat_lt later) le

private theorem blockKeeps_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    BlockKeeps state after := by
  rcases consolidationRequest_cases computed with
    rfl | ⟨_, _, _, switched⟩ | ⟨_, _, _, _, accepted, queued⟩
  · exact BlockKeeps.refl _
  · exact blockKeeps_switchToCompoundingValidator switched
  -- The source had not started to exit.
  · exact blockKeeps_queueConsolidation accepted.sourceAt accepted.sourceStays
      accepted.sourceActive queued

private theorem blockKeeps_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    BlockKeeps state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processDepositRequest ok)
    depositsOk).trans <|
    (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processConsolidationRequest ok) consolidationsOk

theorem stepKeeps_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processExecutionRequests computed).1

/-! ## Withdrawals and the execution part of a block -/

private theorem blockKeeps_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : BlockKeeps state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact BlockKeeps.of_validators
  · exact blockKeeps_decreaseBalance computed

private theorem blockKeeps_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    BlockKeeps state after := by
  exact applyExpectedWithdrawals_of BlockKeeps BlockKeeps.refl (fun one two => one.trans two)
    (fun ok => blockKeeps_applyWithdrawal ok)
    (fun frame validators => BlockKeeps.of_validators (congrArg (·.data) validators) frame.slot)
    computed

private theorem blockKeeps_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : BlockKeeps state after :=
  processWithdrawals_of BlockKeeps (BlockKeeps.refl _)
    (fun _ => blockKeeps_applyExpectedWithdrawals) computed

private theorem blockKeeps_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    BlockKeeps state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact blockKeeps_setValidator found set (fun _ _ => by simp only [isActiveValidator])
    (fun far assigned => absurd far assigned)

theorem stepKeeps_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processBlsToExecutionChange computed).1

private theorem blockKeeps_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    BlockKeeps state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact BlockKeeps.of_validators

private theorem blockKeeps_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    BlockKeeps state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BlockKeeps.of_validators)

private theorem blockKeeps_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    BlockKeeps state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact BlockKeeps.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact BlockKeeps.of_validators

private theorem blockKeeps_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    BlockKeeps state after := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact BlockKeeps.refl _
  · have settledStep : BlockKeeps state settled := by
      rw [settleParentPayment_eq settledOk]
      exact BlockKeeps.of_validators
    exact settledStep.trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processDepositRequest ok) depositsOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processWithdrawalRequest ok)
        withdrawalsOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processConsolidationRequest ok)
        consolidationsOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processBuilderDepositRequest ok)
        buildersOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processBuilderExitRequest ok) exitsOk).trans
        BlockKeeps.of_validators

private theorem blockKeeps_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    BlockKeeps state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact BlockKeeps.of_validators
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact BlockKeeps.of_validators

private theorem blockKeeps_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    BlockKeeps state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (blockKeeps_processWithdrawals withdrawnOk).trans
      (blockKeeps_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (blockKeeps_processWithdrawals withdrawnOk).trans
      (blockKeeps_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact blockKeeps_processExecutionPayload computed
    · cases computed
      exact BlockKeeps.refl _

theorem stepKeeps_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processBlockExecution computed).1

private theorem blockKeeps_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    BlockKeeps state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine BlockKeeps.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (blockKeeps_increaseBalance raised).trans (blockKeeps_increaseBalance paid)
  · exact blockKeeps_decreaseBalance (liftAccessor_ok.mp ok)

theorem stepKeeps_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processSyncAggregate computed).1

/-! ## The other steps of a block -/

private theorem blockKeeps_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : BlockKeeps state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact BlockKeeps.of_validators

private theorem blockKeeps_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : BlockKeeps state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact BlockKeeps.of_validators

private theorem blockKeeps_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : BlockKeeps state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact BlockKeeps.of_validators

theorem stepKeeps_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : StepKeeps state after :=
  (blockKeeps_processEth1Data computed).1

private theorem blockKeeps_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    BlockKeeps state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, v, found, _, slashable, _, _, _, _, slashed⟩ := computed
  exact blockKeeps_slashValidator (fun _ read _ => by
    obtain rfl := Except.ok.inj (found.symm.trans read)
    exact activationLe_of_slashable slashable) slashed

theorem stepKeeps_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processProposerSlashing computed).1

private theorem blockKeeps_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    BlockKeeps state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine foldlM_ok_invariant (fun step => BlockKeeps state step.1)
    (fun step _ next before ok => before.trans ?_)
    (show BlockKeeps state (state, false).1 from BlockKeeps.refl state) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · rename_i slashable
    simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact blockKeeps_slashValidator (fun _ read _ => by
      obtain rfl := Except.ok.inj (found.symm.trans read)
      exact activationLe_of_slashable slashable) slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ BlockKeeps.refl _

theorem stepKeeps_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processAttesterSlashing computed).1

private theorem blockKeeps_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    BlockKeeps state after :=
  BlockKeeps.of_validators (by rw [(processAttestation_registry computed).1])
    (frame_processAttestation computed).slot

theorem stepKeeps_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processAttestation computed).1

private theorem blockKeeps_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    BlockKeeps state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨v, found, _, active, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact blockKeeps_initiateValidatorExit (fun _ read _ => by
    obtain rfl := Except.ok.inj (found.symm.trans read)
    exact activationLe_of_active active) exited

theorem stepKeeps_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processVoluntaryExit computed).1

/-! ## Blocks -/

private theorem blockKeeps_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    BlockKeeps state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processProposerSlashing ok)
      proposersOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processAttesterSlashing ok)
        attestersOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processAttestation ok) attestedOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processVoluntaryExit ok) exitsOk).trans <|
      (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processBlsToExecutionChange ok)
        changesOk).trans <|
      BlockKeeps.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact BlockKeeps.refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : BlockKeeps exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ BlockKeeps.refl _
  have requests : BlockKeeps changed after := by
    split at requestsOk
    · exact blockKeeps_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ BlockKeeps.refl _
  exact (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processProposerSlashing ok)
    proposersOk).trans <|
    (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processAttesterSlashing ok) attestersOk).trans <|
    (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processAttestation ok) attestedOk).trans <|
    (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processDeposit ok) depositedOk).trans <|
    (BlockKeeps.foldlM (fun _ _ _ ok => blockKeeps_processVoluntaryExit ok) exitsOk).trans <|
    changes.trans requests

private theorem blockKeeps_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    BlockKeeps state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [stateBeforeOperations, bind_assoc, bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidStep : BlockKeeps state paid := by
      split at paidOk
      · exact blockKeeps_processParentExecutionPayload paidOk
      · cases paidOk
        exact BlockKeeps.refl _
    have executedStep : BlockKeeps headed executed := by
      split at executedOk
      · exact blockKeeps_processBlockExecution executedOk
      · cases executedOk
        exact BlockKeeps.refl _
    have votedStep : BlockKeeps revealed voted := by
      split at votedOk
      · exact blockKeeps_processEth1Data votedOk
      · cases votedOk
        exact BlockKeeps.refl _
    exact paidStep.trans <| (blockKeeps_processBlockHeader headedOk).trans <|
      executedStep.trans <| (blockKeeps_processRandao revealedOk).trans <| votedStep.trans <|
      (blockKeeps_processOperations operatedOk).trans (blockKeeps_processSyncAggregate synced)
  rename_i notAltair
  have notGloas' : ¬ Fork.glamsterdam ≤ fork := fun h => notAltair (Nat.le_trans (by decide) h)
  have notBellatrix' : ¬ Fork.bellatrix ≤ fork := fun h => notAltair (Nat.le_trans (by decide) h)
  have early' : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le notAltair) (by decide)
  simp only [stateBeforeOperations, notGloas', notBellatrix', early', ↓reduceDIte, pure_bind,
    bind_assoc, bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (blockKeeps_processBlockHeader headerOk).trans <|
    (blockKeeps_processRandao randaoOk).trans <|
    (blockKeeps_processEth1Data eth1Ok).trans (blockKeeps_processOperations operationsOk)



theorem stepKeeps_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    StepKeeps state after :=
  (blockKeeps_processBlock computed).1

/-! ## The steps of an epoch -/

private theorem blockKeeps_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    BlockKeeps state after :=
  BlockKeeps.of_step
    (by rw [(processJustificationAndFinalization_keeps computed).2.2.2.2.2.1]; exact Nat.le_refl _)
    (activeStep_processJustificationAndFinalization computed)
    (congrArg (·.data) (processJustificationAndFinalization_keeps computed).2.2.2.2.2.1)

private theorem blockKeeps_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    BlockKeeps state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BlockKeeps.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact BlockKeeps.of_validators

/-- From Electra, the registry updates of one validator keep activity up to the fixed epoch.

An activation goes to an epoch after the fixed epoch, and only from the far future. -/
private theorem blockKeeps_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (later :
      (getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < activationEpoch.toNat)
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    BlockKeeps state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact blockKeeps_setValidatorAt found set (fun _ _ => by simp only [isActiveValidator])
      (fun far assigned => absurd far assigned)
  split at computed
  · rename_i active
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨i, converted, exited⟩ := computed
    have indexEq : i.toNat = index := (ofNatChecked_ok_iff.mp (mapError_ok_iff.mp converted)).2
    refine blockKeeps_initiateValidatorExit (fun v read _ => ?_) exited
    have same : getValidator state i = .ok validator := by
      simpa [getValidator_eq_getValidatorAt, indexEq] using found
    obtain rfl := Except.ok.inj (read.symm.trans same)
    simp only [Bool.and_eq_true] at active
    exact activationLe_of_active active.1
  split at computed
  · rename_i eligible
    simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
    -- Neither the far-future epoch nor the new one is at or before the fixed epoch.
    exact blockKeeps_setValidatorAt found (liftAccessor_ok.mp computed)
      (fun _ le => isActiveValidator_eq_of_activation
        (.inl eligible.2) (activityFixedEpoch_lt_of_toNat_lt later) le)
      (fun far assigned => absurd far assigned)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BlockKeeps.refl _

private theorem blockKeeps_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : BlockKeeps state after := by
  have grows := (frame_processRegistryUpdates computed).registryGrows
  by_cases electra : Fork.pectra ≤ fork
  · unfold processRegistryUpdates at computed
    simp only [electra, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
      mapError_ok_iff] at computed
    obtain ⟨activationEpoch, activationOk, computed⟩ := computed
    have activationEq := (computeActivationExitEpoch_ok_iff.mp activationOk).2
    -- Each step keeps the slot, so the activation epoch stays after the fixed epoch.
    refine (foldlM_ok_invariant (fun middle => BlockKeeps state middle ∧ middle.slot = state.slot)
      (fun middle _ next before ok => ⟨before.1.trans
        (blockKeeps_updateRegistryEntryElectra ?_ ok),
        (frame_updateRegistryEntryElectra ok).slot.trans before.2⟩)
      ⟨BlockKeeps.refl state, rfl⟩ computed).1
    have epoch : getCurrentEpoch middle = getCurrentEpoch state := by
      simp only [getCurrentEpoch, before.2]
    rw [epoch, activationEq]
    omega
  · exact ⟨StepKeeps.of_step grows
      (activeStep_processRegistryUpdates (Nat.lt_of_not_le electra) computed),
      fun h => absurd h electra⟩

/-- Registry updates keep the slot and activity through the fixed epoch.

They do not shrink the registry. -/
theorem stepKeeps_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : StepKeeps state after :=
  (blockKeeps_processRegistryUpdates computed).1

/-- Each validator of the later state has the exit epoch of the one at its index before. -/
private def ExitsSame {f g : Fork} (state : BeaconState preset f) (after : BeaconState preset g) :
    Prop :=
  ∀ (j : Nat) (w : Validator), after.validators.data[j]? = some w →
    ∃ v, state.validators.data[j]? = some v ∧ w.exitEpoch = v.exitEpoch

private theorem ExitsStart.of_same {f g : Fork} {state : BeaconState preset f}
    {after : BeaconState preset g} (same : ExitsSame state after) : ExitsStart state after := by
  intro i v w found read far assigned
  obtain ⟨v', found', equal⟩ := same i w read
  obtain rfl := Option.some.inj (found.symm.trans found')
  exact absurd (equal.trans far) assigned

private theorem ExitsSame.setValidatorAt {state current after : BeaconState preset fork}
    {i : Nat} {old v : Validator} (kept : ExitsSame state current)
    (found : getValidatorAt current i = .ok old) (set : current.setValidatorAt i v = .ok after)
    (same : v.exitEpoch = old.exitEpoch) : ExitsSame state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : current.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro j w read
  by_cases here : j = i
  · subst here
    obtain rfl : w = v := by
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, inside] using
        read.symm
    obtain ⟨v₀, found₀, equal⟩ := kept j old (by simp [Array.getElem?_eq_getElem inside, oldEq])
    exact ⟨v₀, found₀, same.trans equal⟩
  · refine kept j w ?_
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, here, Ne.symm here] using read

/-- The update of the effective balances writes validators that keep their exit epochs. -/
private theorem exitsSame_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : ExitsSame state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine foldlM_ok_invariant (ExitsSame state) (fun current _ next kept step => ?_)
    (fun _ w read => ⟨w, read, rfl⟩) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨_, found, _, _, _, _, set⟩ := step
  exact kept.setValidatorAt found set rfl

private theorem blockKeeps_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : BlockKeeps state after :=
  ⟨StepKeeps.of_step (frame_processEffectiveBalanceUpdates computed).registryGrows
    (activeStep_processEffectiveBalanceUpdates computed),
    fun _ => ExitsStart.of_same (exitsSame_processEffectiveBalanceUpdates computed)⟩

private theorem blockKeeps_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      BlockKeeps state pass.1.state
  := fun computed => passPendingDeposits_of BlockKeeps BlockKeeps.refl
    (fun one two => one.trans two) (fun ok => blockKeeps_applyPendingDeposit ok) computed

private theorem blockKeeps_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    BlockKeeps state after := by
  rw [processEpochAltair_eq_run] at computed
  apply (EpochTrace.run_ok_iff.mp computed).transport BlockKeeps BlockKeeps.refl
    (fun a b => a.trans b)
  intro k _ a b ok
  have edge := EpochStage.action_cases.mp ok
  cases k <;> simp only [EpochStage.Edge, altair, ↓reduceDIte] at edge
  · exact blockKeeps_processJustificationAndFinalization edge
  · exact blockKeeps_processInactivityUpdates edge
  · exact BlockKeeps.of_step (frame_processRewardsAndPenalties edge).registryGrows
      (activeStep_processRewardsAndPenalties edge)
      (congrArg (·.validators.data) (processRewardsAndPenalties_frame edge))
  · exact blockKeeps_processRegistryUpdates edge
  · exact BlockKeeps.of_step (frame_processSlashings edge).registryGrows
      (activeStep_processSlashings edge)
      (congrArg (·.validators.data) (processSlashings_frame edge))
  · split at edge
    · exact BlockKeeps.of_step (frame_processEth1DataReset edge).registryGrows
        (activeStep_processEth1DataReset edge)
        (congrArg (·.validators.data) (processEth1DataReset_frame edge))
    · exact edge ▸ BlockKeeps.refl _
  · split at edge
    · unfold processPendingDeposits at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact (blockKeeps_passPendingDeposits ‹_›).trans BlockKeeps.of_validators
    · exact edge ▸ BlockKeeps.refl _
  · split at edge
    · exact BlockKeeps.of_validators
        (by rw [(processPendingConsolidations_kept edge).1])
        (frame_processPendingConsolidations edge).slot
    · exact edge ▸ BlockKeeps.refl _
  · split at edge
    · rw [processBuilderPendingPayments_eq edge]
      exact BlockKeeps.of_validators
    · exact edge ▸ BlockKeeps.refl _
  · exact blockKeeps_processEffectiveBalanceUpdates edge
  · obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    exact BlockKeeps.of_validators
  · obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    exact BlockKeeps.of_validators
  · split at edge
    · unfold processHistoricalSummariesUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact BlockKeeps.refl _
    · rename_i early
      exact ⟨StepKeeps.of_step (frame_processHistoricalRootsUpdate edge).registryGrows
        (activeStep_processHistoricalRootsUpdate edge),
        fun electra => absurd (Nat.le_trans (by decide) electra) early⟩
  · subst b
    exact BlockKeeps.of_validators
  · unfold processSyncCommitteeUpdates at edge
    simp only [bind, Except.bind, pure, Except.pure] at edge
    repeat' (split at edge <;> try cases edge)
    all_goals exact BlockKeeps.refl _
  · split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact BlockKeeps.of_validators
    · exact edge ▸ BlockKeeps.refl _
  · split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact BlockKeeps.of_validators
    · exact edge ▸ BlockKeeps.refl _

/-- The epoch step keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`.

That holds at every fork. -/
theorem activeKept_processEpoch
    (computed : processEpoch config checks state = .ok after) :
    ActiveKept (activityFixedEpoch state) state after := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processEpoch, altair, ↓reduceDIte] at computed
    exact (blockKeeps_processEpochAltair computed).1.2.2
  · exact activeKept_processEpoch_of_lt_altair (Nat.lt_of_not_le altair) computed

/-- The epoch step never shrinks the registry. -/
private theorem processEpoch_registryGrows
    (computed : processEpoch config checks state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size := by
  obtain ⟨_, justifiedOk, frame⟩ := processEpoch_frame computed
  rw [← (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1]
  exact frame.registryGrows

/-! ## Slots and upgrades -/

/-- One slot never shrinks the registry.

It keeps activity. -/
private theorem advanceSlot_kept (computed : advanceSlot config checks state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size ∧
      ActiveKept (activityFixedEpoch state) state after := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  -- The slot step writes neither the registry nor the slot.
  have validators : cached.validators = state.validators := by rw [cachedEq]
  have epoch : activityFixedEpoch cached = activityFixedEpoch state :=
    activityFixedEpoch_eq_of_slot (by rw [cachedEq])
  have first : ActiveKept (activityFixedEpoch state) state cached :=
    ActiveKept.of_validators (by rw [validators]) _
  suffices kept : cached.validators.data.size ≤ epoched.validators.data.size ∧
      ActiveKept (activityFixedEpoch cached) cached epoched by
    refine ⟨validators ▸ kept.1, first.trans ?_⟩
    exact (epoch ▸ kept.2).trans (ActiveKept.of_validators rfl _)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact ⟨processEpoch_registryGrows epochedOk, activeKept_processEpoch epochedOk⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨Nat.le_refl _, ActiveKept.refl _ _⟩

/-- One slot never shrinks the registry. -/
theorem advanceSlot_registryGrows (computed : advanceSlot config checks state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size :=
  (advanceSlot_kept computed).1

/-- Queueing a validator that is not yet active keeps its activation and exit epochs. -/
private theorem stepKeeps_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : StepKeeps state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact ((StepKeeps.of_validators : StepKeeps state _).trans
    (stepKeeps_setValidator (by exact found) (fun _ _ => by simp only [isActiveValidator])
      set₂)).trans StepKeeps.of_validators

private theorem stepKeeps_queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    StepKeeps state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · exact (blockKeeps_queueExcessActiveBalance (liftAccessor_ok.mp computed)).1
    · cases computed
      exact StepKeeps.refl _
  · cases computed
    exact StepKeeps.refl _

/-- The upgrade to Electra keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
private theorem activeKept_upgradeToElectra {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok post) :
    ActiveKept (activityFixedEpoch pre) pre post := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := computed
  have step := (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_queuePreActivation ok) queued).trans
    (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_queueCompoundingExcess ok) compounded)
  exact (ActiveKept.of_validators rfl _).trans
    step.2.2

/-- A block keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`, at every fork. -/
theorem activeKept_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ActiveKept (activityFixedEpoch state) state after :=
  (stepKeeps_processBlock computed).2.2

/-! ## The attestations of a block -/

/-- A step of a block before its attestations.

It is a block frame, and it never shrinks the registry.

It keeps the slot and activity.

Of the RANDAO mixes, it writes at most the one of the current epoch. -/
private structure BeforeVotes (state after : BeaconState preset fork) : Prop where
  frame : BlockFrame state after
  step : StepKeeps state after
  mixes : MixesKeptBut (getCurrentEpoch state) state after

/-- Every state is a step before votes to itself. -/
private theorem BeforeVotes.refl (state : BeaconState preset fork) : BeforeVotes state state :=
  ⟨BlockFrame.refl state, StepKeeps.refl state, fun _ _ => rfl⟩

/-- Two steps before votes in a row are one. -/
private theorem BeforeVotes.trans {first second third : BeaconState preset fork}
    (one : BeforeVotes first second) (two : BeforeVotes second third) :
    BeforeVotes first third := by
  have epoch : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, one.frame.slot]
  exact ⟨one.frame.trans two.frame, one.step.trans two.step,
    fun other apart => (two.mixes other (epoch ▸ apart)).trans (one.mixes other apart)⟩

/-- A block frame that never shrinks the registry and keeps the mixes is a step before votes. -/
private theorem BeforeVotes.of_mixes (frame : BlockFrame state after)
    (step : StepKeeps state after) (mixes : after.randaoMixes = state.randaoMixes) :
    BeforeVotes state after :=
  ⟨frame, step, fun _ _ => by rw [mixes]⟩

/-- A proposer slashing is a step before votes. -/
private theorem beforeVotes_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processProposerSlashing computed)
    (stepKeeps_processProposerSlashing computed)
    (payloadInputs_processProposerSlashing computed).randaoMixes

/-- An attester slashing is a step before votes. -/
private theorem beforeVotes_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processAttesterSlashing computed)
    (stepKeeps_processAttesterSlashing computed)
    (payloadInputs_processAttesterSlashing computed).randaoMixes

/-- The header step is a step before votes. -/
private theorem beforeVotes_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processBlockHeader computed)
    (blockKeeps_processBlockHeader computed).1
    (payloadInputs_processBlockHeader computed).randaoMixes

/-- The RANDAO step is a step before votes. -/
private theorem beforeVotes_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : BeforeVotes state after :=
  ⟨frame_processRandao computed, (blockKeeps_processRandao computed).1,
    mixesKeptBut_processRandao computed⟩

/-- The vote on the deposit contract is a step before votes. -/
private theorem beforeVotes_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processEth1Data computed) (stepKeeps_processEth1Data computed)
    (payloadInputs_processEth1Data computed).randaoMixes

/-- Where a list of attestations starts, each has the attesters of an earlier state.

The start must have the slot of the earlier state, and keep its activity up to its current epoch.

Of the RANDAO mixes, the start may differ from it at most at the one of its current epoch.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem getAttestingIndices_eq_of_foldlM {first last : BeaconState preset fork}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotEq : first.slot = state.slot) (active : ActiveKept (getCurrentEpoch state) state first)
    (mixes : MixesKeptBut (getCurrentEpoch state) state first)
    {parentSlot : Slot} {attestations : List (Attestation preset fork)}
    (attested :
      attestations.foldlM (processAttestation config checks · parentSlot ·) first = .ok last) :
    ∀ attestation ∈ attestations,
      getAttestingIndices first attestation = getAttestingIndices state attestation := by
  intro attestation member
  -- The fold runs the attestation at a state with the slot of the earlier state.
  obtain ⟨index, bound, found⟩ := List.getElem_of_mem member
  obtain ⟨mid, _, prefixOk, ok, -⟩ := (foldlM_ok_steps (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) attested).2 index bound
  rw [found] at ok
  have slot : mid.slot = state.slot :=
    foldlM_ok_invariant (fun next : BeaconState preset fork => next.slot = state.slot)
      (fun _ _ _ holds ok => (frame_processAttestation ok).slot.trans holds) slotEq prefixOk
  have current : getCurrentEpoch mid = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  have previous : getPreviousEpoch mid = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  have previousNat := getPreviousEpoch_toNat state
  have recent := processAttestation_slotEpoch ok
  rw [previous, current] at recent
  have low : computeEpochAtSlot preset attestation.data.slot ≤ getCurrentEpoch state := by
    rcases recent with same | same <;> rw [same]
    · exact getPreviousEpoch_le state
    · exact UInt64.le_refl _
  have high : (getCurrentEpoch state).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat + 1 := by
    rcases recent with same | same <;> rw [same] <;> omega
  exact getAttestingIndices_eq_of_activeKept apart (active.mono low) mixes low high

/-- The steps of a block before its attestations are a step before votes. -/
private theorem beforeVotes_attestationsStart {engine : ExecutionEngine preset fork}
    {state input proposersDone first : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input)
    (proposers : block.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) input = .ok proposersDone)
    (slashings : block.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposersDone = .ok first) :
    BeforeVotes state first :=
  (started.step_of BeforeVotes BeforeVotes.refl BeforeVotes.trans
    (fun _ ok => BeforeVotes.of_mixes (frame_processParentExecutionPayload ok)
      ((blockKeeps_processParentExecutionPayload ok).1)
      (payloadInputs_processParentExecutionPayload ok).randaoMixes)
    beforeVotes_processBlockHeader
    (fun _ ok => BeforeVotes.of_mixes (frame_processBlockExecution ok)
      (stepKeeps_processBlockExecution ok) (randaoMixes_processBlockExecution ok))
    beforeVotes_processRandao (fun _ ok => beforeVotes_processEth1Data ok)).trans <|
    (foldlM_ok_steps BeforeVotes BeforeVotes.refl BeforeVotes.trans
      (fun _ _ _ ok => beforeVotes_processProposerSlashing ok) proposers).1.trans <|
    (foldlM_ok_steps BeforeVotes BeforeVotes.refl BeforeVotes.trans
      (fun _ _ _ ok => beforeVotes_processAttesterSlashing ok) slashings).1

/-- Where the attestations of a block start, each has the attesters of the state before it.

The start is the state after the operations input and the slashings of the block.

The attestations succeed when they are processed in order from that start.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem getAttestingIndices_attestationsStart
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {engine : ExecutionEngine preset fork} {state : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    {input proposersDone first last : BeaconState preset fork}
    (started : OperationsInput config checks engine state block input)
    (proposers : block.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) input = .ok proposersDone)
    (slashings : block.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposersDone = .ok first)
    (attested : block.body.attestations.data.toList.foldlM
      (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok last)
    {attestation : Attestation preset fork}
    (member : attestation ∈ block.body.attestations.data.toList) :
    getAttestingIndices first attestation = getAttestingIndices state attestation :=
  let head := beforeVotes_attestationsStart started proposers slashings
  getAttestingIndices_eq_of_foldlM apart head.frame.slot
    (head.step.2.2.mono (getCurrentEpoch_le_activityFixedEpoch _)) head.mixes attested
    attestation member

/-- A block runs its attestations in order, between two block frames.

Where they start, the attesters of each of them are those of the state before the block.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem processBlock_attestationSplit
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ first last, BlockFrame state first ∧
      (∀ attestation ∈ block.body.attestations.data,
        getAttestingIndices first attestation = getAttestingIndices state attestation) ∧
      block.body.attestations.data.toList.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok last ∧
      BlockFrame last after := by
  obtain ⟨input, proposersDone, first, last, started, proposers, slashings, attested, tail⟩ :=
    processBlock_folds computed
  exact ⟨first, last, (beforeVotes_attestationsStart started proposers slashings).frame,
    fun _ member => getAttestingIndices_attestationsStart apart started proposers slashings
      attested (Array.mem_toList_iff.mpr member), attested, tail⟩

/-- One slot keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`, at every fork. -/
theorem activeKept_advanceSlot
    (computed : advanceSlot config checks state = .ok after) :
    ActiveKept (activityFixedEpoch state) state after :=
  (advanceSlot_kept computed).2

/-- An upgrade keeps activity in each epoch up to the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
theorem activeKept_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    ActiveKept (activityFixedEpoch pre.state) pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact ActiveKept.of_validators (upgradeToAltair_spec upgraded).1 _
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ActiveKept.of_validators rfl _
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact activeKept_upgradeToElectra upgraded
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact ActiveKept.of_validators (upgradeToFulu_spec upgraded).1 _
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact ActiveKept.of_validators (upgradeToGloas_spec upgraded).1 _
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact ActiveKept.of_validators (upgradeHezeFields_lists _).1 _
  all_goals
    simp only [upgradeNext] at computed
    cases computed

/-- One step of a chain never shrinks the registry, nor moves the current epoch back.

It keeps activity. -/
private theorem chainStep_kept {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size ∧
      ActiveKept (activityFixedEpoch forked.state) forked.state after.state ∧
      getCurrentEpoch forked.state ≤ getCurrentEpoch after.state := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    -- The upgrades keep the slot, the registry and activity.
    obtain ⟨grows, active, slot⟩ := processUpgrades_induction
      (property := fun upgraded =>
        advanced.validators.data.size ≤ upgraded.state.validators.data.size ∧
          ActiveKept (activityFixedEpoch advanced) advanced upgraded.state ∧
          upgraded.state.slot = advanced.slot)
      (fun {pre} _ ⟨grows, active, slot⟩ stepOk => by
        have frame := upgradeFrame_upgradeNext stepOk
        have epoch : activityFixedEpoch pre.state = activityFixedEpoch advanced :=
          activityFixedEpoch_eq_of_slot slot
        exact ⟨Nat.le_trans grows frame.registryGrows,
          active.trans (epoch ▸ activeKept_upgradeNext stepOk), frame.slot.trans slot⟩)
      ⟨Nat.le_refl _, ActiveKept.refl _ _, rfl⟩ upgraded
    obtain ⟨advancedGrows, advancedActive⟩ := advanceSlot_kept advancedOk
    -- The slot moves on by one, so the current epoch does not move back.
    have later : getCurrentEpoch forked.state ≤ getCurrentEpoch advanced := by
      have sum := advanceSlot_slot advancedOk
      apply UInt64.le_iff_toNat_le.mpr
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, sum]
      exact Nat.div_le_div_right (Nat.le_succ _)
    have epoch : getCurrentEpoch after.state = getCurrentEpoch advanced := by
      simp only [getCurrentEpoch, slot]
    exact ⟨Nat.le_trans advancedGrows grows,
      advancedActive.trans (active.mono (activityFixedEpoch_mono later)), epoch ▸ later⟩
  | @block _ blockState blockAfter engine signed validateResult computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    have kept := stepKeeps_processBlock blockOk
    have epoch : getCurrentEpoch blockAfter = getCurrentEpoch blockState := by
      simp only [getCurrentEpoch, (frame_processBlock blockOk).slot]
    exact ⟨kept.1, kept.2.2, UInt64.le_of_eq epoch.symm⟩

/-- A run of steps of a chain never shrinks the registry.

It keeps activity. -/
private theorem chainSteps_kept {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    first.state.validators.data.size ≤ last.state.validators.data.size ∧
      ActiveKept (activityFixedEpoch first.state) first.state last.state := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨Nat.le_refl _, ActiveKept.refl _ _⟩
  | head step _ more =>
    obtain ⟨grows, active, later⟩ := chainStep_kept step
    exact ⟨Nat.le_trans grows more.1,
      active.trans (more.2.mono (activityFixedEpoch_mono later))⟩

/-- One step of a chain keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
theorem ChainStep.activeKept {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    ActiveKept (activityFixedEpoch forked.state) forked.state after.state :=
  (chainStep_kept step).2.1

/-- A run of steps of a chain keeps activity up to the fixed epoch of its start.

That is the current epoch of its start plus `MAX_SEED_LOOKAHEAD`. -/
theorem activeKept_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    ActiveKept (activityFixedEpoch first.state) first.state last.state :=
  (chainSteps_kept steps).2

/-- One step of a chain does not move the current epoch back. -/
theorem ChainStep.currentEpoch_le {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    getCurrentEpoch forked.state ≤ getCurrentEpoch after.state :=
  (chainStep_kept step).2.2

/-- A run of steps of a chain does not move the current epoch back. -/
theorem currentEpoch_le_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    getCurrentEpoch first.state ≤ getCurrentEpoch last.state := by
  induction steps with
  | refl => exact UInt64.le_refl _
  | tail _ step more => exact UInt64.le_trans more step.currentEpoch_le

/-- One step of a chain never shrinks the registry. -/
theorem ChainStep.registryGrows {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size :=
  (chainStep_kept step).1

/-- A run of steps of a chain never shrinks the registry. -/
theorem registryGrows_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    first.state.validators.data.size ≤ last.state.validators.data.size :=
  (chainSteps_kept steps).1

/-! ## Exits start from activity at every chain step -/

private theorem ExitsStart.of_data_right {f g h : Fork} {state : BeaconState preset f}
    {middle : BeaconState preset g} {after : BeaconState preset h}
    (starts : ExitsStart state middle)
    (same : after.validators.data = middle.validators.data := by rfl) : ExitsStart state after := by
  intro i v w found read far assigned
  rw [same] at read
  exact starts i v w found read far assigned

/-- One slot starts exits only of activated validators, from Electra. -/
private theorem exitsStart_advanceSlot (electra : .pectra ≤ fork)
    (computed : advanceSlot config checks state = .ok after) : ExitsStart state after := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : BlockKeeps state cached :=
    BlockKeeps.of_validators (by rw [cachedEq]) (by rw [cachedEq])
  unfold epochIfLast at epochedOk
  split at epochedOk
  · have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
    simp only [processEpoch, altair, ↓reduceDIte] at epochedOk
    exact ExitsStart.of_data_right
      ((first.trans (blockKeeps_processEpochAltair epochedOk)).2 electra)
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ExitsStart.of_data_right (first.2 electra)

/-- From Electra, an upgrade keeps the validators as the same sequence. -/
theorem upgradeNext_validators_of_electra {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.validators.data = pre.state.validators.data := by
  obtain ⟨fork, state⟩ := pre
  change .pectra ≤ fork at electra
  cases fork
  case phase0 | altair | bellatrix | shapella | dencun => exact absurd electra (by decide)
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToFulu_spec upgraded).1
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToGloas_spec upgraded).1
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact (upgradeHezeFields_lists _).1
  all_goals
    simp only [upgradeNext] at computed
    cases computed

/-- From Electra, a chain step assigns an exit only to a validator activated by its start epoch. -/
theorem ChainStep.exit_assigned_activated {forked after : ForkedBeaconState preset}
    (electra : .pectra ≤ forked.fork) (step : ChainStep config checks forked after)
    {i : Nat} {v w : Validator} (before : forked.state.validators.data[i]? = some v)
    (later : after.state.validators.data[i]? = some w) (unset : v.exitEpoch = FAR_FUTURE_EPOCH)
    (set : w.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    v.activationEpoch ≤ getCurrentEpoch forked.state := by
  have starts : ExitsStart forked.state after.state := by
    cases step with
    | slot computed =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
      have same := processUpgrades_induction
        (property := fun upgraded => .pectra ≤ upgraded.fork ∧
          upgraded.state.validators.data = advanced.validators.data)
        (fun {pre post} ⟨kept, validators⟩ stepOk => ⟨Nat.le_trans kept (Nat.le_of_lt post.2),
          (upgradeNext_validators_of_electra kept stepOk).trans validators⟩)
        (forked := (⟨_, advanced⟩ : ForkedBeaconState preset)) ⟨electra, rfl⟩ upgraded
      exact ExitsStart.of_data_right (exitsStart_advanceSlot electra advancedOk) same.2
    | block engine signed validateResult computed =>
      obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
      exact (blockKeeps_processBlock blockOk).2 electra
  exact starts i v w before later unset set

/-! ## Activity through block operations -/

/-- The block header keeps the slot and activity. -/
theorem activeStep_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : ActiveStep state after :=
  ((blockKeeps_processBlockHeader computed).1).2

/-- The execution part of a block keeps the slot and activity. -/
theorem activeStep_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    ActiveStep state after :=
  (stepKeeps_processBlockExecution computed).2

/-- The RANDAO reveal keeps the slot and activity. -/
theorem activeStep_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : ActiveStep state after :=
  (blockKeeps_processRandao computed).1.2

/-- The vote on the deposit contract keeps the slot and activity. -/
theorem activeStep_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : ActiveStep state after :=
  (stepKeeps_processEth1Data computed).2

/-- A proposer slashing keeps the slot and activity. -/
theorem activeStep_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    ActiveStep state after :=
  (stepKeeps_processProposerSlashing computed).2

/-- An attester slashing keeps the slot and activity. -/
theorem activeStep_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ActiveStep state after :=
  (stepKeeps_processAttesterSlashing computed).2

/-- An attestation keeps the slot and activity. -/
theorem activeStep_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ActiveStep state after :=
  (stepKeeps_processAttestation computed).2

/-- A deposit keeps the slot and activity. -/
theorem activeStep_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    ActiveStep state after :=
  (stepKeeps_processDeposit computed).2

/-- A voluntary exit keeps the slot and activity. -/
theorem activeStep_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    ActiveStep state after :=
  (stepKeeps_processVoluntaryExit computed).2

/-- A change to an execution address keeps the slot and activity. -/
theorem activeStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    ActiveStep state after :=
  (stepKeeps_processBlsToExecutionChange computed).2

/-- A deposit request keeps the slot and activity. -/
theorem activeStep_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    ActiveStep state after :=
  (blockKeeps_processDepositRequest computed).1.2

/-- A withdrawal request keeps the slot and activity. -/
theorem activeStep_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    ActiveStep state after :=
  (blockKeeps_processWithdrawalRequest computed).1.2

/-- A consolidation request keeps the slot and activity. -/
theorem activeStep_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    ActiveStep state after :=
  (blockKeeps_processConsolidationRequest computed).1.2

end EthLib.Consensus
