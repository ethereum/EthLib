module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Mutators
public import EthLib.Consensus.Proofs.Churn
public import EthLib.Consensus.Credentials
public import EthLib.Serialization.Proofs.Ssz.Typed.RootedList

/-!
# Proofs: state mutators

Every mutator keeps the number of validators and the number of balances.

So a state whose registry and balances have one length keeps that property.

Raising a balance succeeds exactly when the balance exists and the sum stays below `2^64`.

Lowering an existing balance always succeeds, and the result is zero when the amount is larger.

A validator that starts to exit may withdraw a fixed delay after its exit epoch, with no overflow.

Before Electra, an exit epoch other than the far future held fewer exits than the churn limit.

Slashing a validator sets its slashed flag and changes no flag of another validator.

From Gloas, slashing a validator cancels exactly the builder payments of the blocks it proposed.

From Electra, the balance of a validator above the activation balance moves to the pending deposits.

The balance and the amounts added to the queue keep their sum.

A validator that switches to compounding credentials then has compounding credentials.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Two states with registries of one size and balances of one size. -/
def SameSizes (before after : BeaconState preset fork) : Prop :=
  after.validators.data.size = before.validators.data.size ∧
    after.balances.data.size = before.balances.data.size

theorem SameSizes.refl (state : BeaconState preset fork) : SameSizes state state :=
  ⟨rfl, rfl⟩

theorem SameSizes.trans {first second third : BeaconState preset fork}
    (one : SameSizes first second) (two : SameSizes second third) : SameSizes first third :=
  ⟨two.1.trans one.1, two.2.trans one.2⟩

/-- Setting a balance in the balances keeps the sizes. -/
theorem sameSizes_putBalance (state : BeaconState preset fork) {index : Nat}
    (inside : index < state.balances.data.size) (balance : Gwei) :
    SameSizes state (state.putBalance index inside balance) := by
  simp [SameSizes, BeaconState.putBalance]

/-- Setting a validator in the registry keeps the sizes. -/
theorem sameSizes_putValidator (state : BeaconState preset fork) {index : Nat}
    (inside : index < state.validators.data.size) (validator : Validator) :
    SameSizes state (state.putValidator index inside validator) := by
  simp [SameSizes, BeaconState.putValidator]

/-- A balance that is set is set in the balances. -/
theorem setBalance_ok {state after : BeaconState preset fork} {index : ValidatorIndex}
    {balance : Gwei} (set : state.setBalance index balance = .ok after) :
    ∃ inside, after = state.putBalance index.toNat inside balance := by
  unfold BeaconState.setBalance at set
  split at set
  · rename_i inside
    cases set
    exact ⟨inside, rfl⟩
  · cases set

/-- A successful write at a plain position uses that position, without reduction modulo `2^64`. -/
theorem setValidatorAt_ok {state after : BeaconState preset fork} {position : Nat}
    {validator : Validator} (set : state.setValidatorAt position validator = .ok after) :
    ∃ inside : position < state.validators.data.size,
      after = state.putValidator position inside validator := by
  unfold BeaconState.setValidatorAt at set
  split at set
  · cases set
    exact ⟨_, rfl⟩
  · simp [bind_ok_iff, throw, throwThe, MonadExceptOf.throw] at set

/-- A write at a validator index is the write at the position that the index names. -/
theorem setValidator_eq_setValidatorAt (state : BeaconState preset fork) (index : ValidatorIndex)
    (validator : Validator) :
    state.setValidator index validator = state.setValidatorAt index.toNat validator := by
  unfold BeaconState.setValidator BeaconState.setValidatorAt
  split
  · rfl
  · simp [liftArith, ofNatChecked_toNat, bind, Except.bind, Except.mapError, throw, throwThe,
      MonadExceptOf.throw]

/-- A validator that is set is set in the registry. -/
theorem setValidator_ok {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (set : state.setValidator index validator = .ok after) :
    ∃ inside, after = state.putValidator index.toNat inside validator :=
  setValidatorAt_ok (by rwa [← setValidator_eq_setValidatorAt])

/-- Setting a balance keeps the slot. -/
theorem setBalance_slot {state after : BeaconState preset fork} {index : ValidatorIndex}
    {balance : Gwei} (set : state.setBalance index balance = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- Setting a validator keeps the slot. -/
theorem setValidator_slot {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (set : state.setValidator index validator = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- Setting a balance keeps the sizes. -/
theorem sameSizes_setBalance {state after : BeaconState preset fork} {index : ValidatorIndex}
    {balance : Gwei} (set : state.setBalance index balance = .ok after) :
    SameSizes state after := by
  obtain ⟨inside, rfl⟩ := setBalance_ok set
  exact sameSizes_putBalance state inside balance

/-- A write at a plain position keeps the registry and balance lengths. -/
theorem sameSizes_setValidatorAt {state after : BeaconState preset fork} {position : Nat}
    {validator : Validator} (set : state.setValidatorAt position validator = .ok after) :
    SameSizes state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  exact sameSizes_putValidator state inside validator

/-- Setting a validator keeps the sizes. -/
theorem sameSizes_setValidator {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (set : state.setValidator index validator = .ok after) :
    SameSizes state after :=
  sameSizes_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])


/-- A read at a plain position succeeds exactly when that position holds the validator. -/
theorem getValidatorAt_eq_ok_iff {state : BeaconState preset fork} {position : Nat}
    {validator : Validator} :
    getValidatorAt state position = .ok validator ↔
      state.validators.data[position]? = some validator := by
  unfold getValidatorAt
  split <;> simp_all [bind_ok_iff, throw, throwThe, MonadExceptOf.throw]

/-- A validator read at a plain position belongs to the registry. -/
theorem mem_of_getValidatorAt {state : BeaconState preset fork} {position : Nat}
    {validator : Validator} (computed : getValidatorAt state position = .ok validator) :
    validator ∈ state.validators.data :=
  Array.mem_of_getElem? (getValidatorAt_eq_ok_iff.mp computed)

/-- A read at a plain position succeeds exactly when that position holds the balance. -/
theorem getBalanceAt_eq_ok_iff {state : BeaconState preset fork} {position : Nat}
    {balance : Gwei} :
    getBalanceAt state position = .ok balance ↔ state.balances.data[position]? = some balance := by
  unfold getBalanceAt
  split <;> simp_all [bind_ok_iff, throw, throwThe, MonadExceptOf.throw]

/-- A read at a validator index is the read at the position that the index names. -/
theorem getValidator_eq_getValidatorAt (state : BeaconState preset fork) (index : ValidatorIndex) :
    getValidator state index = getValidatorAt state index.toNat := by
  unfold getValidator getValidatorAt
  split
  · rfl
  · simp [liftArith, ofNatChecked_toNat, bind, Except.bind, Except.mapError, throw, throwThe,
      MonadExceptOf.throw]

/-- A balance read at a validator index is the read at the position that the index names. -/
theorem getBalance_eq_getBalanceAt (state : BeaconState preset fork) (index : ValidatorIndex) :
    getBalance state index = getBalanceAt state index.toNat := by
  unfold getBalance getBalanceAt
  split
  · rfl
  · simp [liftArith, ofNatChecked_toNat, bind, Except.bind, Except.mapError, throw, throwThe,
      MonadExceptOf.throw]

/-- Raising a balance sets a balance. -/
theorem increaseBalance_ok {state after : BeaconState preset fork} {index : ValidatorIndex}
    {delta : Gwei} (computed : increaseBalance state index delta = .ok after) :
    ∃ balance, state.setBalance index balance = .ok after := by
  simp only [increaseBalance, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨_, _, balance, _, set⟩ := computed
  exact ⟨balance, set⟩

/-- Lowering a balance sets a balance. -/
theorem decreaseBalance_ok {state after : BeaconState preset fork} {index : ValidatorIndex}
    {delta : Gwei} (computed : decreaseBalance state index delta = .ok after) :
    ∃ balance, state.setBalance index balance = .ok after := by
  simp only [decreaseBalance, bind_ok_iff] at computed
  obtain ⟨_, _, set⟩ := computed
  exact ⟨_, set⟩

/-- Raising a balance succeeds exactly when the index names a balance and the sum is below `2^64`.

The state then holds the sum in place of that balance. -/
theorem increaseBalance_eq_ok_iff {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} :
    increaseBalance state index delta = .ok after ↔
      ∃ inside : index.toNat < state.balances.data.size,
        state.balances.data[index.toNat].toNat + delta.toNat < 2 ^ 64 ∧
          after = state.putBalance index.toNat inside
            (state.balances.data[index.toNat] + delta) := by
  unfold increaseBalance getBalance BeaconState.setBalance
  by_cases inside : index.toNat < state.balances.data.size
  · simp only [inside, Array.getElem?_eq_getElem, bind_ok_iff, liftArith, mapError_ok_iff,
      addChecked, exists_true_left]
    by_cases fits : state.balances.data[index.toNat].toNat + delta.toNat < 2 ^ 64
    · simp [fits, eq_comm]
    · simp [fits]
  · simp [inside, bind, Except.bind]

/-- Lowering a balance succeeds exactly when the index names a balance.

The state then holds the balance minus the amount, or zero if the amount is larger. -/
theorem decreaseBalance_eq_ok_iff {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} :
    decreaseBalance state index delta = .ok after ↔
      ∃ inside : index.toNat < state.balances.data.size,
        after = state.putBalance index.toNat inside
          (saturatingSub state.balances.data[index.toNat] delta) := by
  unfold decreaseBalance getBalance BeaconState.setBalance
  by_cases inside : index.toNat < state.balances.data.size
  · simp [inside, bind, Except.bind, eq_comm]
  · simp [inside, bind, Except.bind]

/-- Raising a balance keeps the sizes. -/
theorem sameSizes_increaseBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : increaseBalance state index delta = .ok after) :
    SameSizes state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  exact sameSizes_setBalance set

/-- Lowering a balance keeps the sizes. -/
theorem sameSizes_decreaseBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : decreaseBalance state index delta = .ok after) :
    SameSizes state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  exact sameSizes_setBalance set

/-- The exit queue changes neither the registry nor the balances. -/
theorem exitQueue_validators {config : Config} {state after : BeaconState preset fork}
    {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    after.validators = state.validators ∧ after.balances = state.balances := by
  unfold exitQueue at computed
  split at computed
  · exact (computeExitEpochAndUpdateChurn_earliest computed).2
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact ⟨rfl, rfl⟩

/-- The exit queue changes the state only in its exit churn, which exists from Electra.

Before Electra it keeps the state. -/
theorem exitQueue_eq {config : Config} {state after : BeaconState preset fork}
    {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    ∃ left earliest,
      after = { state with exitBalanceToConsume := left, earliestExitEpoch := earliest } := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact ⟨_, _, rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact ⟨_, _, rfl⟩

/-- The steps of an exit.

A validator that has started to exit stays the same.

Otherwise the exit queue gives its exit epoch, and its withdrawable epoch follows a delay later. -/
theorem initiateValidatorExit_ok {config : Config} {state after : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config state index = .ok after) :
    ∃ validator, getValidator state index = .ok validator ∧
      ((validator.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ after = state) ∨
        (validator.exitEpoch = FAR_FUTURE_EPOCH ∧ ∃ queued exitEpoch withdrawableEpoch,
          exitQueue config state validator.effectiveBalance = .ok (queued, exitEpoch) ∧
          addChecked exitEpoch config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok withdrawableEpoch ∧
          queued.setValidator index { validator with exitEpoch, withdrawableEpoch } =
            .ok after)) := by
  simp only [initiateValidatorExit, bind_ok_iff] at computed
  obtain ⟨validator, found, rest⟩ := computed
  refine ⟨validator, found, ?_⟩
  split at rest
  · rename_i started
    simp only [pure, Except.pure, Except.ok.injEq] at rest
    exact .inl ⟨by simpa using started, rest.symm⟩
  · rename_i notStarted
    simp only [bind_ok_iff, liftArith, mapError_ok_iff] at rest
    obtain ⟨⟨queued, exitEpoch⟩, queue, withdrawableEpoch, summed, final⟩ := rest
    exact .inr ⟨by simpa using notStarted, queued, exitEpoch, withdrawableEpoch, queue, summed,
      final⟩

/-- Starting an exit keeps the sizes. -/
theorem sameSizes_initiateValidatorExit {config : Config} {state after : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config state index = .ok after) :
    SameSizes state after := by
  obtain ⟨validator, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact SameSizes.refl _
  · obtain ⟨validators, balances⟩ := exitQueue_validators queue
    refine (?_ : SameSizes state queued).trans (sameSizes_setValidator set)
    exact ⟨by rw [validators], by rw [balances]⟩

/-- The last step of a slashing keeps the registry and the balances. -/
theorem slashValidator_last {last after : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    after.validators = last.validators ∧ after.balances = last.balances := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split <;> exact ⟨rfl, rfl⟩

/-- The steps of a successful slashing, in order.

The validator exits, and its record in the exited state is read.

Its withdrawal is delayed and it is marked slashed.

Its effective balance is added to the slashed balance of the epoch, in the slashings vector.

Its balance pays the first penalty, and the proposer of the slot is read.

The proposer and the whistleblower are paid.

From Gloas the pending builder payments of its blocks are cancelled. -/
theorem slashValidator_ok {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    ∃ exited validator withdrawable marked slashed total slashings lowered proposer reward raised
      last,
      initiateValidatorExit config state slashedIndex = .ok exited ∧
      getValidator exited slashedIndex = .ok validator ∧
      addChecked (getCurrentEpoch state) preset.EPOCHS_PER_SLASHINGS_VECTOR = .ok withdrawable ∧
      exited.setValidator slashedIndex
        { validator with
          slashed := true
          withdrawableEpoch := max validator.withdrawableEpoch withdrawable } = .ok marked ∧
      readCircular marked.slashings.elements (getCurrentEpoch state) = .ok slashed ∧
      addChecked slashed validator.effectiveBalance = .ok total ∧
      writeCircularRooted marked.slashings (getCurrentEpoch state) total = .ok slashings ∧
      decreaseBalance { marked with slashings } slashedIndex
        (validator.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT) =
          .ok lowered ∧
      getBeaconProposerIndex lowered = .ok proposer ∧
      proposerShare preset fork
        (validator.effectiveBalance / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT) =
          .ok reward ∧
      increaseBalance lowered proposer reward = .ok raised ∧
      increaseBalance raised (whistleblowerIndex.getD proposer)
        (validator.effectiveBalance / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT -
          reward) = .ok last ∧
      after = if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas slashedIndex
        else last := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, withdrawable, delay, marked, markedOk, slashed,
    slashedOk, total, totalOk, slashings, slashingsOk, lowered, loweredOk, proposer, proposerOk,
    reward, rewardOk, raised, raisedOk, last, lastOk, done⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at done
  exact ⟨exited, validator, withdrawable, marked, slashed, total, slashings, lowered, proposer,
    reward, raised, last, exitedOk, found, delay, markedOk, slashedOk, totalOk, slashingsOk,
    loweredOk, proposerOk, rewardOk, raisedOk, lastOk, done.symm⟩

/-- Slashing a validator keeps the sizes. -/
theorem sameSizes_slashValidator {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, last, exitedOk, -, -, markedOk, -, -, -, lowered, -, -,
    raised, final, done⟩ := slashValidator_ok computed
  have cancelled := slashValidator_last (last := last) (after := after) (index := slashedIndex)
    (by subst done; rfl)
  refine (sameSizes_initiateValidatorExit exitedOk).trans (SameSizes.trans ?_
    ((sameSizes_decreaseBalance lowered).trans ((sameSizes_increaseBalance raised).trans
      ((sameSizes_increaseBalance final).trans ⟨by rw [cancelled.1], by rw [cancelled.2]⟩))))
  exact (sameSizes_setValidator markedOk).trans ⟨rfl, rfl⟩

/-- The running maximum of the exit epochs is at least its start and each exit epoch it reads. -/
theorem le_foldl_maxExitEpoch (validators : List Validator) (start : Epoch) :
    start ≤ validators.foldl (fun latest validator => max latest validator.exitEpoch) start ∧
      ∀ validator ∈ validators,
        validator.exitEpoch ≤
          validators.foldl (fun latest validator => max latest validator.exitEpoch) start := by
  induction validators generalizing start with
  | nil => exact ⟨UInt64.le_refl _, by simp⟩
  | cons first rest ih =>
    obtain ⟨startLe, restLe⟩ := ih (max start first.exitEpoch)
    have leMax : start ≤ max start first.exitEpoch ∧ first.exitEpoch ≤ max start first.exitEpoch := by
      simp only [max]
      split <;> simp_all [UInt64.le_iff_toNat_le] <;> omega
    have trans : ∀ a b c : UInt64, a ≤ b → b ≤ c → a ≤ c := fun a b c ab bc => by
      rw [UInt64.le_iff_toNat_le] at *; omega
    refine ⟨trans _ _ _ leMax.1 startLe, fun validator mem => ?_⟩
    rcases List.mem_cons.mp mem with rfl | inRest
    · exact trans _ _ _ leMax.2 startLe
    · exact restLe validator inRest

/-- Before Electra, take an exit epoch of the queue other than the far future.

It held fewer exits than the churn limit, or none if the limit is zero.

So after the exit that takes it, it holds at most the churn limit, or one. -/
theorem exitQueueEpoch_churn {config : Config} {state : BeaconState preset fork} {epoch : Epoch}
    (computed : exitQueueEpoch config state = .ok epoch) (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (state.validators.data.toList.filter (·.exitEpoch == epoch)).length <
      max 1 (getValidatorChurnLimit config state).toNat := by
  simp only [exitQueueEpoch, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  rename_i earliest _
  split at computed
  · rename_i _ full
    have sum := (addChecked_ok_iff.mp (mapError_ok_iff.mp computed)).2
    -- No validator exits at the epoch after the latest exit epoch.
    have none : state.validators.data.toList.filter (·.exitEpoch == epoch) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro validator mem same
      have sameEpoch : validator.exitEpoch = epoch := by simpa using same
      by_cases far : validator.exitEpoch = FAR_FUTURE_EPOCH
      · exact finite (sameEpoch ▸ far)
      have le := (le_foldl_maxExitEpoch
        (state.validators.data.toList.filter (·.exitEpoch != FAR_FUTURE_EPOCH)) earliest).2
        validator (List.mem_filter.mpr ⟨mem, by simp [far]⟩)
      rw [sameEpoch, UInt64.le_iff_toNat_le] at le
      have one : (1 : UInt64).toNat = 1 := rfl
      omega
    rw [none, List.length_nil]
    omega
  · rename_i _ notFull
    cases computed
    omega

/-- A state with the same registry reads the same validators. -/
theorem getValidator_of_validators_eq {state after : BeaconState preset fork}
    (same : after.validators = state.validators) (index : ValidatorIndex) :
    getValidator after index = getValidator state index := by
  simp [getValidator, same]

/-- A read of a balance returns the balance at its position of the list. -/
theorem getBalance_eq_ok_iff {state : BeaconState preset fork} {index : ValidatorIndex}
    {balance : Gwei} :
    getBalance state index = .ok balance ↔ state.balances.data[index.toNat]? = some balance := by
  rw [getBalance_eq_getBalanceAt]
  exact getBalanceAt_eq_ok_iff

/-- The lookup returns a validator exactly when it is the one at its index of the registry. -/
theorem getValidator_eq_ok_iff {state : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} :
    getValidator state index = .ok validator ↔
      state.validators.data[index.toNat]? = some validator := by
  rw [getValidator_eq_getValidatorAt]
  exact getValidatorAt_eq_ok_iff

/-- The slashed flag of a validator, or the error of an index outside the registry. -/
def slashedFlag (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Bool :=
  (getValidator state index).map (·.slashed)

/-- A replaced validator is read back at its index. -/
theorem getValidator_putValidator_self {state : BeaconState preset fork}
    {index : ValidatorIndex} (inside : index.toNat < state.validators.data.size)
    (validator : Validator) :
    getValidator (state.putValidator index.toNat inside validator) index = .ok validator := by
  simp [getValidator, BeaconState.putValidator, inside]

/-- Replacing a validator leaves the validators at other indices. -/
theorem getValidator_putValidator_of_ne {state : BeaconState preset fork}
    {index other : ValidatorIndex} (inside : index.toNat < state.validators.data.size)
    (distinct : other ≠ index) (validator : Validator) :
    getValidator (state.putValidator index.toNat inside validator) other =
      getValidator state other := by
  have : index.toNat ≠ other.toNat := fun same => distinct (UInt64.toNat_inj.mp same).symm
  simp [getValidator, BeaconState.putValidator, this]

/-- A replaced validator is read back at its index. -/
theorem getValidator_setValidator_self {state after : BeaconState preset fork}
    {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) :
    getValidator after index = .ok validator := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  exact getValidator_putValidator_self inside validator

/-- Replacing a validator leaves the validators at other indices. -/
theorem getValidator_setValidator_of_ne {state after : BeaconState preset fork}
    {index other : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) (distinct : other ≠ index) :
    getValidator after other = getValidator state other := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  exact getValidator_putValidator_of_ne inside distinct validator

/-- A validator that starts to exit may withdraw a fixed delay after its exit epoch.

The sum does not wrap, since an exit whose sum reaches `2^64` fails. -/
theorem initiateValidatorExit_withdrawableEpoch {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (notExiting : validator.exitEpoch = FAR_FUTURE_EPOCH)
    (computed : initiateValidatorExit config state index = .ok after) :
    ∃ exited, getValidator after index = .ok exited ∧
      exited.withdrawableEpoch.toNat =
        exited.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  obtain ⟨read, readOk, ⟨started, _⟩ | ⟨_, queued, exitEpoch, withdrawableEpoch, queue, summed,
    set⟩⟩ := initiateValidatorExit_ok computed
  · rw [found] at readOk
    cases readOk
    exact absurd notExiting started
  · rw [found] at readOk
    cases readOk
    have sum := (addChecked_ok_iff.mp summed).2
    refine ⟨{ validator with exitEpoch, withdrawableEpoch }, ?_, sum⟩
    rw [← getValidator_of_validators_eq (exitQueue_validators queue).1] at found
    exact getValidator_setValidator_self set

/-- Raising a balance leaves the registry. -/
theorem increaseBalance_validators {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    after.validators = state.validators := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- Lowering a balance leaves the registry. -/
theorem decreaseBalance_validators {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    after.validators = state.validators := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- Raising a balance adds the amount at its own index, without overflow, and keeps the others. -/
theorem balance_increaseBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) {j : Nat} {balance : Gwei}
    (found : state.balances.data[j]? = some balance) :
    ∃ raised, after.balances.data[j]? = some raised ∧
      raised.toNat = balance.toNat + if index.toNat = j then delta.toNat else 0 := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  by_cases same : index.toNat = j
  · subst same
    rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
    subst found
    exact ⟨state.balances.data[index.toNat] + delta, by simp [BeaconState.putBalance],
      by simp [toNat_add_of_lt fits]⟩
  · exact ⟨balance, by simp [BeaconState.putBalance, same, found], by simp [same]⟩

/-- Lowering a balance subtracts the amount at its own index, stopping at zero.

It keeps the other balances. -/
theorem balance_decreaseBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) {j : Nat} {balance : Gwei}
    (found : state.balances.data[j]? = some balance) :
    ∃ lowered, after.balances.data[j]? = some lowered ∧
      lowered.toNat = if index.toNat = j then balance.toNat - delta.toNat else balance.toNat := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
  by_cases same : index.toNat = j
  · subst same
    rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
    subst found
    exact ⟨saturatingSub state.balances.data[index.toNat] delta, by simp [BeaconState.putBalance],
      by simp [toNat_saturatingSub]⟩
  · exact ⟨balance, by simp [BeaconState.putBalance, same, found], by simp [same]⟩

/-- Starting an exit changes no slashed flag. -/
theorem slashedFlag_initiateValidatorExit {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) (other : ValidatorIndex) :
    slashedFlag after other = slashedFlag state other := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · rfl
  have same := getValidator_of_validators_eq (exitQueue_validators queue).1
  by_cases equal : other = index
  · subst equal
    have foundQueued : getValidator queued other = .ok validator := (same other).trans found
    simp [slashedFlag, getValidator_setValidator_self set, found, Except.map]
  · simp [slashedFlag, getValidator_setValidator_of_ne set equal, same]

/-- Slashing a validator sets its slashed flag, and changes no other flag. -/
theorem slashValidator_slashedFlag {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    slashedFlag after slashedIndex = .ok true ∧
      ∀ other, other ≠ slashedIndex → slashedFlag after other = slashedFlag state other := by
  obtain ⟨exited, validator, withdrawable, slashedState, _, _, _, _, _, _, _, last, exitedOk, -, -,
    markedOk, -, -, -, lowered, -, -, raised, final, done⟩ := slashValidator_ok computed
  -- The balance steps keep the registry in which the validator is marked slashed.
  let marked : Validator :=
    { validator with
      slashed := true, withdrawableEpoch := max validator.withdrawableEpoch withdrawable }
  have same := (slashValidator_last (last := last) (after := after) (index := slashedIndex)
    (by subst done; rfl)).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  replace same : after.validators = slashedState.validators := same
  refine ⟨?_, fun other distinct => ?_⟩
  · simp [slashedFlag, getValidator_of_validators_eq same,
      getValidator_setValidator_self markedOk, Except.map]
  · rw [slashedFlag, getValidator_of_validators_eq same,
      getValidator_setValidator_of_ne markedOk distinct]
    exact slashedFlag_initiateValidatorExit exitedOk other

/-! ## The builder payments of a slashing -/

/-- Raising a balance leaves the builder payments. -/
theorem increaseBalance_payments {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    after.builderPendingPayments = state.builderPendingPayments := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- Lowering a balance leaves the builder payments. -/
theorem decreaseBalance_payments {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    after.builderPendingPayments = state.builderPendingPayments := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- The exit queue leaves the builder payments. -/
theorem exitQueue_payments {config : Config} {state after : BeaconState preset fork}
    {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    after.builderPendingPayments = state.builderPendingPayments := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
      Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    rfl

/-- Starting an exit leaves the builder payments. -/
theorem initiateValidatorExit_payments {config : Config} {state after : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config state index = .ok after) :
    after.builderPendingPayments = state.builderPendingPayments := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  · have kept := exitQueue_payments queue
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact kept

/-- From Gloas, a slashing cancels exactly the pending builder payments of the slashed proposer.

Each payment whose proposer is the slashed validator becomes the payment of no bid.

Every other payment stays. -/
theorem slashValidator_payments {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (gloas : .glamsterdam ≤ fork)
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    after.builderPendingPayments gloas =
      .ofVector ((state.builderPendingPayments gloas).elements.map fun payment =>
        if payment.proposerIndex = slashedIndex then .empty else payment) := by
  obtain ⟨exited, _, _, _, _, _, _, _, _, _, _, _, exitedOk, -, -, markedOk, -, -, -, lowered, -, -,
    raised, final, done⟩ := slashValidator_ok computed
  simp only [gloas, ↓reduceDIte] at done
  subst done
  simp only [cancelProposerPayments]
  rw [increaseBalance_payments final, increaseBalance_payments raised,
    decreaseBalance_payments lowered]
  have kept := initiateValidatorExit_payments exitedOk
  obtain ⟨inside, rfl⟩ := setValidator_ok markedOk
  show RootedVector.ofVector ((exited.builderPendingPayments gloas).elements.map _) = _
  rw [kept]

/-- A read of a replaced balance returns the new balance. -/
theorem getBalance_setBalance_self {state after : BeaconState preset fork}
    {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) :
    getBalance after index = .ok balance := by
  obtain ⟨inside, rfl⟩ := setBalance_ok set
  simp [getBalance, BeaconState.putBalance, inside]

/-- An append within the limit adds the element at the end. -/
theorem appendWithinLimit_data {switch : Base.Fork} {α : Type} {limit : Nat}
    {list after : ForkList switch fork α limit} {item : α}
    (computed : appendWithinLimit list item = .ok after) : after.data = list.data.push item := by
  unfold appendWithinLimit at computed
  split at computed
  · cases computed
    rfl
  · cases computed

/-- A pending deposit added to the queue changes no other field of the state. -/
theorem addPendingDeposit_eq {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {deposit : PendingDeposit} (computed : addPendingDeposit state electra deposit = .ok after) :
    ∃ pending, after = { state with pendingDeposits := fun _ => pending } := by
  simp only [addPendingDeposit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨pending, _, rfl⟩ := computed
  exact ⟨pending, rfl⟩

/-- The balance above the activation balance moves to the end of the pending deposits.

The balance keeps at most the activation balance.

The new balance and the amounts added to the queue add up to the old balance. -/
theorem queueExcessActiveBalance_balance {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} {balance : Gwei}
    (found : getBalance state index = .ok balance)
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    getBalance after index = .ok (min balance preset.MIN_ACTIVATION_BALANCE) ∧
      ∃ added : List PendingDeposit,
        (after.pendingDeposits electra).data.toList =
          (state.pendingDeposits electra).data.toList ++ added ∧
        (added.map (·.amount.toNat)).sum + (min balance preset.MIN_ACTIVATION_BALANCE).toNat =
          balance.toNat := by
  simp only [queueExcessActiveBalance, bind_ok_iff, found, Except.ok.injEq,
    exists_eq_left'] at computed
  split at computed
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validator, _, pending, appended, mid, setOk, rfl⟩ := computed
    have minimum : min balance preset.MIN_ACTIVATION_BALANCE = preset.MIN_ACTIVATION_BALANCE := by
      rw [UInt64.min_def, ite_eq_right_iff.mpr (fun le => absurd above (UInt64.not_lt.mpr le))]
    rw [minimum]
    have read := getBalance_setBalance_self setOk
    refine ⟨read, [⟨validator.pubkey,
      validator.withdrawalCredentials, balance - preset.MIN_ACTIVATION_BALANCE,
      Cryptography.Bls.Signatures.infinitySignature, GENESIS_SLOT⟩], ?_, ?_⟩
    · show pending.data.toList = _
      rw [appendWithinLimit_data appended, Array.toList_push]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have := UInt64.lt_iff_toNat_lt.mp above
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)]
      omega
  · rename_i notAbove
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    have minimum : min balance preset.MIN_ACTIVATION_BALANCE = balance := by
      rw [UInt64.min_def, ite_eq_left_iff.mpr (fun no => absurd (UInt64.not_lt.mp notAbove) no)]
    rw [minimum]
    exact ⟨found, [], by simp, by simp⟩

/-- Moving the balance above the activation balance to the queue keeps the sizes. -/
theorem sameSizes_queueExcessActiveBalance {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    SameSizes state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, setOk, rfl⟩ := computed
    exact (sameSizes_setBalance setOk).trans ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact SameSizes.refl _

/-- A validator that switches to compounding credentials has compounding credentials.

The sizes stay the same. -/
theorem switchToCompoundingValidator_compounding {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    SameSizes state after ∧ ∃ validator, getValidator after index = .ok validator ∧
      hasCompoundingWithdrawalCredential validator = true := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, switched, set, queued⟩ := computed
  refine ⟨(sameSizes_setValidator set).trans (sameSizes_queueExcessActiveBalance queued),
    { validator with withdrawalCredentials :=
      validator.withdrawalCredentials.set 0 COMPOUNDING_WITHDRAWAL_PREFIX[0] }, ?_, ?_⟩
  · -- Moving the balance leaves the registry.
    have same : after.validators = switched.validators := by
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, setOk, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok setOk
        rfl
      · simp only [pure, Except.pure, Except.ok.injEq] at queued
        rw [queued]
    rw [getValidator_of_validators_eq same]
    exact getValidator_setValidator_self set
  · simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential]

end EthLib.Consensus
