module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Mutators
public import EthLib.Consensus.Proofs.Churn
public import EthLib.Consensus.Credentials

/-!
# Proofs: state mutators

Every mutator keeps the number of validators and the number of balances.

So a state whose registry and balances have one length keeps that property.

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

theorem sameSizes_setBalance (state : BeaconState preset fork) (index : Nat) (balance : Gwei) :
    SameSizes state (state.setBalance index balance) := by
  simp [SameSizes, BeaconState.setBalance]

theorem sameSizes_setValidator (state : BeaconState preset fork) (index : Nat)
    (validator : Validator) : SameSizes state (state.setValidator index validator) := by
  simp [SameSizes, BeaconState.setValidator]

/-- Raising a balance keeps the sizes. -/
theorem sameSizes_increaseBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : increaseBalance state index delta = .ok after) :
    SameSizes state after := by
  simp only [increaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  exact sameSizes_setBalance _ _ _

/-- Lowering a balance keeps the sizes. -/
theorem sameSizes_decreaseBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : decreaseBalance state index delta = .ok after) :
    SameSizes state after := by
  simp only [decreaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  exact sameSizes_setBalance _ _ _

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
          after =
            queued.setValidator index.toNat { validator with exitEpoch, withdrawableEpoch })) := by
  simp only [initiateValidatorExit, bind_ok_iff] at computed
  obtain ⟨validator, found, rest⟩ := computed
  refine ⟨validator, found, ?_⟩
  split at rest
  · rename_i started
    simp only [pure, Except.pure, Except.ok.injEq] at rest
    exact .inl ⟨by simpa using started, rest.symm⟩
  · rename_i notStarted
    simp only [bind_ok_iff, liftArith, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at rest
    obtain ⟨⟨queued, exitEpoch⟩, queue, withdrawableEpoch, summed, final⟩ := rest
    exact .inr ⟨by simpa using notStarted, queued, exitEpoch, withdrawableEpoch, queue, summed,
      final.symm⟩

/-- Starting an exit keeps the sizes. -/
theorem sameSizes_initiateValidatorExit {config : Config} {state after : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config state index = .ok after) :
    SameSizes state after := by
  obtain ⟨validator, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, rfl⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact SameSizes.refl _
  · obtain ⟨validators, balances⟩ := exitQueue_validators queue
    refine (?_ : SameSizes state queued).trans (sameSizes_setValidator _ _ _)
    exact ⟨by rw [validators], by rw [balances]⟩

/-- The last step of a slashing keeps the registry and the balances. -/
theorem slashValidator_last {last after : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    after.validators = last.validators ∧ after.balances = last.balances := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split <;> exact ⟨rfl, rfl⟩

/-- Slashing a validator keeps the sizes. -/
theorem sameSizes_slashValidator {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    SameSizes state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, _, _, _, _, _, _, _, _, _, lowered, _, _, _, _, _, raised, _, final,
    done⟩ := computed
  have cancelled := slashValidator_last done
  refine (sameSizes_initiateValidatorExit exitedOk).trans (SameSizes.trans ?_
    ((sameSizes_decreaseBalance lowered).trans ((sameSizes_increaseBalance raised).trans
      ((sameSizes_increaseBalance final).trans ⟨by rw [cancelled.1], by rw [cancelled.2]⟩))))
  simp [SameSizes, BeaconState.setValidator]

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

/-- The slashed flag of a validator, or the error of an index outside the registry. -/
def slashedFlag (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Bool :=
  (getValidator state index).map (·.slashed)

/-- A replaced validator is read back at its index. -/
theorem getValidator_setValidator_self {state : BeaconState preset fork}
    {index : ValidatorIndex} {old : Validator} (found : getValidator state index = .ok old)
    (validator : Validator) :
    getValidator (state.setValidator index.toNat validator) index = .ok validator := by
  unfold getValidator at found ⊢
  split at found
  · rename_i read
    have inRange := (Array.getElem?_eq_some_iff.mp read).1
    simp [BeaconState.setValidator, inRange]
  · cases found

/-- Replacing a validator leaves the validators at other indices. -/
theorem getValidator_setValidator_of_ne {state : BeaconState preset fork}
    {index other : ValidatorIndex} (distinct : other ≠ index) (validator : Validator) :
    getValidator (state.setValidator index.toNat validator) other = getValidator state other := by
  have : index.toNat ≠ other.toNat := fun same => distinct (UInt64.toNat_inj.mp same).symm
  simp [getValidator, BeaconState.setValidator, this]

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
    rfl⟩⟩ := initiateValidatorExit_ok computed
  · rw [found] at readOk
    cases readOk
    exact absurd notExiting started
  · rw [found] at readOk
    cases readOk
    have sum := (addChecked_ok_iff.mp summed).2
    refine ⟨{ validator with exitEpoch, withdrawableEpoch }, ?_, sum⟩
    rw [← getValidator_of_validators_eq (exitQueue_validators queue).1] at found
    exact getValidator_setValidator_self found _

/-- Raising a balance leaves the registry. -/
theorem increaseBalance_validators {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    after.validators = state.validators := by
  simp only [increaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  rfl

/-- Lowering a balance leaves the registry. -/
theorem decreaseBalance_validators {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    after.validators = state.validators := by
  simp only [decreaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  rfl

/-- Starting an exit changes no slashed flag. -/
theorem slashedFlag_initiateValidatorExit {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) (other : ValidatorIndex) :
    slashedFlag after other = slashedFlag state other := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, rfl⟩⟩ :=
    initiateValidatorExit_ok computed
  · rfl
  have same := getValidator_of_validators_eq (exitQueue_validators queue).1
  by_cases equal : other = index
  · subst equal
    have foundQueued : getValidator queued other = .ok validator := (same other).trans found
    simp [slashedFlag, getValidator_setValidator_self foundQueued, found, Except.map]
  · simp [slashedFlag, getValidator_setValidator_of_ne equal, same]

/-- Slashing a validator sets its slashed flag, and changes no other flag. -/
theorem slashValidator_slashedFlag {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    slashedFlag after slashedIndex = .ok true ∧
      ∀ other, other ≠ slashedIndex → slashedFlag after other = slashedFlag state other := by
  unfold slashValidator at computed
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, withdrawable, _, _, _, _, _, _, lowered, _, _, _, _,
    _, raised, _, final, done⟩ := computed
  -- The balance steps keep the registry in which the validator is marked slashed.
  let marked : Validator :=
    { validator with
      slashed := true, withdrawableEpoch := max validator.withdrawableEpoch withdrawable }
  have same := (slashValidator_last done).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  replace same : after.validators = (exited.setValidator slashedIndex.toNat marked).validators :=
    same
  refine ⟨?_, fun other distinct => ?_⟩
  · simp [slashedFlag, getValidator_of_validators_eq same, getValidator_setValidator_self found,
      Except.map, marked]
  · rw [slashedFlag, getValidator_of_validators_eq same, getValidator_setValidator_of_ne distinct]
    exact slashedFlag_initiateValidatorExit exitedOk other

/-! ## The builder payments of a slashing -/

/-- Raising a balance leaves the builder payments. -/
theorem increaseBalance_payments {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    after.builderPendingPayments = state.builderPendingPayments := by
  simp only [increaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  rfl

/-- Lowering a balance leaves the builder payments. -/
theorem decreaseBalance_payments {state after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    after.builderPendingPayments = state.builderPendingPayments := by
  simp only [decreaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
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
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, rfl⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  · have kept := exitQueue_payments queue
    exact kept

/-- From Gloas, a slashing cancels exactly the pending builder payments of the slashed proposer.

Each payment whose proposer is the slashed validator becomes the payment of no bid.

Every other payment stays. -/
theorem slashValidator_payments {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (gloas : .glamsterdam ≤ fork)
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    after.builderPendingPayments gloas = (state.builderPendingPayments gloas).map fun payment =>
      if payment.proposerIndex = slashedIndex then .empty else payment := by
  unfold slashValidator at computed
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, _, _, _, _, _, _, _, _, _, lowered, _, _, _, _, _, raised, _, final,
    done⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq, gloas, ↓reduceDIte] at done
  subst done
  simp only [cancelProposerPayments]
  rw [increaseBalance_payments final, increaseBalance_payments raised,
    decreaseBalance_payments lowered]
  have kept := initiateValidatorExit_payments exitedOk
  show (exited.builderPendingPayments gloas).map _ = _
  rw [kept]

/-- A read of a replaced balance returns the new balance. -/
theorem getBalance_setBalance_self {state : BeaconState preset fork} {index : ValidatorIndex}
    {old : Gwei} (found : getBalance state index = .ok old) (balance : Gwei) :
    getBalance (state.setBalance index.toNat balance) index = .ok balance := by
  unfold getBalance at found ⊢
  split at found
  · rename_i read
    have inRange := (Array.getElem?_eq_some_iff.mp read).1
    simp [BeaconState.setBalance, inRange]
  · cases found

/-- An append within the limit adds the element at the end. -/
theorem appendWithinLimit_data {switch : Base.Fork} {α : Type} {limit : Nat}
    {list after : ForkList switch fork α limit} {item : α}
    (computed : appendWithinLimit list item = .ok after) : after.data = list.data.push item := by
  unfold appendWithinLimit at computed
  split at computed
  · cases computed
    rfl
  · cases computed

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
    obtain ⟨validator, _, pending, appended, rfl⟩ := computed
    have minimum : min balance preset.MIN_ACTIVATION_BALANCE = preset.MIN_ACTIVATION_BALANCE := by
      rw [UInt64.min_def, ite_eq_right_iff.mpr (fun le => absurd above (UInt64.not_lt.mpr le))]
    rw [minimum]
    refine ⟨getBalance_setBalance_self found _, [⟨validator.pubkey,
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
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact sameSizes_setBalance state index.toNat preset.MIN_ACTIVATION_BALANCE
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
  obtain ⟨validator, found, queued⟩ := computed
  refine ⟨(sameSizes_setValidator _ _ _).trans (sameSizes_queueExcessActiveBalance queued),
    { validator with withdrawalCredentials :=
      validator.withdrawalCredentials.set 0 COMPOUNDING_WITHDRAWAL_PREFIX[0] }, ?_, ?_⟩
  · -- Moving the balance leaves the registry.
    have same : after.validators = (state.setValidator index.toNat { validator with
        withdrawalCredentials :=
          validator.withdrawalCredentials.set 0 COMPOUNDING_WITHDRAWAL_PREFIX[0] }).validators := by
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, rfl⟩ := queued
        rfl
      · simp only [pure, Except.pure, Except.ok.injEq] at queued
        rw [queued]
    rw [getValidator_of_validators_eq same]
    exact getValidator_setValidator_self found _
  · simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential]

end EthLib.Consensus
