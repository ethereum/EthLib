module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Mutators

/-!
# Proofs: state mutators

Every mutator keeps the number of validators and the number of balances.

So a state whose registry and balances have one length keeps that property.

A validator that starts to exit may withdraw a fixed delay after its exit epoch, with no overflow.

Before Electra, an exit epoch other than the far future held fewer exits than the churn limit.
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

/-- Starting an exit keeps the sizes. -/
theorem sameSizes_initiateValidatorExit {config : Config} {state after : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config state index = .ok after) :
    SameSizes state after := by
  simp only [initiateValidatorExit, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  split at computed
  · cases computed
    exact SameSizes.refl _
  split at computed
  · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  exact sameSizes_setValidator _ _ _

/-- Slashing a validator keeps the sizes. -/
theorem sameSizes_slashValidator {config : Config} {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    SameSizes state after := by
  simp only [slashValidator, bind, Except.bind] at computed
  split at computed
  · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at computed
  split at computed
  · cases computed
  rename_i exited exitedOk
  have one := sameSizes_initiateValidatorExit exitedOk
  repeat' (split at computed; · cases computed)
  rename_i lowered _ _ _ _ _ _ _ raised raisedOk
  refine one.trans (SameSizes.trans ?_ ((sameSizes_decreaseBalance lowered).trans
    ((sameSizes_increaseBalance raisedOk).trans (sameSizes_increaseBalance computed))))
  simp [SameSizes, BeaconState.setValidator]

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
  have inRange : index.toNat < state.validators.data.size := by
    unfold getValidator at found
    split at found
    · rename_i read
      exact (Array.getElem?_eq_some_iff.mp read).1
    · cases found
  simp only [initiateValidatorExit, found, notExiting, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at computed
  split at computed
  · cases computed
  rename_i exitEpoch _
  split at computed
  · cases computed
  rename_i withdrawableEpoch summed
  cases computed
  have sum := (addChecked_ok_iff.mp (mapError_ok_iff.mp summed)).2
  refine ⟨{ validator with exitEpoch, withdrawableEpoch }, ?_, sum⟩
  simp [getValidator, BeaconState.setValidator, inRange]

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

end EthLib.Consensus
