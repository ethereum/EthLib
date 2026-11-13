module

public import EthLib.Consensus.BeaconApi.Validators

/-!
# Proofs: the statuses of validators and builders in the Beacon API

The status that EthLib gives a validator always meets the condition of the source.

When its activation, exit and withdrawable epochs do not decrease, it is the only status that does.

Without that order two conditions can hold at once, so the order is needed.

The group of the status is active exactly when the validator is active.

The status of a builder is the only one whose condition holds.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork}

private theorem far_toNat : FAR_FUTURE_EPOCH.toNat = 18446744073709551615 := by
  simp [FAR_FUTURE_EPOCH]

private theorem toNat_le (x : UInt64) : x.toNat ≤ 18446744073709551615 := by
  have := x.toNat_lt
  omega

set_option hygiene false in
/-- Decide the six conditions of the status, then close the goal on the natural numbers. -/
local macro "status_cases" : tactic => `(tactic|
  (have := toNat_le validator.exitEpoch
   have := toNat_le validator.activationEligibilityEpoch
   unfold validatorStatus
   simp only [← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, far_toNat, UInt64.toNat_zero]
   by_cases a : epoch.toNat < validator.activationEpoch.toNat <;>
     by_cases b : epoch.toNat < validator.exitEpoch.toNat <;>
     by_cases c : epoch.toNat < validator.withdrawableEpoch.toNat <;>
     by_cases d : validator.exitEpoch.toNat = 18446744073709551615 <;>
     by_cases e : validator.activationEligibilityEpoch.toNat = 18446744073709551615 <;>
     by_cases f : balance.toNat = 0 <;>
     cases hs : validator.slashed <;>
     (try simp only [eq_true a]) <;> (try simp only [eq_false a]) <;>
     (try simp only [eq_true b]) <;> (try simp only [eq_false b]) <;>
     (try simp only [eq_true c]) <;> (try simp only [eq_false c]) <;>
     (try simp only [eq_true d]) <;> (try simp only [eq_false d]) <;>
     (try simp only [eq_true e]) <;> (try simp only [eq_false e]) <;>
     (try simp only [eq_true f]) <;> (try simp only [eq_false f]) <;>
     simp only [hs, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte,
       ValidatorStatus.Holds, ValidatorStatus.coarse, isActiveValidator, Bool.and_eq_true,
       decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
       far_toNat, UInt64.toNat_zero, reduceCtorEq, Bool.true_eq_false, ne_eq, eq_self, iff_true,
       iff_false, true_iff, false_iff, true_and, and_true] <;>
     omega))

/-- The status of a validator meets the condition of the source for that status. -/
theorem validatorStatus_holds (validator : Validator) (balance : Gwei) (epoch : Epoch) :
    (validatorStatus validator balance epoch).Holds validator balance epoch := by
  status_cases

/-- Two statuses that meet their conditions are equal, for epochs that do not decrease. -/
private theorem holds_unique {validator : Validator} {balance : Gwei} {epoch : Epoch}
    (activated : validator.activationEpoch ≤ validator.exitEpoch)
    (exited : validator.exitEpoch ≤ validator.withdrawableEpoch) {s t : ValidatorStatus}
    (hs : s.Holds validator balance epoch) (ht : t.Holds validator balance epoch) : s = t := by
  have := toNat_le validator.exitEpoch
  have := toNat_le validator.activationEligibilityEpoch
  rw [UInt64.le_iff_toNat_le] at activated exited
  cases hsl : validator.slashed <;> cases s <;> cases t <;> try rfl
  all_goals
    exfalso
    simp only [ValidatorStatus.Holds, hsl, Bool.false_eq_true, Bool.true_eq_false, eq_self,
      and_true, and_false, ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      far_toNat, UInt64.toNat_zero, ne_eq] at hs ht <;> omega

/-- With epochs that do not decrease, a status meets its condition exactly when EthLib gives it. -/
theorem validatorStatus_unique {validator : Validator} {balance : Gwei} {epoch : Epoch}
    (activated : validator.activationEpoch ≤ validator.exitEpoch)
    (exited : validator.exitEpoch ≤ validator.withdrawableEpoch) (status : ValidatorStatus) :
    status.Holds validator balance epoch ↔ validatorStatus validator balance epoch = status := by
  refine ⟨fun h => (holds_unique activated exited h (validatorStatus_holds ..)).symm, ?_⟩
  rintro rfl
  exact validatorStatus_holds ..

/-- Without the order of the activation and exit epochs, two statuses can both hold. -/
theorem validatorStatus_order_needed :
    ∃ (validator : Validator) (epoch : Epoch),
      ValidatorStatus.pendingQueued.Holds validator 32 epoch ∧
        ValidatorStatus.exitedUnslashed.Holds validator 32 epoch := by
  refine ⟨Validator.mk default default 0 false 9 10 5 300, 7, ?_, ?_⟩
  · simp only [ValidatorStatus.Holds, FAR_FUTURE_EPOCH]
    decide
  · simp only [ValidatorStatus.Holds]
    decide

/-- Without the order of the exit and withdrawable epochs, two statuses can both hold. -/
theorem validatorStatus_exit_order_needed :
    ∃ (validator : Validator) (epoch : Epoch),
      ValidatorStatus.activeExiting.Holds validator 32 epoch ∧
        ValidatorStatus.withdrawalPossible.Holds validator 32 epoch := by
  refine ⟨Validator.mk default default 0 false 1 1 5 3, 4, ?_, ?_⟩
  · simp only [ValidatorStatus.Holds, FAR_FUTURE_EPOCH]
    decide
  · simp only [ValidatorStatus.Holds]
    decide

/-- The group of the status of a validator is active exactly when the validator is active. -/
theorem validatorStatus_active_iff (validator : Validator) (balance : Gwei) (epoch : Epoch) :
    (validatorStatus validator balance epoch).coarse = .active ↔
      isActiveValidator validator epoch = true := by
  status_cases

/-- For a builder of the state, a status meets its condition exactly when EthLib gives it. -/
theorem builderStatus_unique {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {index : BuilderIndex} {builder : Builder} (found : getBuilder state gloas index = .ok builder)
    (status : BuilderStatus) :
    status.Holds builder state.finalizedCheckpoint.epoch ↔
      builderStatus state gloas index = .ok status := by
  unfold builderStatus isActiveBuilder
  rw [found]
  by_cases w : builder.withdrawableEpoch = FAR_FUTURE_EPOCH <;>
    by_cases dep : builder.depositEpoch < state.finalizedCheckpoint.epoch <;> cases status <;>
    simp [BuilderStatus.Holds, w, dep, bind, Except.bind, pure, Except.pure]

end EthLib.Consensus.BeaconApi
