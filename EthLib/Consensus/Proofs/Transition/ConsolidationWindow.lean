module

public import EthLib.Consensus.Proofs.Transition.Requests

/-!
# Proofs: a consolidation keeps the stake of a slashable source

From Electra, a validator can consolidate its balance into another one.

The epoch step moves the balance only once the source may withdraw in the next epoch.

It skips a slashed source, and stops at the first source that cannot yet withdraw in the next epoch.

So while a slashing in the next epoch can still hit the source, this step has not moved its balance.

This step leaves the stake of the source at the source for a slashing to find.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- A read of a balance returns the balance at its position of the list. -/
private theorem getBalance_eq_ok_iff' {state : BeaconState preset fork} {index : ValidatorIndex}
    {balance : Gwei} :
    getBalance state index = .ok balance ↔ state.balances.data[index.toNat]? = some balance := by
  unfold getBalance
  split <;> simp_all

/-- A pass never lowers the balance of a validator that cannot yet withdraw in its epoch.

So that validator is never a source whose balance moves. -/
private theorem passPendingConsolidations_balance_le {nextEpoch : Epoch}
    {list : List PendingConsolidation} :
    ∀ {state after : BeaconState preset fork} {read : Nat} {index : ValidatorIndex}
      {validator : Validator} {balance : Gwei},
    passPendingConsolidations nextEpoch state list = .ok (after, read) →
    getValidator state index = .ok validator → getBalance state index = .ok balance →
    nextEpoch < validator.withdrawableEpoch →
    ∃ later, getBalance after index = .ok later ∧ balance ≤ later := by
  induction list with
  | nil =>
    intro state after read index validator balance computed _ current _
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨rfl, -⟩ := computed
    exact ⟨balance, current, UInt64.le_refl _⟩
  | cons consolidation rest ih =>
    intro state after read index validator balance computed read' current window
    simp only [passPendingConsolidations, liftAccessor, bind_ok_iff, mapError_ok_iff] at computed
    obtain ⟨source, sourceRead, computed⟩ := computed
    by_cases slashed : source.slashed = true
    · simp only [slashed, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at computed
      obtain ⟨⟨state', read''⟩, passed, rfl, -⟩ := computed
      exact ih passed read' current window
    · replace slashed : source.slashed = false := by simpa using slashed
      by_cases early : nextEpoch < source.withdrawableEpoch
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨rfl, -⟩ := computed
        exact ⟨balance, current, UInt64.le_refl _⟩
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, bind_ok_iff,
          mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨sourceBalance, sourceBalanceOk, lowered, loweredOk, raised, raisedOk,
          ⟨state', read''⟩, passed, rfl, -⟩ := computed
        have different : consolidation.sourceIndex.toNat ≠ index.toNat := by
          intro same
          have atIndex := getValidator_eq_ok_iff.mp read'
          have atSource := getValidator_eq_ok_iff.mp sourceRead
          rw [same, atIndex, Option.some.injEq] at atSource
          subst atSource
          exact early window
        have found := getBalance_eq_ok_iff'.mp current
        obtain ⟨down, downFound, downEq⟩ := balance_decreaseBalance loweredOk found
        obtain ⟨up, upFound, upEq⟩ := balance_increaseBalance raisedOk downFound
        simp only [different, ↓reduceIte] at downEq
        have sameValidators := (increaseBalance_validators raisedOk).trans
          (decreaseBalance_validators loweredOk)
        obtain ⟨later, laterOk, le⟩ := ih passed
          ((getValidator_of_validators_eq sameValidators index).trans read')
          (getBalance_eq_ok_iff'.mpr upFound) window
        refine ⟨later, laterOk, UInt64.le_trans ?_ le⟩
        rw [UInt64.le_iff_toNat_le]
        have : balance.toNat ≤ up.toNat := by
          rw [upEq]
          split <;> omega
        exact this

/-- The pending consolidations of an epoch never lower the balance of some validators.

These are the validators that cannot yet withdraw in the next epoch.

Each one may still be the target of a consolidation, which raises its balance. -/
theorem processPendingConsolidations_balance_le {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) {index : ValidatorIndex}
    {validator : Validator} {balance : Gwei} (read : getValidator state index = .ok validator)
    (current : getBalance state index = .ok balance)
    (window : getCurrentEpoch state + 1 < validator.withdrawableEpoch) :
    ∃ later, getBalance after index = .ok later ∧ balance ≤ later := by
  simp only [processPendingConsolidations, liftAccessor, liftArith, bind_ok_iff, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, summed, ⟨passed, read'⟩, pass, rfl⟩ := computed
  have next : nextEpoch = getCurrentEpoch state + 1 := by
    obtain ⟨fits, value⟩ := addChecked_ok_iff.mp summed
    rw [← UInt64.toNat_inj, value, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  obtain ⟨later, laterOk, le⟩ := passPendingConsolidations_balance_le pass read current
    (next ▸ window)
  exact ⟨later, laterOk, le⟩

/-- The pending consolidations of an epoch never lower the balance of a slashable validator.

The validator must be slashable in the next epoch. -/
theorem processPendingConsolidations_balance_le_of_slashable {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) {index : ValidatorIndex}
    {validator : Validator} {balance : Gwei} (read : getValidator state index = .ok validator)
    (current : getBalance state index = .ok balance)
    (slashable : isSlashableValidator validator (getCurrentEpoch state + 1) = true) :
    ∃ later, getBalance after index = .ok later ∧ balance ≤ later := by
  simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at slashable
  exact processPendingConsolidations_balance_le computed read current slashable.2

end EthLib.Consensus
