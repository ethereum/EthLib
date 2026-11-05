module

public import EthLib.Execution.Evm.StateGas

/-!
# Proofs: `Evm.StateGas`

A charge of state gas fails exactly when the reservoir and the execution gas do not cover it.

A charge raises the net state gas by its amount, and a refill lowers it by its amount.

So execution gas, plus the reservoir, plus the net state gas, stays the same.

Charges, refills, rollbacks and repayments keep execution gas plus the spill.

A commit lowers that sum.

When the reservoir or the spill is empty, a refill undoes the charge of the same amount.

A repayment leaves the reservoir or the spill empty.

A rollback credits the spill back, and lowers the net state gas as EIP-8037 writes it.

A rollback to the start leaves no net state gas.

The net state gas of a merge is that of the caller plus that of the child.
-/

@[expose] public section

namespace EthLib.Execution.Evm.StateGasMeter

/-- The reservoir or the spill is empty: no gas has drifted between the two pools. -/
def Repaid (meter : StateGasMeter) : Prop :=
  meter.reservoir = 0 ∨ meter.spill = 0

/-! ## Execution gas -/

/-- A charge of execution gas fails exactly when it is above the execution gas left. -/
theorem charge_eq_error_iff {meter : StateGasMeter} {amount : Nat} {e : EvmError} :
    meter.charge amount = .error e ↔ meter.gasLeft < amount ∧ e = .outOfGas := by
  unfold charge
  split
  · simp only [Except.error.injEq]
    constructor
    · rintro rfl
      exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl
  · simp only [reduceCtorEq, false_iff, not_and]
    omega

/-- A charge of execution gas takes it from the execution gas left, and changes nothing else. -/
theorem charge_eq_ok_iff {meter after : StateGasMeter} {amount : Nat} :
    meter.charge amount = .ok after ↔
      amount ≤ meter.gasLeft ∧ after = { meter with gasLeft := meter.gasLeft - amount } := by
  unfold charge
  split
  · simp only [reduceCtorEq, false_iff, not_and]
    omega
  · simp only [Except.ok.injEq]
    constructor
    · rintro rfl
      exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

/-- An exceptional halt leaves no execution gas, and the reservoir of the baseline. -/
theorem halt_eq (meter : StateGasMeter) :
    meter.halt = { meter with gasLeft := 0, spill := 0, reservoir := meter.baseline } :=
  rfl

/-! ## Charges and refills of state gas -/

/-- A charge of state gas fails exactly when the reservoir and the execution gas are below it. -/
theorem chargeState_eq_error_iff {meter : StateGasMeter} {amount : Nat} {e : EvmError} :
    meter.chargeState amount = .error e ↔
      meter.reservoir + meter.gasLeft < amount ∧ e = .outOfGas := by
  unfold chargeState
  split
  · simp only [reduceCtorEq, false_iff, not_and]
    omega
  · split
    · simp only [reduceCtorEq, false_iff, not_and]
      omega
    · simp only [Except.error.injEq]
      constructor
      · rintro rfl
        exact ⟨by omega, rfl⟩
      · rintro ⟨-, rfl⟩
        rfl

/-- A charge of state gas raises the net state gas by its amount. -/
theorem stateGasUsed_chargeState {meter after : StateGasMeter} {amount : Nat}
    (h : meter.chargeState amount = .ok after) :
    after.stateGasUsed = meter.stateGasUsed + amount := by
  unfold chargeState at h
  split at h
  · cases h
    simp only [stateGasUsed]
    omega
  · split at h
    · cases h
      simp only [stateGasUsed]
      omega
    · cases h

/-- A charge of state gas keeps execution gas plus the reservoir plus the net state gas. -/
theorem total_chargeState {meter after : StateGasMeter} {amount : Nat}
    (h : meter.chargeState amount = .ok after) :
    (after.gasLeft : Int) + after.reservoir + after.stateGasUsed =
      meter.gasLeft + meter.reservoir + meter.stateGasUsed := by
  have used := stateGasUsed_chargeState h
  unfold chargeState at h
  split at h
  · cases h
    simp only at used ⊢
    omega
  · split at h
    · cases h
      simp only at used ⊢
      omega
    · cases h

/-- A charge of state gas keeps execution gas plus the spill. -/
theorem budget_chargeState {meter after : StateGasMeter} {amount : Nat}
    (h : meter.chargeState amount = .ok after) :
    after.gasLeft + after.spill = meter.gasLeft + meter.spill := by
  unfold chargeState at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      simp only
      omega
    · cases h

/-- A charge of state gas keeps the reservoir or the spill empty. -/
theorem repaid_chargeState {meter after : StateGasMeter} {amount : Nat}
    (repaid : meter.Repaid) (h : meter.chargeState amount = .ok after) : after.Repaid := by
  unfold chargeState at h
  unfold Repaid at repaid
  split at h
  · cases h
    unfold Repaid
    simp only
    omega
  · split at h
    · cases h
      exact Or.inl rfl
    · cases h

/-- A refill of state gas lowers the net state gas by its amount. -/
theorem stateGasUsed_refill (meter : StateGasMeter) (amount : Nat) :
    (meter.refill amount).stateGasUsed = meter.stateGasUsed - amount := by
  simp only [refill, stateGasUsed]
  omega

/-- A refill of state gas keeps execution gas plus the reservoir plus the net state gas. -/
theorem total_refill (meter : StateGasMeter) (amount : Nat) :
    ((meter.refill amount).gasLeft : Int) + (meter.refill amount).reservoir +
        (meter.refill amount).stateGasUsed =
      meter.gasLeft + meter.reservoir + meter.stateGasUsed := by
  simp only [refill, stateGasUsed]
  omega

/-- A refill of state gas keeps execution gas plus the spill. -/
theorem budget_refill (meter : StateGasMeter) (amount : Nat) :
    (meter.refill amount).gasLeft + (meter.refill amount).spill = meter.gasLeft + meter.spill := by
  simp only [refill]
  omega

/-- A refill of state gas keeps the reservoir or the spill empty. -/
theorem repaid_refill {meter : StateGasMeter} (repaid : meter.Repaid) (amount : Nat) :
    (meter.refill amount).Repaid := by
  unfold Repaid at repaid ⊢
  simp only [refill]
  omega

/-- When the reservoir or the spill is empty, a refill undoes the charge of the same amount. -/
theorem refill_chargeState {meter after : StateGasMeter} {amount : Nat}
    (repaid : meter.Repaid) (h : meter.chargeState amount = .ok after) :
    after.refill amount = meter := by
  obtain ⟨gas, reservoir, baseline, spill, committed, grant⟩ := meter
  unfold Repaid at repaid
  unfold chargeState at h
  simp only at repaid h
  by_cases low : amount ≤ reservoir
  · simp only [low, ↓reduceIte, Except.ok.injEq] at h
    subst h
    simp only [refill, StateGasMeter.mk.injEq, and_true, true_and]
    rcases repaid with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> omega
  · by_cases covered : amount ≤ reservoir + gas
    · simp only [low, covered, ↓reduceIte, Except.ok.injEq] at h
      subst h
      simp only [refill, StateGasMeter.mk.injEq, and_true, true_and]
      rcases repaid with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> omega
    · simp only [low, covered, ↓reduceIte, reduceCtorEq] at h

/-! ## Commits, rollbacks and repayments -/

/-- A commit keeps the net state gas, the execution gas and the reservoir. -/
theorem commit_keeps (meter : StateGasMeter) :
    meter.commit.stateGasUsed = meter.stateGasUsed ∧ meter.commit.gasLeft = meter.gasLeft ∧
      meter.commit.reservoir = meter.reservoir := by
  simp only [commit, stateGasUsed]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | omega

/-- A commit lowers execution gas plus the spill by the spill. -/
theorem budget_commit (meter : StateGasMeter) :
    meter.commit.gasLeft + meter.commit.spill = meter.gasLeft := by
  simp only [commit]
  omega

/-- A rollback credits the spill back to execution gas. -/
theorem gasLeft_restore (meter : StateGasMeter) :
    meter.restore.gasLeft = meter.gasLeft + meter.spill :=
  rfl

/-- A rollback keeps execution gas plus the spill. -/
theorem budget_restore (meter : StateGasMeter) :
    meter.restore.gasLeft + meter.restore.spill = meter.gasLeft + meter.spill := by
  simp only [restore]
  omega

/-- A rollback lowers the net state gas by the baseline minus the reservoir plus the spill. -/
theorem stateGasUsed_restore (meter : StateGasMeter) :
    meter.restore.stateGasUsed =
      meter.stateGasUsed - ((meter.baseline : Int) - meter.reservoir + meter.spill) := by
  simp only [restore, stateGasUsed]
  omega

/-- A rollback after a commit keeps the execution gas and the reservoir at the commit. -/
theorem restore_commit (meter : StateGasMeter) :
    meter.commit.restore.gasLeft = meter.gasLeft ∧
      meter.commit.restore.reservoir = meter.reservoir := by
  simp only [commit, restore]
  refine ⟨?_, ?_⟩ <;> first | trivial | omega

/-- A rollback to the start credits back every spill and leaves no net state gas. -/
theorem restoreToEntry_spec (meter : StateGasMeter) :
    meter.restoreToEntry.gasLeft = meter.gasLeft + meter.spill + meter.committed ∧
      meter.restoreToEntry.stateGasUsed = 0 := by
  simp only [restoreToEntry, stateGasUsed]
  refine ⟨?_, ?_⟩ <;> first | trivial | omega

/-- A repayment keeps the net state gas. -/
theorem stateGasUsed_repay (meter : StateGasMeter) :
    meter.repay.stateGasUsed = meter.stateGasUsed := by
  simp only [repay, stateGasUsed]
  omega

/-- A repayment keeps execution gas plus the reservoir. -/
theorem gasLeft_add_reservoir_repay (meter : StateGasMeter) :
    meter.repay.gasLeft + meter.repay.reservoir = meter.gasLeft + meter.reservoir := by
  simp only [repay]
  omega

/-- A repayment keeps execution gas plus the spill. -/
theorem budget_repay (meter : StateGasMeter) :
    meter.repay.gasLeft + meter.repay.spill = meter.gasLeft + meter.spill := by
  simp only [repay]
  omega

/-- A repayment leaves the reservoir or the spill empty. -/
theorem repaid_repay (meter : StateGasMeter) : meter.repay.Repaid := by
  unfold Repaid
  simp only [repay]
  omega

/-! ## Calls -/

/-- A child that never ran gives the caller back its meter, with the gas the call passed on. -/
theorem cancel_enter (meter : StateGasMeter) (gas : Nat) :
    cancel (meter.enter gas).1 (meter.enter gas).2 =
      { meter with gasLeft := meter.gasLeft + gas } := by
  simp only [enter, drain, cancel, start, Nat.zero_add]

/-- The net state gas of a merge is that of the caller plus that of the child.

The child got the whole reservoir of the caller, and committed nothing. -/
theorem stateGasUsed_absorb (meter child : StateGasMeter) (gas : Nat) (succeeded : Bool)
    (grant : child.grant = meter.reservoir) (committed : child.committed = 0) :
    (absorb (meter.enter gas).1 child succeeded).stateGasUsed =
      meter.stateGasUsed + child.stateGasUsed := by
  unfold absorb
  split
  · rw [stateGasUsed_repay]
    simp only [enter, drain, stateGasUsed]
    omega
  · simp only [enter, drain, stateGasUsed]
    omega

/-- A merge returns the execution gas and the spill of the child to the caller. -/
theorem budget_absorb (caller child : StateGasMeter) (succeeded : Bool) :
    (absorb caller child succeeded).gasLeft + (absorb caller child succeeded).spill =
      caller.gasLeft + caller.spill + (child.gasLeft + child.spill) := by
  unfold absorb
  split
  · rw [budget_repay]
    simp only
    omega
  · simp only
    omega

/-- The merge of a child that succeeds leaves the reservoir or the spill empty. -/
theorem repaid_absorb (caller child : StateGasMeter) : (absorb caller child true).Repaid :=
  repaid_repay _

end EthLib.Execution.Evm.StateGasMeter
