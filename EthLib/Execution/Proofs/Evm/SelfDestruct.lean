module

public import EthLib.Execution.Evm.SelfDestruct

/-!
# Proofs: `Evm.SelfDestruct`

From Cancun, SELFDESTRUCT deletes no account that the transaction did not create.

Before Cancun, it always records the current account for deletion.

From London, it gives no refund.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- From Cancun, an account that the transaction did not create is not recorded for deletion. -/
theorem finishSelfdestruct_keeps_account {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (cancun : fork ≥ .dencun)
    (h : finishSelfdestruct fork beneficiary refund evm = .ok after)
    (old : evm.message.currentTarget ∉ after.state.createdAccounts) :
    after.substate.accountsToDelete = evm.substate.accountsToDelete := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have : ¬ (fork < .dencun) := Nat.not_lt.mpr cancun
    simp_all

omit [GasMeter Meter] in
/-- Before Cancun, the current account is recorded for deletion. -/
theorem finishSelfdestruct_deletes {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (early : fork < .dencun)
    (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    evm.message.currentTarget ∈ after.substate.accountsToDelete := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp [early]

/-- From London, SELFDESTRUCT gives no refund. -/
theorem refund_selfdestruct_of_london (london : fork ≥ .london) :
    (gasSchedule fork).REFUND_SELF_DESTRUCT = 0 := by
  simp [gasSchedule, london]

end EthLib.Execution.Evm
