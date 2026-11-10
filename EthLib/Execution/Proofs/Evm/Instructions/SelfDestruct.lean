module

public import EthLib.Execution.Evm.Instructions.SelfDestruct
public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: `Evm.Instructions.SelfDestruct`

From Cancun, SELFDESTRUCT deletes no account that the transaction did not create.

Before Cancun, it always records the current account for deletion.

From London, it gives no refund.

From Cancun to BPO5, an account created in the transaction that names itself burns its ether.

From Glamsterdam, SELFDESTRUCT burns no ether, by EIP-8246.

It moves the balance to another beneficiary and keeps the sum of the two balances.

An account that names itself keeps its balance.

From Glamsterdam, a new beneficiary costs 9000 execution gas and 183600 state gas.

No SELFDESTRUCT pays state gas before Glamsterdam.

SELFDESTRUCT keeps memory.

From Glamsterdam, it writes the transfer log of the balance it moves, and none before.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)

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

/-! ## The ether -/

/-- From Glamsterdam, the transfer of SELFDESTRUCT moves the whole balance, and nothing more. -/
theorem selfdestructTransfer_of_glamsterdam (h : fork ≥ .glamsterdam) (state : TransactionState)
    (originator beneficiary : Address) :
    selfdestructTransfer fork state originator beneficiary =
      state.moveEther fork originator beneficiary (state.getAccount originator).balance := by
  have dencun : fork ≥ .dencun := Nat.le_trans (by decide) h
  have : ¬fork < .glamsterdam := Nat.not_lt.mpr h
  simp only [selfdestructTransfer, dencun, this, false_and, ↓reduceIte, bind_pure]

/-- From Glamsterdam, SELFDESTRUCT keeps the sum of the balances of the originator and beneficiary.

When they are one account, its balance is counted once for each name.

Every other balance is unchanged, so no ether is gone. -/
theorem selfdestructTransfer_balance_of_glamsterdam (h : fork ≥ .glamsterdam)
    {state after : TransactionState} {originator beneficiary : Address}
    (ht : selfdestructTransfer fork state originator beneficiary = .ok after) :
    (after.getAccount originator).balance.toNat + (after.getAccount beneficiary).balance.toNat =
        (state.getAccount originator).balance.toNat +
          (state.getAccount beneficiary).balance.toNat ∧
      ∀ other, other ≠ originator → other ≠ beneficiary →
        after.getAccount other = state.getAccount other := by
  rw [selfdestructTransfer_of_glamsterdam h] at ht
  exact TransactionState.moveEther_balance ht

/-- From Glamsterdam, an account that names itself as beneficiary keeps its balance. -/
theorem selfdestructTransfer_self_of_glamsterdam (h : fork ≥ .glamsterdam)
    {state after : TransactionState} {originator : Address}
    (ht : selfdestructTransfer fork state originator originator = .ok after) :
    (after.getAccount originator).balance = (state.getAccount originator).balance := by
  rw [selfdestructTransfer_of_glamsterdam h] at ht
  exact congrArg (·.balance) (TransactionState.moveEther_self ht).1

/-- From Cancun to BPO5, an account created in the transaction that names itself burns its ether.

Its balance drops to 0. -/
theorem selfdestructTransfer_self_burns (h : fork ≥ .dencun) (hlt : fork < .glamsterdam)
    {state after : TransactionState} {originator : Address}
    (created : originator ∈ state.createdAccounts)
    (ht : selfdestructTransfer fork state originator originator = .ok after) :
    (after.getAccount originator).balance = 0 := by
  simp only [selfdestructTransfer, h, ↓reduceIte] at ht
  obtain ⟨moved, hm, ht⟩ := Base.bind_ok_iff.mp ht
  have keeps : moved.createdAccounts = state.createdAccounts :=
    TransactionState.createdAccounts_moveEther hm
  simp only [hlt, keeps, created, and_self, ↓reduceIte] at ht
  obtain ⟨account, hf, hread, -⟩ := TransactionState.modifyState_eq_ok ht
  cases hf
  rw [hread]

/-! ## The price -/

/-- From Glamsterdam, a new beneficiary costs the write of an account, 9000 execution gas. -/
theorem selfdestructNewAccount_of_glamsterdam (h : fork ≥ .glamsterdam) :
    (gasSchedule fork).OPCODE_SELFDESTRUCT_NEW_ACCOUNT = 9000 := by
  simp only [gasSchedule, h, ↓reduceIte]
  rfl

/-- From Glamsterdam, a new beneficiary costs the state gas of a new account. -/
theorem selfdestructStateGas_of_glamsterdam (h : fork ≥ .glamsterdam) :
    selfdestructStateGas fork true = 183600 := by
  simp only [selfdestructStateGas, h, and_self, ↓reduceIte]
  rfl

/-- No SELFDESTRUCT pays state gas before Glamsterdam, nor without a new beneficiary. -/
theorem selfdestructStateGas_eq_zero (h : fork < .glamsterdam ∨ createsAccount = false) :
    selfdestructStateGas fork createsAccount = 0 := by
  unfold selfdestructStateGas
  rcases h with h | h
  · have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
    simp [this]
  · simp [h]

omit [GasMeter Meter] in
/-- The end of SELFDESTRUCT keeps memory. -/
theorem memory_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.memory = evm.memory := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    rfl

omit [GasMeter Meter] in
/-- The end of SELFDESTRUCT keeps the message. -/
theorem message_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.message = evm.message := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    rfl

omit [GasMeter Meter] in
/-- The end of SELFDESTRUCT keeps the code. -/
theorem code_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.code = evm.code := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    rfl

/-- SELFDESTRUCT keeps memory. -/
theorem memory_selfdestructOpStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.memory = evm.memory := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  unfold selfdestructStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hpair : accessAddress e1 (Base.toAddressMasked w) with ⟨cold, e2⟩
  have m2 : e2.memory = evm.memory := by
    have := memory_accessAddress e1 (Base.toAddressMasked w)
    rw [hpair] at this
    exact this.trans (popWord_eq_ok h1).2.1
  simp only [hpair] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    rw [memory_finishSelfdestruct h, memory_chargeStateGas h4, memory_chargeGas h3]
    exact m2
  · exact m2

/-- SELFDESTRUCT writes the transfer log of the balance it moves, none before Glamsterdam. -/
theorem finishSelfdestruct_logs {beneficiary : Address} {refund : Nat} {Meter : Type}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.substate.logs =
      pushTransferLog fork evm.substate.logs evm.message.currentTarget beneficiary
        (evm.state.getAccount evm.message.currentTarget).balance := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    rfl

end EthLib.Execution.Evm
