module

public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Step
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the reads of an instruction

From Glamsterdam, an instruction checks the gas it knows before it reads the state.

Before Glamsterdam, that check always passes.

An exceptional halt keeps the state of the frame, so it keeps the reads that the frame made.

BALANCE reads its account, and SSTORE its slot.

SSTORE records that read even when it then halts, as EIP-7928 asks.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Before Glamsterdam, the gas check passes. -/
theorem checkGas_of_lt_glamsterdam (h : fork < .glamsterdam) (evm : Evm fork Meter)
    (amount : Nat) : checkGas evm amount = .ok () := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp [checkGas, hpre, pure, Except.pure]

/-- From Glamsterdam, the gas check passes exactly when the frame has the amount left. -/
theorem checkGas_eq_ok_iff (h : fork ≥ .glamsterdam) {evm : Evm fork Meter} {amount : Nat} :
    checkGas evm amount = .ok () ↔ amount ≤ GasMeter.gasLeft evm.gas := by
  unfold checkGas
  by_cases hlt : GasMeter.gasLeft evm.gas < amount
  · simp [h, hlt, throw, throwThe, MonadExceptOf.throw]
  · simp [h, hlt, pure, Except.pure]
    omega

/-- An exceptional halt keeps the state of the frame, with its reads. -/
theorem state_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    (exceptionalHalt evm e).state = evm.state := rfl

/-- A storage write keeps the storage reads. -/
theorem storageReads_setStorage {tx tx' : State.TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.storageReads = tx.storageReads := by
  unfold State.TransactionState.setStorage at h
  split at h
  · cases h
  · cases h
    rfl

/-- SSTORE reads its slot, whether it then completes or halts.

The slot is the top word of the stack, in the storage of the current account. -/
theorem mem_storageReads_sstoreStep {evm after : Evm fork Meter} {key new : U256}
    {rest : List U256} (hs : evm.stack.val = key :: new :: rest)
    (h : sstoreStep evm = .ok after) :
    U256.toBeBytes key ∈ after.state.storageReads.getD evm.message.currentTarget ∅ := by
  have hstack : evm.stack = ⟨key :: new :: rest, hs ▸ evm.stack.property⟩ := Subtype.ext hs
  unfold sstoreStep at h
  split at h
  · cases h
  simp only [popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  generalize accessStorageKey _ evm.message.currentTarget (U256.toBeBytes key) = accessed at h
  obtain ⟨cold, e3⟩ := accessed
  have hread : U256.toBeBytes key ∈
      (recordStorageRead e3 evm.message.currentTarget (U256.toBeBytes key)).state.storageReads.getD
        evm.message.currentTarget ∅ :=
    (State.TransactionState.mem_storageReads_recordStorageRead _ _ _ _ _).mpr (.inl ⟨rfl, rfl⟩)
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    obtain ⟨state, hset, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have s4 := (chargeGas_sameContext h4).state
    have s5 : e5.state = e4.state := by
      obtain ⟨_, -, h5⟩ := Base.bind_ok_iff.mp h5
      cases h5
      rfl
    have hset' : e5.state.setStorage evm.message.currentTarget (U256.toBeBytes key) new =
        .ok state := by
      revert hset
      cases e5.state.setStorage evm.message.currentTarget (U256.toBeBytes key) new <;>
        simp [Except.mapError]
    show U256.toBeBytes key ∈ state.storageReads.getD _ ∅
    rw [storageReads_setStorage hset', s5, s4]
    exact hread
  · exact hread

/-- BALANCE reads the account at its address. -/
theorem mem_accountReads_balanceStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest) (h : balanceStep evm = .ok after) :
    Base.toAddressMasked word ∈ after.state.accountReads := by
  rw [balanceStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    exact (State.TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)

end EthLib.Execution.Evm
