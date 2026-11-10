module

public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.Evm.Instructions.LogData
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Instructions.SelfDestruct
public import EthLib.Execution.Proofs.Evm.Instructions.StackOnly
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.TransientStorage
public import EthLib.Execution.Proofs.Evm.Step
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the reads of an instruction

From Glamsterdam, an instruction checks the gas it knows before it reads the state.

Before Glamsterdam, that check always passes.

An exceptional halt keeps the state of the frame, so it keeps the reads that the frame made.

BALANCE, EXTCODESIZE, EXTCODECOPY and EXTCODEHASH each read the account at their address.

SELFBALANCE reads the current account.

SLOAD and SSTORE each read their slot in the storage of the current account.

SSTORE records that read even when it then halts, as EIP-7928 asks.

SELFDESTRUCT reads its beneficiary even when it then halts.

When it completes, it also reads the current account.

BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH, SELFBALANCE and SLOAD add exactly that read.

They keep every other read.

Every other instruction that gives the next frame keeps the account reads and the storage reads.
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

omit [GasMeter Meter] in
/-- An access to an address keeps the state, with its reads. -/
theorem state_accessAddress (evm : Evm fork Meter) (address : Address) :
    (accessAddress evm address).2.state = evm.state := by
  unfold accessAddress
  split <;> rfl

omit [GasMeter Meter] in
/-- An access to a storage key keeps the state, with its reads. -/
theorem state_accessStorageKey (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    (accessStorageKey evm address key).2.state = evm.state := by
  unfold accessStorageKey
  split <;> rfl

/-- BALANCE adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_balanceStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : balanceStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  rw [balanceStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    rw [state_accessAddress]
    exact ⟨rfl, rfl⟩

/-- EXTCODESIZE adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_extcodesizeStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : extcodesizeStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  rcases hacc : accessAddress e1 (Base.toAddressMasked word) with ⟨cold, e2⟩
  have s2 : e2.state = evm.state := by
    have s := state_accessAddress e1 (Base.toAddressMasked word)
    rw [hacc] at s
    exact s.trans (popWord_sameContext h1).state
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [(pushWord_sameContext h4).advance.state, ← s2, ← (chargeGas_sameContext h3).state]
  exact ⟨rfl, rfl⟩

/-- EXTCODECOPY adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_extcodecopyStep {evm after : Evm fork Meter} {word start offset size : U256}
    {rest : List U256} (hs : evm.stack.val = word :: start :: offset :: size :: rest)
    (h : extcodecopyStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (Base.toAddressMasked word) with ⟨cold, e5⟩
  have s5 : e5.state = evm.state := by
    have s := state_accessAddress e4 (Base.toAddressMasked word)
    rw [hacc] at s
    exact s.trans ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
      (popWord_sameContext h3)).trans (popWord_sameContext h4)).state
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [← s5, ← (chargeGasAndMemory_sameContext h6).state]
  exact ⟨rfl, rfl⟩

/-- EXTCODEHASH adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_extcodehashStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : extcodehashStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  rw [extcodehashStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    rw [state_accessAddress]
    exact ⟨rfl, rfl⟩

/-- SELFBALANCE adds the current account to the account reads.

It keeps every other read.

It has no step of its own: it reads the frame once the read is recorded. -/
theorem reads_selfbalanceStep {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} (hstep : accountStep fork .selfbalance = some run)
    (h : run evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert evm.message.currentTarget ∧
      after.state.storageReads = evm.state.storageReads := by
  simp only [accountStep] at hstep
  split at hstep
  · simp only [Option.some.injEq] at hstep
    subst hstep
    rw [(readFrame_sameContext h).state]
    exact ⟨rfl, rfl⟩
  · cases hstep

/-- SLOAD adds its slot to the storage reads of the current account.

It keeps every other read. -/
theorem reads_sloadStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : sloadStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads ∧
      after.state.storageReads = evm.state.storageReads.insert evm.message.currentTarget
        ((evm.state.storageReads.getD evm.message.currentTarget ∅).insert
          (U256.toBeBytes word)) := by
  rw [sloadStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    rw [state_accessStorageKey]
    exact ⟨rfl, rfl⟩

/-- The transfer of SELFDESTRUCT adds the originator and the beneficiary to the account reads. -/
theorem accountReads_selfdestructTransfer {tx tx' : State.TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.accountReads = (tx.accountReads.insert originator).insert beneficiary := by
  unfold selfdestructTransfer at h
  dsimp only at h
  split at h
  · obtain ⟨mid, hmove, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨hmid, -⟩ := State.TransactionState.reads_moveEther hmove
    split at h
    · obtain ⟨hset, -⟩ := State.TransactionState.reads_setAccountBalance h
      rw [hset, hmid]
      ext a
      simp [Std.ExtTreeSet.mem_insert, or_left_comm]
    · cases h
      exact hmid
  · obtain ⟨mid, hcreate, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨hmid, -⟩ := State.TransactionState.reads_createEther hcreate
    obtain ⟨hset, -⟩ := State.TransactionState.reads_setAccountBalance h
    rw [hset, hmid]
    ext a
    simp [Std.ExtTreeSet.mem_insert, or_left_comm]

omit [GasMeter Meter] in
/-- Completing SELFDESTRUCT adds the current account and the beneficiary to the account reads. -/
theorem accountReads_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.state.accountReads =
      (evm.state.accountReads.insert evm.message.currentTarget).insert beneficiary := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨state, htr, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have htr' : selfdestructTransfer fork evm.state evm.message.currentTarget beneficiary =
        .ok state := by
      revert htr
      cases selfdestructTransfer fork evm.state evm.message.currentTarget beneficiary <;>
        simp [Except.mapError]
    exact accountReads_selfdestructTransfer htr'

/-- SELFDESTRUCT adds its beneficiary to the account reads, even when it then halts.

When it completes, it also adds the current account. -/
theorem accountReads_selfdestructStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest)
    (h : selfdestructStep fork evm = .ok after) :
    (after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
        ∃ e, after.error = some e) ∨
      after.state.accountReads =
        (evm.state.accountReads.insert evm.message.currentTarget).insert
          (Base.toAddressMasked word) := by
  unfold selfdestructStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  have c1 := popWord_sameContext h1
  dsimp only at h
  rcases hacc : accessAddress e1 (Base.toAddressMasked word) with ⟨cold, e2⟩
  have c2 : e2.message = evm.message ∧ e2.state = evm.state := by
    obtain ⟨_, ha⟩ := accessAddress_snd e1 (Base.toAddressMasked word)
    rw [hacc] at ha
    dsimp only at ha
    rw [ha]
    exact ⟨c1.message, c1.state⟩
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have c4 := (chargeGas_sameContext h3).trans (chargeStateGas_sameContext h4)
    right
    rw [accountReads_finishSelfdestruct h, c4.message, c4.state]
    show ((e2.state.accountReads.insert _).insert e2.message.currentTarget).insert _ = _
    rw [c2.1, c2.2]
    ext a
    simp [Std.ExtTreeSet.mem_insert, or_left_comm]
  · left
    exact ⟨by rw [← c2.2]; rfl, e, rfl⟩


/-- Every other instruction that gives the next frame keeps the account and storage reads.

The eight instructions that read an account or a storage slot are left out. -/
theorem reads_instruction {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} (hrun : instruction fork op = some run)
    (ordinary : op ∉ [.balance, .selfbalance, .extcodesize, .extcodecopy, .extcodehash,
      .sload, .sstore, .selfdestruct])
    (h : run evm = .ok after) :
    after.state.accountReads = evm.state.accountReads ∧
      after.state.storageReads = evm.state.storageReads := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (stackOnlyStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (controlFlowStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (memoryDataStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
    case «return» =>
      subst hf
      have hs := (returnStep_sameContext h).state
      exact ⟨by rw [hs], by rw [hs]⟩
    case revert =>
      split at hf
      · cases hf
        have hs := (revertStep_sameContext h).state
        exact ⟨by rw [hs], by rw [hs]⟩
      · cases hf
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (environmentStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [accountStep, reduceCtorEq] at hf <;> exact absurd (by simp) ordinary
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;>
      exact absurd (by simp) ordinary
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · have hs := (tloadStep_sameContext h).state
      exact ⟨by rw [hs], by rw [hs]⟩
    · obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨⟨v, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · cases h
        have hs := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
          (chargeGas_sameContext h3)).state
        obtain ⟨ha, hst⟩ := State.TransactionState.reads_setTransientStorage e3.state
          e3.message.currentTarget (U256.toBeBytes w) v
        exact ⟨ha.trans (by rw [hs]), hst.trans (by rw [hs])⟩
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, -, hs, -⟩ := logStep_eq_ok h
    exact ⟨by rw [hs], by rw [hs]⟩
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    exact absurd (by simp) ordinary

end EthLib.Execution.Evm
