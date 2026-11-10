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

SELFBALANCE reads the account of the current target.

SLOAD and SSTORE each read their slot in the storage of the current account.

SSTORE records that read even when it then halts, as EIP-7928 asks.

SELFDESTRUCT reads its beneficiary even when it then halts, and the current account on success.

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

/-- EXTCODESIZE reads the account at its address. -/
theorem mem_accountReads_extcodesizeStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest)
    (h : extcodesizeStep evm = .ok after) :
    Base.toAddressMasked word ∈ after.state.accountReads := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  rcases hacc : accessAddress e1 (Base.toAddressMasked word) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have s4 := (pushWord_sameContext h4).advance.state
  rw [s4]
  exact (State.TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)

/-- EXTCODECOPY reads the account at its address. -/
theorem mem_accountReads_extcodecopyStep {evm after : Evm fork Meter}
    {word start offset size : U256} {rest : List U256}
    (hs : evm.stack.val = word :: start :: offset :: size :: rest)
    (h : extcodecopyStep evm = .ok after) :
    Base.toAddressMasked word ∈ after.state.accountReads := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  obtain ⟨⟨_, e2⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, -, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (Base.toAddressMasked word) with ⟨cold, e5⟩
  simp only [hacc] at h
  obtain ⟨e6, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (State.TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)

/-- EXTCODEHASH reads the account at its address. -/
theorem mem_accountReads_extcodehashStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest)
    (h : extcodehashStep evm = .ok after) :
    Base.toAddressMasked word ∈ after.state.accountReads := by
  rw [extcodehashStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    exact (State.TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)

/-- SELFBALANCE reads the account of the current target. -/
theorem mem_accountReads_selfbalanceStep {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} (hstep : accountStep fork .selfbalance = some run)
    (h : run evm = .ok after) : evm.message.currentTarget ∈ after.state.accountReads := by
  simp only [accountStep] at hstep
  split at hstep
  · simp only [Option.some.injEq] at hstep
    subst hstep
    rw [(readFrame_sameContext h).state]
    exact (State.TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)
  · cases hstep

/-- SLOAD reads its slot in the storage of the current account. -/
theorem mem_storageReads_sloadStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest) (h : sloadStep evm = .ok after) :
    U256.toBeBytes word ∈ after.state.storageReads.getD evm.message.currentTarget ∅ := by
  rw [sloadStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    exact (State.TransactionState.mem_storageReads_recordStorageRead _ _ _ _ _).mpr
      (.inl ⟨rfl, rfl⟩)

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

/-- SELFDESTRUCT reads its beneficiary, whether it then completes or halts.

When it completes, it also reads the current account. -/
theorem mem_accountReads_selfdestructStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest)
    (h : selfdestructStep fork evm = .ok after) :
    Base.toAddressMasked word ∈ after.state.accountReads ∧
      (after.error = none → evm.message.currentTarget ∈ after.state.accountReads) := by
  unfold selfdestructStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  have m1 := (popWord_sameContext h1).message
  dsimp only at h
  rcases hacc : accessAddress e1 (Base.toAddressMasked word) with ⟨cold, e2⟩
  have ha : e2.message = e1.message := by
    have e2eq : e2 = (accessAddress e1 (Base.toAddressMasked word)).2 := by rw [hacc]
    rw [e2eq]
    obtain ⟨_, hacc2⟩ := accessAddress_snd e1 (Base.toAddressMasked word)
    rw [hacc2]
  have m2 : e2.message = evm.message := ha.trans m1
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have hben : Base.toAddressMasked word ∈
      (recordAccountRead e2 (Base.toAddressMasked word)).state.accountReads :=
    (State.TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.message = evm.message :=
      (chargeStateGas_sameContext h4).message.trans
        ((chargeGas_sameContext h3).message.trans m2)
    have hfin := accountReads_finishSelfdestruct h
    rw [hfin, m4]
    exact ⟨by simp [Std.ExtTreeSet.mem_insert], fun _ => by simp [Std.ExtTreeSet.mem_insert]⟩
  · exact ⟨hben, fun herr => by simp [exceptionalHalt] at herr⟩

/-- Every instruction that gives the next frame and reads no account or slot keeps the reads. -/
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
  · have hmem := (isSome_accountStep.mp (Option.isSome_iff_exists.mpr ⟨run, hf⟩)).1
    exact absurd (by simp_all : op ∈ [.balance, .selfbalance, .extcodesize, .extcodecopy,
      .extcodehash, .sload, .sstore, .selfdestruct]) ordinary
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
