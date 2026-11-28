module

public import EthLib.Execution.Proofs.Evm.OpTables.FailsStack
public import EthLib.Execution.Proofs.Evm.OpTables.FailsMemory

/-!
# Proofs: the errors of the instructions that read accounts, use storage or log follow the tables

Each one fails on a stack error only when the stack is too short or would grow too high.

A read of the state that aborts the run comes only once the instruction has taken its words.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- A read of the code of an account fails only with an error that aborts the run. -/
theorem accountCode_error {evm : Evm fork Meter} {address : Address} {e : EvmError}
    (h : accountCode evm address = .error e) : e.aborts = true := by
  unfold accountCode at h
  cases hc : evm.state.getCode (evm.state.getAccount address).codeHash with
  | error e' =>
    rw [hc] at h
    cases h
    rfl
  | ok code =>
    rw [hc] at h
    cases h

variable [LawfulGasMeter Meter]

/-! ## Other accounts -/

/-- BALANCE fails by its tables. -/
theorem balanceStep_fails {evm : Evm fork Meter} {e : EvmError} (h : balanceStep evm = .error e) :
    FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨word, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨_, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((((popWord_moves h1).trans (accessAddress_moves _ _)).trans
      (chargeGas_moves h2)).trans (recordAccountRead_moves _ _)) h
  · cases h

/-- EXTCODESIZE fails by its tables. -/
theorem extcodesizeStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : extcodesizeStep evm = .error e) : FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨word, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨_, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  have m := (((popWord_moves h1).trans (accessAddress_moves _ _)).trans
    (chargeGas_moves h2)).trans (recordAccountRead_moves _ (Base.toAddressMasked word))
  dsimp only at h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .of_aborts m (by omega) (accountCode_error h)
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push m h
  · cases h

/-- EXTCODECOPY fails by its tables. -/
theorem extcodecopyStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : extcodecopyStep evm = .error e) : FailsByTables 4 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨word, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e3⟩, h3, h⟩
  · exact .pop m2 h
  have m3 := m2.trans (popWord_moves h3)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e4⟩, h4, h⟩
  · exact .pop m3 h
  have m4 := m3.trans (popWord_moves h4)
  rcases Base.bind_eq_error h with h | ⟨_, h5, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  have m := ((m4.trans (accessAddress_moves _ _)).trans (chargeGasAndMemory_moves h5)).trans
    (recordAccountRead_moves _ (Base.toAddressMasked word))
  dsimp only at h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .of_aborts m (by omega) (accountCode_error h)
  · cases h

/-- EXTCODEHASH fails by its tables. -/
theorem extcodehashStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : extcodehashStep evm = .error e) : FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨word, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨_, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((((popWord_moves h1).trans (accessAddress_moves _ _)).trans
      (chargeGas_moves h2)).trans (recordAccountRead_moves _ _)) h
  · cases h

/-- Each instruction that reads another account fails by its tables. -/
theorem accountStep_fails {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8} {e : EvmError}
    (hf : accountStep fork op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .error e) : FailsByTables takes leaves evm e := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  case balance => exact balanceStep_fails h
  case extcodesize => exact extcodesizeStep_fails h
  case extcodecopy => exact extcodecopyStep_fails h
  case extcodehash.isTrue => exact extcodehashStep_fails h
  case selfbalance.isTrue =>
    dsimp only at h
    exact .of_stack (b := recordAccountRead evm evm.message.currentTarget) rfl (readFrame_fails h)
  all_goals cases hf

/-! ## Storage -/

/-- SLOAD fails by its tables. -/
theorem sloadStep_fails {evm : Evm fork Meter} {e : EvmError} (h : sloadStep evm = .error e) :
    FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨word, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨_, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((((popWord_moves h1).trans (accessStorageKey_moves _ _ _)).trans
      (chargeGas_moves h2)).trans (recordStorageRead_moves _ _ _)) h
  · cases h

omit [LawfulGasMeter Meter] in
/-- SSTORE fails by its tables. -/
theorem sstoreStep_fails {evm : Evm fork Meter} {e : EvmError} (h : sstoreStep evm = .error e) :
    FailsByTables 2 0 evm e := by
  unfold sstoreStep at h
  split at h
  · cases h
    exact .writeInStaticContext
  rcases Base.bind_eq_error h with h | ⟨⟨word, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨new, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  dsimp only at h
  split at h
  · cases h
    exact .outOfGas
  have m := (m2.trans (accessStorageKey_moves e2 e2.message.currentTarget
    (U256.toBeBytes word))).trans
    (recordStorageRead_moves _ e2.message.currentTarget (U256.toBeBytes word))
  exact .of_aborts m (by omega) (keepReads_eq_error.mp h).2

/-! ## Transient storage -/

/-- TLOAD fails by its tables. -/
theorem tloadStep_fails {evm : Evm fork Meter} {e : EvmError} (h : tloadStep evm = .error e) :
    FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨_, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((popWord_moves h1).trans (chargeGas_moves h2)) h
  · cases h

/-- TSTORE fails by its tables. -/
theorem tstoreStep_fails {evm : Evm fork Meter} {e : EvmError} (h : tstoreStep evm = .error e) :
    FailsByTables 2 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, -, h⟩
  · exact .pop (popWord_moves h1) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  split at h
  · cases h
    exact .writeInStaticContext
  · cases h

/-! ## Logs -/

omit [LawfulGasMeter Meter] in
/-- The pops of the topics of a log fail by the tables of a step that takes them too. -/
theorem popTopics_fails {before evm : Evm fork Meter} {n t p l : Nat} {e : EvmError}
    (m : Moves t 0 p before evm) (h : popTopics evm n = .error e) :
    FailsByTables (t + n) l before e := by
  induction n generalizing evm t with
  | zero => cases h
  | succ k ih =>
    rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
    · exact .pop m h
    rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, -, h⟩
    · have := ih ((m.trans (popWord_moves h1)).weaken (t' := t + 1) (l' := 0) (p' := p)) h
      rwa [show t + 1 + k = t + (k + 1) by omega] at this
    · cases h

/-- LOGn fails by its tables. -/
theorem logStep_fails {n : Nat} {evm : Evm fork Meter} {e : EvmError}
    (h : logStep n evm = .error e) : FailsByTables (n + 2) 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := (m1.trans (popWord_moves h2)).weaken (t' := 2) (l' := 0) (p' := 0)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e3⟩, -, h⟩
  · rw [Nat.add_comm n 2]
    exact popTopics_fails m2 h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  split at h
  · cases h
    exact .writeInStaticContext
  · cases h

/-! ## SELFDESTRUCT -/

omit [LawfulGasMeter Meter] in
/-- SELFDESTRUCT fails by its tables. -/
theorem selfdestructStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : selfdestructStep fork evm = .error e) : FailsByTables 1 0 evm e := by
  unfold selfdestructStep at h
  split at h
  · cases h
    exact .writeInStaticContext
  rcases Base.bind_eq_error h with h | ⟨⟨word, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  dsimp only at h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [checkGas_error h]
    exact .outOfGas
  have m := ((popWord_moves h1).trans (accessAddress_moves e1 (Base.toAddressMasked word))).trans
    (recordAccountRead_moves _ (Base.toAddressMasked word))
  exact .of_aborts m (by omega) (keepReads_eq_error.mp h).2

/-! ## Every instruction that gives the next frame -/

/-- Each instruction that gives the next frame fails by its tables. -/
theorem instruction_fails {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm : Evm fork Meter} {takes leaves : Nat} {e : EvmError}
    (hrun : instruction fork op = some run)
    (hw : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : run evm = .error e) : FailsByTables takes leaves evm e := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact stackOnlyStep_fails hf hw h
  rcases orElse_eq_some hrun with hf | hrun
  · exact controlFlowStep_fails hf hw h
  rcases orElse_eq_some hrun with hf | hrun
  · exact memoryDataStep_fails hf hw h
  rcases orElse_eq_some hrun with hf | hrun
  · exact returnOpStep_fails hf hw h
  rcases orElse_eq_some hrun with hf | hrun
  · exact environmentStep_fails hf hw h
  rcases orElse_eq_some hrun with hf | hrun
  · exact accountStep_fails hf hw h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    · exact sloadStep_fails h
    · exact sstoreStep_fails h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    · exact tloadStep_fails h
    · exact tstoreStep_fails h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact logStep_fails h
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact selfdestructStep_fails h

end EthLib.Execution.Evm
