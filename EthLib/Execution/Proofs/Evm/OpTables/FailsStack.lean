module

public import EthLib.Execution.Proofs.Evm.OpTables.Fails
public import EthLib.Execution.Proofs.Evm.Instructions.StackN

/-!
# Proofs: the errors of the instructions that read and write only the stack follow the tables

Each one fails on a stack error only when the stack is too short or would grow too high.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- POP fails by its tables. -/
theorem popStep_fails {evm : Evm fork Meter} {e : EvmError} (h : popStep evm = .error e) :
    FailsByTables 1 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, -, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  · cases h

/-- PUSHn fails by its tables. -/
theorem pushN_fails {n : Fin 33} {evm : Evm fork Meter} {e : EvmError}
    (h : pushN n evm = .error e) : FailsByTables 0 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨e1, h1, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push (chargeGas_moves h1) h
  · cases h

/-- DUPn fails by its tables. -/
theorem dupN_fails {n : Fin 16} {evm : Evm fork Meter} {e : EvmError}
    (h : dupN n evm = .error e) : FailsByTables (n.val + 1) (n.val + 2) evm e := by
  rcases Base.bind_eq_error h with h | ⟨e1, h1, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  have m1 := chargeGas_moves h1
  have := m1.stack
  split at h
  · rename_i hx
    cases h
    have := List.getElem?_eq_none_iff.mp hx
    exact .of_underflow (by omega)
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact .push m1 h
    · cases h

/-- SWAPn fails by its tables. -/
theorem swapN_fails {n : Fin 16} {evm : Evm fork Meter} {e : EvmError}
    (h : swapN n evm = .error e) : FailsByTables (n.val + 2) (n.val + 2) evm e := by
  rcases Base.bind_eq_error h with h | ⟨e1, h1, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  have := (chargeGas_moves h1).stack
  split at h
  · rename_i top rest hs hstack
    have hlen : e1.stack.val.length = rest.length + 1 := by rw [hstack]; rfl
    split at h
    · rename_i hx
      cases h
      have := List.getElem?_eq_none_iff.mp hx
      exact .of_underflow (by omega)
    · cases h
  · rename_i hs hstack
    cases h
    have hlen : e1.stack.val.length = 0 := by rw [hstack]; rfl
    exact .of_underflow (by omega)

/-- DUPN fails by its tables, for the depth of its immediate byte. -/
theorem dupnStep_fails {evm : Evm fork Meter} {n : Nat} {e : EvmError}
    (hn : decodeSingle (immediateByte evm.code evm.pc) = some n) (h : dupnStep evm = .error e) :
    FailsByTables n (n + 1) evm e := by
  cases hc : GasMeter.charge evm.gas OPCODE_DUPN with
  | error e' =>
    rw [dupnStep_of_charge_eq_error hc] at h
    cases h
    rw [LawfulGasMeter.charge_error hc]
    exact .outOfGas
  | ok g =>
    rcases (dupnStep_eq_error_iff hc).mp h with ⟨hn', -⟩ | ⟨n', hn', hcase⟩
    · rw [hn] at hn'
      cases hn'
    rw [hn] at hn'
    cases hn'
    rcases hcase with ⟨hl, rfl⟩ | ⟨-, hl, rfl⟩
    · exact .of_underflow hl
    · exact .of_overflow (by omega)

/-- SWAPN fails by its tables, for the depth of its immediate byte. -/
theorem swapnStep_fails {evm : Evm fork Meter} {n : Nat} {e : EvmError}
    (hn : decodeSingle (immediateByte evm.code evm.pc) = some n) (h : swapnStep evm = .error e) :
    FailsByTables (n + 1) (n + 1) evm e := by
  cases hc : GasMeter.charge evm.gas OPCODE_SWAPN with
  | error e' =>
    rw [swapnStep_of_charge_eq_error hc] at h
    cases h
    rw [LawfulGasMeter.charge_error hc]
    exact .outOfGas
  | ok g =>
    rcases (swapnStep_eq_error_iff hc).mp h with ⟨hn', -⟩ | ⟨n', hn', hl, rfl⟩
    · rw [hn] at hn'
      cases hn'
    rw [hn] at hn'
    cases hn'
    exact .of_underflow (by omega)

/-- EXCHANGE fails by its tables, for the depths of its immediate byte. -/
theorem exchangeStep_fails {evm : Evm fork Meter} {n m : Nat} {e : EvmError}
    (hn : decodePair (immediateByte evm.code evm.pc) = some (n, m))
    (h : exchangeStep evm = .error e) : FailsByTables (m + 1) (m + 1) evm e := by
  cases hc : GasMeter.charge evm.gas OPCODE_EXCHANGE with
  | error e' =>
    rw [exchangeStep_of_charge_eq_error hc] at h
    cases h
    rw [LawfulGasMeter.charge_error hc]
    exact .outOfGas
  | ok g =>
    rcases (exchangeStep_eq_error_iff hc).mp h with ⟨hn', -⟩ | ⟨n', m', hn', hl, rfl⟩
    · rw [hn] at hn'
      cases hn'
    rw [hn] at hn'
    cases hn'
    exact .of_underflow (by omega)

/-- EXP fails by its tables. -/
theorem expStep_fails {evm : Evm fork Meter} {e : EvmError} (h : expStep fork evm = .error e) :
    FailsByTables 2 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  rcases Base.bind_eq_error h with h | ⟨e3, h3, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push (m2.trans (chargeGas_moves h3)) h
  · cases h

/-- KECCAK256 fails by its tables. -/
theorem keccak256Step_fails {evm : Evm fork Meter} {e : EvmError}
    (h : keccak256Step evm = .error e) : FailsByTables 2 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  rcases Base.bind_eq_error h with h | ⟨e3, h3, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push (m2.trans (chargeGasAndMemory_moves h3)) h
  · cases h

/-- Each instruction that reads and writes only the stack fails by its tables. -/
theorem stackOnlyStep_fails {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm : Evm fork Meter} {takes leaves : Nat} {e : EvmError}
    (hf : stackOnlyStep fork op = some f)
    (hw : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : f evm = .error e) : FailsByTables takes leaves evm e := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hf
  case dupn =>
    split at hf
    · cases hf
      obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp hw
      cases he
      exact dupnStep_fails hn h
    · cases hf
  case swapn =>
    split at hf
    · cases hf
      obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp hw
      cases he
      exact swapnStep_fails hn h
    · cases hf
  case exchange =>
    split at hf
    · cases hf
      obtain ⟨⟨n, m⟩, hn, he⟩ := Option.map_eq_some_iff.mp hw
      cases he
      exact exchangeStep_fails hn h
    · cases hf
  all_goals subst hf
  all_goals simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw
  all_goals obtain ⟨rfl, rfl⟩ := hw
  case push n => exact pushN_fails h
  all_goals first
    | exact binaryOp_fails h
    | exact unaryOp_fails h
    | exact ternaryOp_fails h
    | exact expStep_fails h
    | exact keccak256Step_fails h
    | exact popStep_fails h
    | exact dupN_fails h
    | exact swapN_fails h

end EthLib.Execution.Evm
