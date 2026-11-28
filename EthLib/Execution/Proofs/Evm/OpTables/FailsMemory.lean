module

public import EthLib.Execution.Proofs.Evm.OpTables.Fails

/-!
# Proofs: the errors of control flow, memory, the environment and RETURN follow the tables

Each one fails on a stack error only when the stack is too short or would grow too high.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-! ## Control flow -/

/-- JUMP fails by its tables. -/
theorem jumpStep_fails {evm : Evm fork Meter} {e : EvmError} (h : jumpStep evm = .error e) :
    FailsByTables 1 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, -, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  split at h
  · cases h
  · cases h
    exact .of_halts nofun nofun rfl

/-- JUMPI fails by its tables. -/
theorem jumpiStep_fails {evm : Evm fork Meter} {e : EvmError} (h : jumpiStep evm = .error e) :
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
  split at h
  · cases h
  · cases h
    exact .of_halts nofun nofun rfl

/-- JUMPDEST fails by its tables. -/
theorem jumpdestStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : jumpdestStep evm = .error e) : FailsByTables 0 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  · cases h

/-- Each instruction of control flow fails by its tables. -/
theorem controlFlowStep_fails {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8} {e : EvmError}
    (hf : controlFlowStep op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .error e) : FailsByTables takes leaves evm e := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  case stop => cases h
  all_goals first
    | exact readFrame_fails h
    | exact jumpStep_fails h
    | exact jumpiStep_fails h
    | exact jumpdestStep_fails h

/-! ## Memory -/

/-- MLOAD fails by its tables. -/
theorem mloadStep_fails {evm : Evm fork Meter} {e : EvmError} (h : mloadStep evm = .error e) :
    FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨e2, h2, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((popWord_moves h1).trans (chargeGasAndMemory_moves h2)) h
  · cases h

/-- MSTORE fails by its tables. -/
theorem mstoreStep_fails {evm : Evm fork Meter} {e : EvmError} (h : mstoreStep evm = .error e) :
    FailsByTables 2 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, -, h⟩
  · exact .pop (popWord_moves h1) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  · cases h

/-- MSTORE8 fails by its tables. -/
theorem mstore8Step_fails {evm : Evm fork Meter} {e : EvmError}
    (h : mstore8Step evm = .error e) : FailsByTables 2 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, -, h⟩
  · exact .pop (popWord_moves h1) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  · cases h

/-- MCOPY fails by its tables. -/
theorem mcopyStep_fails {evm : Evm fork Meter} {e : EvmError} (h : mcopyStep evm = .error e) :
    FailsByTables 3 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  rcases Base.bind_eq_error h with h | ⟨⟨_, e3⟩, -, h⟩
  · exact .pop (m1.trans (popWord_moves h2)) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  · cases h

/-- CALLDATALOAD fails by its tables. -/
theorem calldataloadStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : calldataloadStep evm = .error e) : FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨e2, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((popWord_moves h1).trans (chargeGas_moves h2)) h
  · cases h

/-- A copy to memory fails by its tables. -/
theorem copyToMemory_fails {base : Nat} {source : ByteArray} {evm : Evm fork Meter}
    {e : EvmError} (h : copyToMemory base source evm = .error e) : FailsByTables 3 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  rcases Base.bind_eq_error h with h | ⟨⟨_, e3⟩, -, h⟩
  · exact .pop (m1.trans (popWord_moves h2)) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  · cases h

/-- RETURNDATACOPY fails by its tables. -/
theorem returndatacopyStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : returndatacopyStep evm = .error e) : FailsByTables 3 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  rcases Base.bind_eq_error h with h | ⟨⟨_, e3⟩, -, h⟩
  · exact .pop (m1.trans (popWord_moves h2)) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  dsimp only at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · cases h
      exact .of_halts nofun nofun rfl
    · cases h
  · cases h

/-- Each instruction that moves bytes to or from memory fails by its tables. -/
theorem memoryDataStep_fails {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8} {e : EvmError}
    (hf : memoryDataStep op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .error e) : FailsByTables takes leaves evm e := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  case mload => exact mloadStep_fails h
  case mstore => exact mstoreStep_fails h
  case mstore8 => exact mstore8Step_fails h
  case mcopy => exact mcopyStep_fails h
  case calldataload => exact calldataloadStep_fails h
  case calldatacopy => exact copyToMemory_fails h
  case codecopy => exact copyToMemory_fails h
  case returndatacopy => exact returndatacopyStep_fails h
  all_goals exact readFrame_fails h

/-! ## RETURN and REVERT -/

/-- A halt with output fails by the tables of RETURN. -/
theorem haltWithOutput_fails {evm : Evm fork Meter} {e : EvmError}
    (h : haltWithOutput evm = .error e) : FailsByTables 2 0 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, -, h⟩
  · exact .pop (popWord_moves h1) h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  · cases h

/-- RETURN and REVERT fail by their tables. -/
theorem returnOpStep_fails {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8} {e : EvmError}
    (hf : returnOpStep fork op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .error e) : FailsByTables takes leaves evm e := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  · subst hf
    exact haltWithOutput_fails h
  · split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact haltWithOutput_fails h
      · cases h
    · cases hf

/-! ## The environment -/

/-- BLOCKHASH fails by its tables. -/
theorem blockhashStep_fails {evm : Evm fork Meter} {e : EvmError}
    (h : blockhashStep evm = .error e) : FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨e2, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((popWord_moves h1).trans (chargeGas_moves h2)) h
  · cases h

/-- BLOBHASH fails by its tables. -/
theorem blobhashStep_fails {hf : .dencun ≤ fork} {evm : Evm fork Meter} {e : EvmError}
    (h : blobhashStep hf evm = .error e) : FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  rcases Base.bind_eq_error h with h | ⟨e2, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push ((popWord_moves h1).trans (chargeGas_moves h2)) h
  · cases h

/-- Each instruction that reads the environment fails by its tables. -/
theorem environmentStep_fails {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8} {e : EvmError}
    (hf : environmentStep fork op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .error e) : FailsByTables takes leaves evm e := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  all_goals first
    | cases hf
    | exact readFrame_fails h
    | exact readNumber_fails h
    | exact blockhashStep_fails h
    | exact blobhashStep_fails h

end EthLib.Execution.Evm
