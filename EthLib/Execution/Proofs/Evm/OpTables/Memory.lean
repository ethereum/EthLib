module

public import EthLib.Execution.Proofs.Evm.OpTables.Parts

/-!
# Proofs: the instructions of control flow, memory, the environment and RETURN follow the tables

Each one takes and leaves the words of its tables, and pays its constant price.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-! ## Control flow -/

/-- JUMP takes a word and pays at least its price. -/
theorem jumpStep_moves {evm after : Evm fork Meter} (h : jumpStep evm = .ok after) :
    Moves 1 0 OPCODE_JUMP evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  have m := ((popWord_moves h1).trans (chargeGas_moves h2)).weaken (t' := 1) (l' := 0)
    (p' := OPCODE_JUMP)
  split at h
  · cases h
    exact m.keep rfl rfl rfl rfl
  · cases h

/-- JUMPI takes two words and pays at least its price. -/
theorem jumpiStep_moves {evm after : Evm fork Meter} (h : jumpiStep evm = .ok after) :
    Moves 2 0 OPCODE_JUMPI evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  have m := (((popWord_moves h1).trans (popWord_moves h2)).trans (chargeGas_moves h3)).weaken
    (t' := 2) (l' := 0) (p' := OPCODE_JUMPI)
  split at h
  · cases h
    exact m.keep rfl rfl rfl rfl
  · split at h
    · cases h
      exact m.keep rfl rfl rfl rfl
    · cases h

/-- JUMPDEST pays at least its price. -/
theorem jumpdestStep_moves {evm after : Evm fork Meter} (h : jumpdestStep evm = .ok after) :
    Moves 0 0 OPCODE_JUMPDEST evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (chargeGas_moves h1).keep rfl rfl rfl rfl

/-- Each instruction of control flow follows the tables. -/
theorem controlFlowStep_moves {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8}
    (hf : controlFlowStep op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .ok after) : Moves takes leaves (op.constantGas fork) evm after := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  case stop =>
    cases h
    exact .of_eq rfl rfl rfl rfl
  all_goals first
    | exact readFrame_moves h
    | exact jumpStep_moves h
    | exact jumpiStep_moves h
    | exact jumpdestStep_moves h

/-! ## Memory -/

/-- MLOAD takes a word, leaves one and pays at least its price. -/
theorem mloadStep_moves {evm after : Evm fork Meter} (h : mloadStep evm = .ok after) :
    Moves 1 1 OPCODE_MLOAD_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (chargeGasAndMemory_moves h2)).trans
    (pushWord_moves h3)).trans (advance_moves _ _)).weaken

/-- MSTORE takes two words and pays at least its price. -/
theorem mstoreStep_moves {evm after : Evm fork Meter} (h : mstoreStep evm = .ok after) :
    Moves 2 0 OPCODE_MSTORE_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (popWord_moves h2)).trans
    (chargeGasAndMemory_moves h3)).weaken (t' := 2) (l' := 0) (p' := OPCODE_MSTORE_BASE)).keep
    rfl rfl rfl rfl

/-- MSTORE8 takes two words and pays at least its price. -/
theorem mstore8Step_moves {evm after : Evm fork Meter} (h : mstore8Step evm = .ok after) :
    Moves 2 0 OPCODE_MSTORE8_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (popWord_moves h2)).trans
    (chargeGasAndMemory_moves h3)).weaken (t' := 2) (l' := 0) (p' := OPCODE_MSTORE8_BASE)).keep
    rfl rfl rfl rfl

/-- MCOPY takes three words and pays at least its price. -/
theorem mcopyStep_moves {evm after : Evm fork Meter} (h : mcopyStep evm = .ok after) :
    Moves 3 0 OPCODE_MCOPY_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((((popWord_moves h1).trans (popWord_moves h2)).trans (popWord_moves h3)).trans
    (chargeGasAndMemory_moves h4)).weaken (t' := 3) (l' := 0) (p' := OPCODE_MCOPY_BASE)).keep
    rfl rfl rfl rfl

/-- CALLDATALOAD takes a word, leaves one and pays at least its price. -/
theorem calldataloadStep_moves {evm after : Evm fork Meter}
    (h : calldataloadStep evm = .ok after) : Moves 1 1 OPCODE_CALLDATALOAD evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (chargeGas_moves h2)).trans (pushWord_moves h3)).trans
    (advance_moves _ _)).weaken

/-- A copy to memory takes three words and pays at least its price. -/
theorem copyToMemory_moves {base : Nat} {source : ByteArray} {evm after : Evm fork Meter}
    (h : copyToMemory base source evm = .ok after) : Moves 3 0 base evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((((popWord_moves h1).trans (popWord_moves h2)).trans (popWord_moves h3)).trans
    (chargeGasAndMemory_moves h4)).weaken (t' := 3) (l' := 0) (p' := base)).keep rfl rfl rfl rfl

/-- RETURNDATACOPY takes three words and pays at least its price. -/
theorem returndatacopyStep_moves {evm after : Evm fork Meter}
    (h : returndatacopyStep evm = .ok after) : Moves 3 0 OPCODE_RETURNDATACOPY_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  have m := ((((popWord_moves h1).trans (popWord_moves h2)).trans (popWord_moves h3)).trans
    (chargeGas_moves h4)).weaken (t' := 3) (l' := 0) (p' := OPCODE_RETURNDATACOPY_BASE)
  split at h
  · cases h
  · cases h
    exact m.keep rfl rfl rfl rfl

/-- Each instruction that moves bytes to or from memory follows the tables. -/
theorem memoryDataStep_moves {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8}
    (hf : memoryDataStep op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .ok after) : Moves takes leaves (op.constantGas fork) evm after := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  all_goals first
    | exact readFrame_moves h
    | exact mloadStep_moves h
    | exact mstoreStep_moves h
    | exact mstore8Step_moves h
    | exact mcopyStep_moves h
    | exact calldataloadStep_moves h
    | exact copyToMemory_moves h
    | exact returndatacopyStep_moves h

/-! ## RETURN and REVERT -/

/-- A halt with output takes two words. -/
theorem haltWithOutput_moves {evm after : Evm fork Meter} (h : haltWithOutput evm = .ok after) :
    Moves 2 0 0 evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (popWord_moves h2)).trans
    (chargeGasAndMemory_moves h3)).weaken (t' := 2) (l' := 0) (p' := 0)).keep rfl rfl rfl rfl

/-- RETURN and REVERT follow the tables. -/
theorem returnOpStep_moves {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8}
    (hf : returnOpStep fork op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .ok after) : Moves takes leaves (op.constantGas fork) evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  · subst hf
    exact haltWithOutput_moves h
  · split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (haltWithOutput_moves h1).keep rfl rfl rfl rfl
    · cases hf

/-! ## The environment -/

/-- BLOCKHASH takes a word, leaves one and pays at least its price. -/
theorem blockhashStep_moves {evm after : Evm fork Meter} (h : blockhashStep evm = .ok after) :
    Moves 1 1 OPCODE_BLOCKHASH evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (chargeGas_moves h2)).trans (pushWord_moves h3)).trans
    (advance_moves _ _)).weaken

/-- BLOBHASH takes a word, leaves one and pays at least its price. -/
theorem blobhashStep_moves {hf : .dencun ≤ fork} {evm after : Evm fork Meter}
    (h : blobhashStep hf evm = .ok after) : Moves 1 1 OPCODE_BLOBHASH evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (chargeGas_moves h2)).trans (pushWord_moves h3)).trans
    (advance_moves _ _)).weaken

/-- Each instruction that reads the environment follows the tables. -/
theorem environmentStep_moves {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8}
    (hf : environmentStep fork op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .ok after) : Moves takes leaves (op.constantGas fork) evm after := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  all_goals first
    | cases hf
    | exact readFrame_moves h
    | exact readNumber_moves h
    | exact blockhashStep_moves h
    | exact blobhashStep_moves h

end EthLib.Execution.Evm
