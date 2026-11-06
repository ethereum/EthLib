module

public import EthLib.Execution.Proofs.Evm.Call.Create
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
public import EthLib.Execution.Proofs.Evm.Interpreter

/-!
# Proofs: the size of memory

The size of the memory of a frame is always a multiple of 32.

Memory grows only by whole words, from an empty memory, so the size stays a multiple of 32.

Each step keeps that size, and a call or a creation keeps it once its message ends.

So does every run of a frame, and the frame that ends every message, with all its messages.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Each instruction that gives the next frame keeps the size of memory a multiple of 32. -/
theorem size_instruction_mod {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) {evm after : Evm fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : run evm = .ok after) :
    after.memory.size % 32 = 0 := by
  have orElse : ∀ {α : Type} {a b : Option α} {x : α}, (a <|> b) = some x →
      a = some x ∨ b = some x := fun h => by
    rw [Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_some_iff] at h
    exact h.imp_right And.right
  unfold instruction at hrun
  rcases orElse hrun with hf | hrun
  · exact size_stackOnlyStep_mod hf hmod h
  rcases orElse hrun with hf | hrun
  · exact memory_controlFlowStep hf h ▸ hmod
  rcases orElse hrun with hf | hrun
  · exact size_memoryDataStep_mod hf hmod h
  rcases orElse hrun with hf | hrun
  · exact size_returnOpStep_mod hf hmod h
  rcases orElse hrun with hf | hrun
  · exact memory_environmentStep hf h ▸ hmod
  rcases orElse hrun with hf | hrun
  · exact size_accountStep_mod hf hmod h
  rcases orElse hrun with hf | hrun
  · exact memory_storageStep hf h ▸ hmod
  rcases orElse hrun with hf | hrun
  · exact memory_transientStorageStep hf h ▸ hmod
  rcases orElse hrun with hf | hf
  · exact size_logOpStep_mod hf hmod h
  · exact memory_selfdestructOpStep hf h ▸ hmod

/-- Each step keeps the size of memory a multiple of 32.

A step that sends a message keeps it in the frame that the resume gives. -/
theorem memoryAligned_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : step fork evm = .ok result) : result.MemoryAligned := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hrun
        obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
        exact size_instruction_mod hrun hmod hr
      · split at h
        · exact memoryAligned_messageInstruction ‹_› hmod h
        · cases h
  · obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
    cases hr
    exact hmod

/-- A run of a frame keeps the size of memory a multiple of 32, whatever runs its messages. -/
theorem size_runFrame_step_mod [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (hmod : evm.memory.size % 32 = 0)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.memory.size % 32 = 0 :=
  size_runFrame_mod (fun hmod h => memoryAligned_step hmod h)
    (fun hmod h resumed => memoryAligned_step hmod h _ _ resumed) hmod h

/-- A precompile keeps the memory of its frame. -/
theorem memory_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : after.memory = evm.memory := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    rfl
  · split at h <;> cases h <;> rfl

/-- The deposit of the code keeps the memory of the frame that ends the init code. -/
theorem memory_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) : after.memory = evm.memory := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    split <;> rfl
  split at h
  · cases h
    rfl
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- The frame that ends a message has a size of memory that is a multiple of 32.

That holds whatever messages the message sends, since each frame starts with empty memory. -/
theorem size_processMessage_mod [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended) :
    ended.val.memory.size % 32 = 0 := by
  rw [processMessage] at h
  obtain ⟨last, hlast, rfl⟩ := Base.map_ok_iff.mp h
  have hmod : last.val.memory.size % 32 = 0 := by
    dsimp only at hlast
    -- Both branches of the transfer start the same frame, with empty memory.
    split at hlast
    all_goals
      obtain ⟨_, -, hlast⟩ := Base.bind_ok_iff.mp hlast
      split at hlast
      · split at hlast
        · cases hlast
          rfl
        · split at hlast
          · cases hlast
            rename_i hp
            rw [memory_runPrecompile hp]
            rfl
          · cases hlast
            rfl
      · split at hlast
        · cases hlast
        · cases hlast
          rename_i hrun
          exact size_runFrame_step_mod rfl hrun
  unfold rollbackOnError
  split
  · exact hmod
  · exact hmod

/-- The frame that ends a creation has a size of memory that is a multiple of 32. -/
theorem size_processCreateMessage_mod [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    ended.val.memory.size % 32 = 0 := by
  rw [processCreateMessage] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
  · cases h
    rw [memory_depositCode ‹depositCode _ _ _ = .ok _›]
    exact size_processMessage_mod hrun

end EthLib.Execution.Evm
