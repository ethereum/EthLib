module

public import EthLib.Execution.Proofs.Evm.OpTables.Stack
public import EthLib.Execution.Proofs.Evm.OpTables.Memory
public import EthLib.Execution.Proofs.Evm.OpTables.State

/-!
# Proofs: each instruction that gives the next frame follows the tables

The instructions are those that send no message: all but the calls and the creations.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- Each instruction that gives the next frame follows the tables. -/
theorem instruction_follows {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} {takes leaves : Nat} (hrun : instruction fork op = some run)
    (hw : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : run evm = .ok after) : FollowsTables takes leaves (op.constantGas fork) evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact (stackOnlyStep_moves hf hw h).toFollows
  rcases orElse_eq_some hrun with hf | hrun
  · exact (controlFlowStep_moves hf hw h).toFollows
  rcases orElse_eq_some hrun with hf | hrun
  · exact (memoryDataStep_moves hf hw h).toFollows
  rcases orElse_eq_some hrun with hf | hrun
  · exact (returnOpStep_moves hf hw h).toFollows
  rcases orElse_eq_some hrun with hf | hrun
  · exact (environmentStep_moves hf hw h).toFollows
  rcases orElse_eq_some hrun with hf | hrun
  · exact (accountStep_moves hf hw h).toFollows
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    · exact (sloadStep_moves h).toFollows
    · exact sstoreStep_follows h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    · exact (tloadStep_moves h).toFollows
    · exact (tstoreStep_moves h).toFollows
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact (logStep_moves h).toFollows
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact selfdestructStep_follows h

end EthLib.Execution.Evm
