module

public import EthLib.Execution.Proofs.Evm.Padding.Basic

/-!
# Proofs: the instructions of the state run the same on code with the same bytes

They read and write accounts, storage and transient storage, and never the code of the frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Each instruction of the accounts runs the same on code with the same bytes. -/
theorem accountStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) : SwapsCode run := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (intro evm code jumps _ _
       try simp only [balanceStep, extcodesizeStep, extcodecopyStep, extcodehashStep,
         accountCode]
       swap_code)

/-- SLOAD and SSTORE run the same on code with the same bytes. -/
theorem storageStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some run) : SwapsCode run := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;> intro evm code jumps _ _
  · simp only [sloadStep]
    swap_code
  · simp only [sstoreStep]
    swap_code

/-- TLOAD and TSTORE run the same on code with the same bytes. -/
theorem transientStorageStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some run) : SwapsCode run := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep <;>
    intro evm code jumps _ _
  · simp only [tloadStep]
    swap_code
  · simp only [tstoreStep]
    swap_code

/-- SELFDESTRUCT runs the same on code with the same bytes. -/
theorem selfdestructOpStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some run) : SwapsCode run := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  intro evm code jumps _ _
  simp only [selfdestructStep, finishSelfdestruct, selfdestructTransfer]
  swap_code

end EthLib.Execution.Evm
