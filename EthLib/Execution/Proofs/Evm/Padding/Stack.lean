module

public import EthLib.Execution.Proofs.Evm.Padding.Basic

/-!
# Proofs: the instructions of the stack run the same on code with the same bytes

PUSH reads its data from the code, and DUPN, SWAPN and EXCHANGE read their immediate byte.

They read both as bytes, with zeros past the end of the code.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- An instruction of one word runs the same on code with the same bytes. -/
private theorem unaryOp_swapsCode (cost : Nat) (f : U256 → U256) :
    SwapsCode (unaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm code jumps _ _
  swap_code

/-- An instruction of two words runs the same on code with the same bytes. -/
private theorem binaryOp_swapsCode (cost : Nat) (f : U256 → U256 → U256) :
    SwapsCode (binaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm code jumps _ _
  swap_code

/-- An instruction of three words runs the same on code with the same bytes. -/
private theorem ternaryOp_swapsCode (cost : Nat) (f : U256 → U256 → U256 → U256) :
    SwapsCode (ternaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm code jumps _ _
  swap_code

/-- EXP runs the same on code with the same bytes. -/
private theorem expStep_swapsCode : SwapsCode (expStep (Meter := Meter) fork) := by
  intro evm code jumps _ _
  simp only [expStep]
  swap_code

/-- KECCAK256 runs the same on code with the same bytes. -/
private theorem keccak256Step_swapsCode :
    SwapsCode (keccak256Step (fork := fork) (Meter := Meter)) := by
  intro evm code jumps _ _
  simp only [keccak256Step]
  swap_code

/-- POP runs the same on code with the same bytes. -/
private theorem popStep_swapsCode : SwapsCode (popStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps _ _
  simp only [popStep]
  swap_code

/-- PUSH reads the same data from code with the same bytes. -/
private theorem pushN_swapsCode (n : Fin 33) :
    SwapsCode (pushN (fork := fork) (Meter := Meter) n) := by
  intro evm code jumps hb _
  simp only [pushN]
  swap_code [pushData_congr hb]

/-- DUP runs the same on code with the same bytes. -/
private theorem dupN_swapsCode (n : Fin 16) :
    SwapsCode (dupN (fork := fork) (Meter := Meter) n) := by
  intro evm code jumps _ _
  simp only [dupN]
  swap_code

/-- SWAP runs the same on code with the same bytes. -/
private theorem swapN_swapsCode (n : Fin 16) :
    SwapsCode (swapN (fork := fork) (Meter := Meter) n) := by
  intro evm code jumps _ _
  simp only [swapN]
  swap_code

/-- DUPN reads the same immediate byte from code with the same bytes. -/
private theorem dupnStep_swapsCode : SwapsCode (dupnStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps hb _
  simp only [dupnStep]
  swap_code [immediateByte_congr hb]

/-- SWAPN reads the same immediate byte from code with the same bytes. -/
private theorem swapnStep_swapsCode : SwapsCode (swapnStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps hb _
  simp only [swapnStep]
  swap_code [immediateByte_congr hb]

/-- EXCHANGE reads the same immediate byte from code with the same bytes. -/
private theorem exchangeStep_swapsCode :
    SwapsCode (exchangeStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps hb _
  simp only [exchangeStep]
  swap_code [immediateByte_congr hb]

/-- Each instruction of the stack runs the same on code with the same bytes. -/
theorem stackOnlyStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some run) : SwapsCode run := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact unaryOp_swapsCode _ _
    | with_reducible exact binaryOp_swapsCode _ _
    | with_reducible exact ternaryOp_swapsCode _ _
    | with_reducible exact expStep_swapsCode
    | with_reducible exact keccak256Step_swapsCode
    | with_reducible exact popStep_swapsCode
    | with_reducible exact pushN_swapsCode _
    | with_reducible exact dupN_swapsCode _
    | with_reducible exact swapN_swapsCode _
    | with_reducible exact dupnStep_swapsCode
    | with_reducible exact swapnStep_swapsCode
    | with_reducible exact exchangeStep_swapsCode

end EthLib.Execution.Evm
