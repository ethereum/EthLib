module

public import EthLib.Execution.Proofs.Evm.Padding.Basic

/-!
# Proofs: the instructions of the frame run the same on code with the same bytes

JUMP and JUMPI read the flags of the destinations, and CODECOPY reads the bytes of the code.

CODESIZE reads the size of the code, which the bytes do not give, so it is left out.

The other instructions here read neither.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- STOP runs the same on code with the same bytes. -/
theorem stopStep_swapsCode : SwapsCode (stopStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps _ _
  rfl

omit [GasMeter Meter] in
/-- A pop runs the same on other code, which it keeps. -/
theorem popWord_withCode (evm : Evm fork Meter) (code : ByteArray) (jumps : Array Bool) :
    popWord { evm with code, validJumpDestinations := jumps } =
      (fun p => (p.1, { p.2 with code, validJumpDestinations := jumps })) <$> popWord evm := by
  simp only [popWord]
  cases evm.stack.pop <;> rfl

omit [GasMeter Meter] in
/-- The pops of the topics of a log run the same on other code, which they keep. -/
theorem popTopics_withCode (evm : Evm fork Meter) (code : ByteArray) (jumps : Array Bool)
    (n : Nat) :
    popTopics { evm with code, validJumpDestinations := jumps } n =
      (fun p => (p.1, { p.2 with code, validJumpDestinations := jumps })) <$> popTopics evm n := by
  induction n generalizing evm with
  | zero => rfl
  | succ k ih =>
    simp only [popTopics, popWord_withCode, bind_map_left, map_bind, ih]
    rfl

/-- JUMP reads the same flag from code with the same destinations. -/
private theorem jumpStep_swapsCode : SwapsCode (jumpStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps _ hj
  simp only [jumpStep]
  swap_code [hj]

/-- JUMPI reads the same flag from code with the same destinations. -/
private theorem jumpiStep_swapsCode : SwapsCode (jumpiStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps _ hj
  simp only [jumpiStep]
  swap_code [hj]

/-- JUMPDEST runs the same on code with the same bytes. -/
private theorem jumpdestStep_swapsCode :
    SwapsCode (jumpdestStep (fork := fork) (Meter := Meter)) := by
  intro evm code jumps _ _
  simp only [jumpdestStep]
  swap_code

/-- Each instruction of the control flow runs the same on code with the same bytes. -/
theorem controlFlowStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some run) : SwapsCode run := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  · exact stopStep_swapsCode
  · exact jumpStep_swapsCode
  · exact jumpiStep_swapsCode
  · intro evm code jumps _ _
    swap_code
  · intro evm code jumps _ _
    swap_code
  · exact jumpdestStep_swapsCode

/-- Each instruction of memory and data but CODESIZE runs the same on code with the same bytes. -/
theorem memoryDataStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some run) (hsize : op ≠ .codesize) : SwapsCode run := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  all_goals first
    | exact absurd rfl hsize
    | (intro evm code jumps hb _
       try simp only [mloadStep, mstoreStep, mstore8Step, mcopyStep, calldataloadStep,
         copyToMemory, returndatacopyStep]
       swap_code [bufferBytes_congr hb])

/-- RETURN and REVERT run the same on code with the same bytes. -/
theorem returnOpStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) : SwapsCode run := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  · subst hstep
    intro evm code jumps _ _
    simp only [returnStep]
    swap_code
  · split at hstep
    · cases hstep
      intro evm code jumps _ _
      simp only [revertStep]
      swap_code
    · cases hstep

/-- Each instruction of the environment runs the same on code with the same bytes. -/
theorem environmentStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some run) : SwapsCode run := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (intro evm code jumps _ _
       try simp only [blockhashStep, blobhashStep]
       swap_code)

/-- LOG0 to LOG4 run the same on code with the same bytes. -/
theorem logOpStep_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some run) : SwapsCode run := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  intro evm code jumps _ _
  simp only [logStep, popWord_withCode, popTopics_withCode, bind_map_left, map_bind]
  swap_code

end EthLib.Execution.Evm
