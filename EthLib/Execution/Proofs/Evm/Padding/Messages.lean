module

public import EthLib.Execution.Proofs.Evm.Padding.Basic

/-!
# Proofs: the calls and the creations run the same on code with the same bytes

The caller and each frame that resumes from it get the other code.

The message runs its own code, so it is the same.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- An access to an address keeps other code. -/
private theorem accessAddress_withCode (evm : Evm fork Meter) (code : ByteArray)
    (jumps : Array Bool) (address : Address) :
    accessAddress { evm with code, validJumpDestinations := jumps } address =
      ((accessAddress evm address).1,
        { (accessAddress evm address).2 with code, validJumpDestinations := jumps }) := by
  unfold accessAddress
  split <;> rfl

omit [GasMeter Meter] in
/-- A read of an account keeps other code. -/
private theorem recordAccountRead_withCode (evm : Evm fork Meter) (code : ByteArray)
    (jumps : Array Bool) (address : Address) :
    recordAccountRead { evm with code, validJumpDestinations := jumps } address =
      { recordAccountRead evm address with code, validJumpDestinations := jumps } :=
  rfl

omit [GasMeter Meter] in
/-- The pops of the operands of a call run the same on other code, which they keep. -/
private theorem popCallOperands_withCode (evm : Evm fork Meter) (code : ByteArray)
    (jumps : Array Bool) (kind : CallKind) :
    popCallOperands kind { evm with code, validJumpDestinations := jumps } =
      (fun p => (p.1, { p.2 with code, validJumpDestinations := jumps })) <$>
        popCallOperands kind evm := by
  simp only [popCallOperands, popCallValue]
  swap_code

/-- The access to a delegate runs the same on other code, which it keeps. -/
private theorem accessDelegation_withCode (evm : Evm fork Meter) (code : ByteArray)
    (jumps : Array Bool) (address : Address) (known : Nat) :
    accessDelegation { evm with code, validJumpDestinations := jumps } address known =
      (fun p => (p.1, { p.2 with code, validJumpDestinations := jumps })) <$>
        accessDelegation evm address known := by
  simp only [accessDelegation, accountCode]
  swap_code

/-- The payment of a call runs the same on other code, which it keeps. -/
private theorem payCall_withCode (evm : Evm fork Meter) (code : ByteArray) (jumps : Array Bool)
    (kind : CallKind) (call : CallOperands) (memoryCost extraGas newAccount : Nat) :
    payCall kind call memoryCost extraGas newAccount
        { evm with code, validJumpDestinations := jumps } =
      (fun p => (p.1, { p.2 with code, validJumpDestinations := jumps })) <$>
        payCall kind call memoryCost extraGas newAccount evm := by
  simp only [payCall]
  swap_code

/-- The end of a call runs the same on other code, which it keeps. -/
private theorem finishCall_withCode (evm : Evm fork Meter) (code : ByteArray)
    (jumps : Array Bool) (kind : CallKind) (call : CallOperands) (callee : Callee)
    (subCall newAccount expandBy : Nat) :
    finishCall kind call callee subCall newAccount expandBy
        { evm with code, validJumpDestinations := jumps } =
      StepResult.withCode code jumps <$>
        finishCall kind call callee subCall newAccount expandBy evm := by
  simp only [finishCall, callerFrame, genericCall, skipCall, callMessage]
  swap_code

/-- Each call runs the same on code with the same bytes. -/
private theorem callStep_swapsCode (kind : CallKind) :
    SwapsCodeChild (callStep (fork := fork) (Meter := Meter) kind) := by
  intro evm code jumps _ _
  simp only [callStep, popCallOperands_withCode, bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  simp only [accessAddress_withCode, recordAccountRead_withCode]
  split
  · rfl
  · simp only [checkGas, accessDelegation_withCode, payCall_withCode, map_bind, bind_map_left]
    refine bind_congr fun _ => ?_
    refine keepReads_map ?_ fun _ => rfl
    simp only [map_bind]
    refine bind_congr fun _ => ?_
    refine keepReads_map ?_ fun _ => rfl
    simp only [map_bind]
    refine bind_congr fun _ => ?_
    exact finishCall_withCode ..

/-- Each creation runs the same on code with the same bytes. -/
private theorem createStep_swapsCode (create2 : Bool) :
    SwapsCodeChild (createStep (fork := fork) (Meter := Meter) create2) := by
  intro evm code jumps _ _
  simp only [createStep, popSalt, genericCreate, launchCreate, skipCall]
  swap_code

/-- Each call and each creation runs the same on code with the same bytes. -/
theorem messageInstruction_swapsCode {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hstep : messageInstruction fork op = some run) : SwapsCodeChild run := by
  unfold messageInstruction at hstep
  rcases orElse_eq_some hstep with hstep | hstep
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hstep
    all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep)
    all_goals first
      | (subst hstep; exact callStep_swapsCode _)
      | cases hstep
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hstep
    all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep)
    all_goals first
      | (subst hstep; exact createStep_swapsCode _)
      | cases hstep

end EthLib.Execution.Evm
