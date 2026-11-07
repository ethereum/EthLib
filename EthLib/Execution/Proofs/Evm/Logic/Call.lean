module

public import EthLib.Execution.Proofs.Evm.Logic.Message
public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Call.Instructions

/-!
# Proofs: a rule for CALL

CALL sends a message to the account at an address, which runs the code of that account.

The rule here covers CALL with no value, an empty input and an empty range of output.

It holds from Berlin to the fork before Glamsterdam, with one counter of gas.

The account must hold its code in the state, and from Pectra that code must be no delegation.

The depth of the frame must leave room for one more frame.

The call pays the access to the address: 2600 when cold and 100 when warm, by EIP-2929.

It passes on the gas it asks for, at most all but one 64th of the gas left after that, by EIP-150.

Sources: EIP-150, EIP-2929 and EIP-7702.

The callee runs arbitrary code, so the rule takes an assumption on the frame that ends the message.

The caller then pushes 1 when that frame ends with no error, and 0 otherwise.

It gets back the gas that the frame leaves, and its state and substate are those of the frame.

The callee may even call the caller again.

So the rule says nothing more about the state after the call.

The runner of the interpreter meets one assumption beyond the trivial one.

A message with no code, to an account that is no precompile, ends with no error.

Out of scope: CREATE, a call with value, DELEGATECALL, STATICCALL, and a call out of gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 toAddressMasked)
open GasCosts

variable {fork : Fork}

/-- The step of CALL with no value and empty ranges sends a message to the address.

The caller has paid the access to the address and the gas it passes on.

It has recorded the access, and the reads of the address and of its own account.

The message runs the code of the address, with no value and no data. -/
theorem callStep_call_of_empty (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {evm : Evm fork Nat} {g a i o : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: 0 :: i :: 0 :: o :: 0 :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) ≤
      evm.gas) :
    ∃ caller msg, callStep .call evm = .ok (.child caller msg (resumeCall fork caller 0 o 0)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = evm.memory ∧
      caller.gas = evm.gas - (min g.toNat (maxMessageCallGas (evm.gas -
        callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))) +
        callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses))) ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧
      caller.state = (evm.state.recordAccountRead (toAddressMasked a)).recordAccountRead
        evm.message.currentTarget ∧
      caller.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } ∧
      msg.gas = min g.toNat (maxMessageCallGas (evm.gas -
        callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))) ∧
      msg.caller = evm.message.currentTarget ∧ msg.currentTarget = toAddressMasked a ∧
      msg.target = some (toAddressMasked a) ∧ msg.codeAddress = some (toAddressMasked a) ∧
      msg.code = calleeCode ∧ msg.data = .empty ∧ msg.value = 0 ∧
      msg.depth = evm.message.depth + 1 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Base.Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Base.Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  simp only at hcode hgas hdepth
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have hgas' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) ≤
      gas := by simpa using hgas
  have hmin : min g.toNat (maxMessageCallGas
      (gas - callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)))) +
      callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) ≤ gas := by
    have : maxMessageCallGas
        (gas - callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses))) ≤
        gas - callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) :=
      Nat.sub_le _ _
    omega
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hcode, hdel', htw, hsd, Except.mapError,
    extendMemory, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hgas', Nat.not_lt.mpr hmin,
    Nat.not_lt.mpr hdepth, memoryExtend_zero, memoryReadBytes]
  exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A caller with room on its stack resumes from every frame that ends its message.

It pushes 1 for a frame with no error and 0 otherwise, and gets back the gas of the frame. -/
theorem resumeCall_of_empty {caller child : Evm fork Nat} {o : U256}
    (hlen : caller.stack.val.length < STACK_LIMIT) :
    ∃ after, resumeCall fork caller 0 o 0 child = .ok after ∧
      after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.message = caller.message ∧ after.pc = caller.pc + 1 ∧
      after.stack.val = (if child.error.isNone then 1 else 0) :: caller.stack.val ∧
      after.memory = caller.memory ∧ after.gas = caller.gas + child.gas ∧
      after.running = caller.running ∧ after.error = caller.error ∧
      after.state = (incorporateChild fork caller child).state ∧
      after.substate = (incorporateChild fork caller child).substate := by
  have hne : caller.stack.val.length ≠ STACK_LIMIT := Nat.ne_of_lt hlen
  unfold resumeCall incorporateChild
  split <;>
    simp [pushWord, Stack.push, bind, Except.bind, pure, Except.pure, advance, refillStateGas,
      GasMeter.refill, GasMeter.absorb, memoryWrite, *]

/-- From Berlin to before Glamsterdam, a call pays 2600 for a cold address, 100 for a warm one. -/
theorem callBaseCost_of_berlin (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (cold : Bool) : callBaseCost fork cold = if cold then 2600 else 100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [callBaseCost, hfork, accountAccessCost, gasSchedule, hng, WARM_ACCESS]

/-- CALL is no instruction of the frame alone: it sends a message. -/
theorem instruction_call : instruction (Meter := Nat) fork .call = none := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
    selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- CALL runs the step of a call. -/
theorem messageInstruction_call :
    messageInstruction (Meter := Nat) fork .call = some (callStep .call) := by
  simp [messageInstruction, callInstruction, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate}

/-- The gas that CALL passes on: what it asks for, at most all but one 64th of what is left. -/
def callGas (asked : U256) (gas cost : Nat) : Nat :=
  min asked.toNat (maxMessageCallGas (gas - cost))

/-- CALL with no value and empty ranges of input and output, to the address `to`.

The callee runs the code of `to`, which the state holds, and is no delegation.

The rule holds for every frame that ends the message and meets the assumption.

The caller pushes 1 when the callee ends with no error, and 0 otherwise.

It gets back the gas that the callee leaves, and its state and substate come from the callee.

The rule says nothing more of them, since the callee is arbitrary. -/
theorem call (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart outputStart : U256} {rest : List U256} {cold : Bool}
    {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) ≤ gas) :
    HoareUnder fork callee
      (At code message pc (asked :: to :: 0 :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = callGas asked gas (if cold then 2600 else 100) ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧ msg.data = .empty ∧ msg.value = 0 ∧
        msg.depth = message.depth + 1 ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (callGas asked gas (if cold then 2600 else 100) + if cold then 2600 else 100) +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  apply HoareUnder.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  have hcost := callBaseCost_of_berlin hfork hglam cold
  subst hm hg hs hss hcold
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, m1, m2, m3, mt, mca, m4,
      m5, m6, m7⟩ :=
    callStep_call_of_empty hfork hglam hst hcode hdel hdepth (by rw [hcost]; exact hgas)
  refine ⟨hrun, caller, msg, resumeCall fork caller 0 outputStart 0, ?_, ?_⟩
  · rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
      (by simp only [hc, hpc, hbyte]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _))
      instruction_call messageInstruction_call]
    exact hstep
  · intro child hchild hcallee
    have hlen : caller.stack.val.length < STACK_LIMIT := by
      have := evm.stack.property
      rw [hst] at this
      rw [c5]
      simp at this
      omega
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
      resumeCall_of_empty (child := child) (o := outputStart) hlen
    refine .inl ⟨after, hres, caller, msg, child, hcallee, hchild, c10, c11, ?_, m2, m3, mt, mca,
      m4, m5, m6, m7, ?_⟩
    · rw [m1, hcost]
      rfl
    · refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
        by rw [a5, c5], by rw [a6, c6, hmem], ?_, by rw [a8, c8, hrun], by rw [a9, c9, herr],
        a10, a11⟩
      rw [a7, c7, hcost]
      rfl

/-- The assumption that a call that runs no code, and reaches no precompile, ends with no error. -/
def NoCodeSucceeds {Meter : Type} [GasMeter Meter] (_caller : Evm fork Meter)
    (message : Message fork) (child : Evm fork Meter) : Prop :=
  message.code = .empty → message.target.isSome = true → precompileAddress fork message = none →
    child.error = none

/-- A running frame past the end of its code stops at once, with no error when it had none. -/
theorem error_runFrame_of_code_le {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {bound : Nat} {runChild : MessageRunner fork Meter bound} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (hsize : evm.code.size ≤ evm.pc)
    (running : evm.running = true) (herr : evm.error = none)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.error = none := by
  have hs : step fork evm = .ok (.next (advance { evm with running := false })) := by
    unfold step
    simp only [Nat.not_lt.mpr hsize, dite_false]
    rfl
  rw [runFrame_of_step_eq_next running hs, runFrame_of_running_eq_false rfl] at h
  cases h
  simpa [advance] using herr

/-- A message with no code, to an account that is no precompile, ends with no error.

That holds whenever the interpreter returns a frame for it. -/
theorem error_processMessage_of_empty {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hcode : message.code = .empty) (hpre : precompileAddress fork message = none)
    (h : processMessage fork message state substate = .ok ended) : ended.val.error = none := by
  rw [processMessage] at h
  obtain ⟨ended0, hdo, rfl⟩ := Base.map_ok_iff.mp h
  split at hdo <;> (dsimp only at hdo; split at hdo)
  all_goals
    obtain ⟨state1, -, hdo⟩ := Base.bind_ok_iff.mp hdo
    simp only [hpre] at hdo
    split at hdo
    · cases hdo
    · rename_i after hrun
      cases hdo
      have hnone := error_runFrame_of_code_le (by simp [startFrame, hcode]) rfl rfl hrun
      simp [rollbackOnError, hnone]

/-- The runner of the interpreter meets the assumption that a call to no code ends with no error.

It runs a call or a creation, as the code of a message runs them, for every bound on their gas. -/
theorem meets_process_noCode {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] (fork : Fork)
    (bound : Nat) :
    Meets (bound := bound) (NoCodeSucceeds (fork := fork) (Meter := Meter))
      fun (caller : Evm fork Meter) message _ =>
        match message.target with
        | some _ => processMessage fork message caller.state caller.substate.child
        | none => processCreateMessage fork message caller.state caller.substate.child := by
  refine ⟨fun caller message _ child h hcode htarget hpre => ?_, (meets_process fork bound).aborts⟩
  split at h
  · exact error_processMessage_of_empty hcode hpre h
  · rename_i hnone
    simp [hnone] at htarget

end EthLib.Execution.Evm.Logic
