module

public import EthLib.Execution.Proofs.Evm.Logic.Message
public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.Evm.Gas.CallGas

/-!
# Proofs: a rule for CALL

CALL sends a message to the account at an address, which runs the code of that account.

The rule here covers CALL with no value, a range of input and a range of output.

Memory grows for both ranges, and the call pays that growth.

The message carries the bytes of the input range as its data.

It holds from Berlin to the fork before Glamsterdam, with one counter of gas.

The account must hold its code in the state, and from Pectra that code must be no delegation.

The depth of the frame must leave room for one more frame.

The call pays the access to the address: 2600 when cold and 100 when warm, by EIP-2929.

It passes on the gas it asks for, at most all but one 64th of the gas left after both, by EIP-150.

Sources: EIP-150, EIP-2929 and EIP-7702.

The callee runs arbitrary code, so the rule takes an assumption on the frame that ends the message.

The caller then pushes 1 when that frame ends with no error, and 0 otherwise.

It writes the start of the output of that frame at the start of the output range.

It writes as many bytes as both the output and the range hold, and leaves the rest of memory.

A rule for empty ranges follows, with no growth and no data.

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

/-- The step of CALL with no value sends a message to the address, with its input as data.

The caller has paid the access to the address, the growth of memory, and the gas it passes on.

It has recorded the access, and the reads of the address and of its own account.

Its memory has grown for both ranges, and the message runs the code of the address.

The caller keeps its output.

The message is static when the frame is. -/
theorem callStep_call (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ caller msg, callStep .call evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      caller.gas = evm.gas - ((messageCallGas fork 0 g.toNat evm.gas
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧ caller.output = evm.output ∧
      caller.state = (evm.state.recordAccountRead (toAddressMasked a)).recordAccountRead
        evm.message.currentTarget ∧
      caller.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } ∧
      msg.gas = (messageCallGas fork 0 g.toNat evm.gas
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))).subCall ∧
      msg.caller = evm.message.currentTarget ∧ msg.currentTarget = toAddressMasked a ∧
      msg.target = some (toAddressMasked a) ∧ msg.codeAddress = some (toAddressMasked a) ∧
      msg.code = calleeCode ∧
      msg.data = memoryReadBytes (memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
      msg.value = 0 ∧ msg.depth = evm.message.depth + 1 ∧
      msg.isStatic = evm.message.isStatic := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Base.Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Base.Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  simp only at hcode hgas hdepth ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas ⊢
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  have hmin : min g.toNat (maxMessageCallGas
      (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - cb)) + cb +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - cb) ≤
        gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - cb := Nat.sub_le _ _
    omega
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hcode, hdel', htw, hsd, Except.mapError,
    callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', Nat.not_lt.mpr hdepth, hgas,
    Nat.not_lt.mpr hmin]
  exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The step of STATICCALL sends a static message to the address, with its input as data.

The caller has paid the access to the address, the growth of memory, and the gas it passes on.

It has recorded the access, and the reads of the address and of its own account.

Its memory has grown for both ranges, and the message runs the code of the address.

The caller keeps its output.

The message carries no value, and it is static. -/
theorem callStep_staticcall (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ caller msg,
      callStep .staticcall evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      caller.gas = evm.gas - ((messageCallGas fork 0 g.toNat evm.gas
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧ caller.output = evm.output ∧
      caller.state = (evm.state.recordAccountRead (toAddressMasked a)).recordAccountRead
        evm.message.currentTarget ∧
      caller.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } ∧
      msg.gas = (messageCallGas fork 0 g.toNat evm.gas
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))).subCall ∧
      msg.caller = evm.message.currentTarget ∧ msg.currentTarget = toAddressMasked a ∧
      msg.target = some (toAddressMasked a) ∧ msg.codeAddress = some (toAddressMasked a) ∧
      msg.code = calleeCode ∧
      msg.data = memoryReadBytes (memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
      msg.value = 0 ∧ msg.depth = evm.message.depth + 1 ∧
      msg.isStatic = true := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Base.Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Base.Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  simp only at hcode hgas hdepth ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas ⊢
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  have hmin : min g.toNat (maxMessageCallGas
      (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - cb)) + cb +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - cb) ≤
        gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - cb := Nat.sub_le _ _
    omega
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hcode, hdel', htw, Except.mapError,
    callExtraGas, callNewAccountStateGas, callValueCost,
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', Nat.not_lt.mpr hdepth, hgas,
    Nat.not_lt.mpr hmin]
  exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The step of CALL with value sends a message with that value, with its input as data.

The frame may change the state, and the current account holds at least the value.

The caller has paid the extra price, the growth of memory, and the gas it passes on.

The extra price is the access of EIP-2929, 2600 when cold and 100 when warm, from Berlin.

It adds 9000 for the value, from Frontier.

It adds 25000 when the callee is dead, by EIP-161 from Spurious Dragon.

The message gets that gas and the stipend of 2300.

The caller keeps its output. -/
theorem callStep_value (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {evm : Evm fork Nat} {g a v i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hstatic : evm.message.isStatic = false)
    (hbal : v ≤ (evm.state.getAccount evm.message.currentTarget).balance)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ caller msg, callStep .call evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      caller.gas = evm.gas - ((messageCallGas fork v g.toNat evm.gas
          (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
          (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
            callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v)).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧ caller.output = evm.output ∧
      caller.state = (evm.state.recordAccountRead (toAddressMasked a)).recordAccountRead
        evm.message.currentTarget ∧
      caller.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } ∧
      msg.gas = (messageCallGas fork v g.toNat evm.gas
          (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
          (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
            callNewAccountCost fork evm.state (toAddressMasked a) v +
            callValueCost fork v)).subCall ∧
      msg.caller = evm.message.currentTarget ∧ msg.currentTarget = toAddressMasked a ∧
      msg.target = some (toAddressMasked a) ∧ msg.codeAddress = some (toAddressMasked a) ∧
      msg.code = calleeCode ∧
      msg.data = memoryReadBytes (memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
      msg.value = v ∧ msg.shouldTransferValue = true ∧ msg.depth = evm.message.depth + 1 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Base.Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Base.Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Base.Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hdepth hstatic hbal ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  generalize hE : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
    (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
  have hgas' : E + (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    rw [← hE]; simpa [callNewAccountCost, callValueCost, hv', hng, hsd] using hgas
  have hmin : min g.toNat (maxMessageCallGas
      (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E)) + E +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E) ≤
        gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E := Nat.sub_le _ _
    omega
  have hbal' : ¬(state.getAccount message.currentTarget).balance < v := by
    simpa [BitVec.lt_def, BitVec.le_def] using hbal
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
    callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost, hv',
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, Nat.not_lt.mpr hdepth, hstatic, hE,
    hgas', Nat.not_lt.mpr hmin, hbal']
  exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The step of CALL with more value than the current account holds sends no message.

The caller pays the extra price and the growth of memory.

It gets back the gas it would pass on, with the stipend of 2300.

It pushes 0, keeps its output, and its return data is empty. -/
theorem callStep_value_low (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {evm : Evm fork Nat} {g a v i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hstatic : evm.message.isStatic = false)
    (hbal : (evm.state.getAccount evm.message.currentTarget).balance < v)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hgas : (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      after.gas = evm.gas - ((messageCallGas fork v g.toNat evm.gas
          (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
          (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
            callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v)).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) +
        (messageCallGas fork v g.toNat evm.gas
          (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
          (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
            callNewAccountCost fork evm.state (toAddressMasked a) v +
            callValueCost fork v)).subCall ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.returnData = .empty ∧
      after.state = (evm.state.recordAccountRead (toAddressMasked a)).recordAccountRead
        evm.message.currentTarget ∧
      after.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Base.Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Base.Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Base.Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hstatic hbal ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  generalize hE : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
    (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
  have hgas' : E + (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    rw [← hE]; simpa [callNewAccountCost, callValueCost, hv', hng, hsd] using hgas
  have hmin : min g.toNat (maxMessageCallGas
      (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E)) + E +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E) ≤
        gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E := Nat.sub_le _ _
    omega
  have hlen : rest.length ≠ STACK_LIMIT := by simp at hl; omega
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
    callExtraGas, callNewAccountCost, callValueCost, hv',
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, hstatic, hE,
    hgas', Nat.not_lt.mpr hmin, hbal, skipCall, refillStateGas, GasMeter.refill, GasMeter.credit,
    pushWord, Stack.push, hlen, advance, Functor.map, Except.map]

/-- A caller with room on its stack resumes from every frame that ends its message.

It pushes 1 for a frame with no error and 0 otherwise, and gets back the gas of the frame.

It writes the start of the output of the frame at the start of its output range.

It writes as many bytes as both the output and the range hold.

The caller keeps its own output. -/
theorem resumeCall_eq {caller child : Evm fork Nat} {o osz : U256}
    (hlen : caller.stack.val.length < STACK_LIMIT) :
    ∃ after, resumeCall fork caller 0 o osz child = .ok after ∧
      after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.message = caller.message ∧ after.pc = caller.pc + 1 ∧
      after.stack.val = (if child.error.isNone then 1 else 0) :: caller.stack.val ∧
      after.memory = memoryWrite caller.memory o.toNat
        (child.output.extract 0 (min osz.toNat child.output.size)) ∧
      after.gas = caller.gas + child.gas ∧
      after.running = caller.running ∧ after.error = caller.error ∧ after.output = caller.output ∧
      after.state = (incorporateChild fork caller child).state ∧
      after.substate = (incorporateChild fork caller child).substate := by
  have hne : caller.stack.val.length ≠ STACK_LIMIT := Nat.ne_of_lt hlen
  unfold resumeCall incorporateChild
  split <;>
    simp [pushWord, Stack.push, bind, Except.bind, pure, Except.pure, advance, refillStateGas,
      GasMeter.refill, GasMeter.absorb, *]

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

/-- CALL with no value, to the address `to`, with a range of input and a range of output.

The callee runs the code of `to`, which the state holds, and is no delegation.

Memory grows for both ranges, and the message carries the bytes of the input range as its data.

The message is static when the frame is.

The rule holds for every frame that ends the message and meets the assumption.

The caller pushes 1 when the callee ends with no error, and 0 otherwise.

It writes the start of the output of the callee at the start of the output range.

It writes as many bytes as both the output and the range hold, and leaves the rest of memory.

It gets back the gas that the callee leaves, and its state and substate come from the callee.

The rule says nothing more of them, since the callee is arbitrary. -/
theorem callWith (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (if cold then 2600 else 100)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        msg.value = 0 ∧ msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (if cold then 2600 else 100)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  apply HoareUnder.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  have hcost := callBaseCost_of_berlin hfork hglam cold
  subst hm hg hs hss hcold hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, mt,
      mca, m4, md, m5, m6, m7⟩ :=
    callStep_call hfork hglam hst hcode hdel hdepth (by rw [hcost]; omega)
  refine ⟨hrun, caller, msg, resumeCall fork caller 0 outputStart outputSize, ?_, ?_⟩
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
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
      resumeCall_eq (child := child) (o := outputStart) (osz := outputSize) hlen
    refine .inl ⟨after, hres, caller, msg, child, hcallee, hchild, c10, c11, ?_, m2, m3, mt, mca,
      m4, md, m5, m6, m7, ?_⟩
    · rw [m1, hcost]
    · refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
        by rw [a5, c5], by rw [a6, c6], ?_, by rw [a8, c8, hrun], by rw [a9, c9, herr],
        by rw [ao, co, hout], a10, a11⟩
      rw [a7, c7, hcost]

/-- CALL with no value and empty ranges of input and output, to the address `to`.

The callee runs the code of `to`, which the state holds, and is no delegation.

The rule holds for every frame that ends the message and meets the assumption.

The caller pushes 1 when the callee ends with no error, and 0 otherwise.

It gets back the gas that the callee leaves, and its state and substate come from the callee.

The message is static when the frame is.

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
        msg.gas = (messageCallGas fork 0 asked.toNat gas 0 (if cold then 2600 else 100)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧ msg.data = .empty ∧ msg.value = 0 ∧
        msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (messageCallGas fork 0 asked.toNat gas 0 (if cold then 2600 else 100)).cost +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  have hext : extendMemory memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have h := callWith (callee := callee) (asked := asked) (inputSize := 0) (outputSize := 0)
    (rest := rest) hfork hglam hlt hbyte hcode hdel hdepth hcold (by rw [hext]; exact hgas)
  rw [hext] at h
  refine h.consequence (fun _ hp => hp) ?_
  rintro evm ⟨caller, msg, child, hc, hle, hst, hss, hmg, rest'⟩
  refine ⟨caller, msg, child, hc, hle, hst, hss, by simpa using hmg, ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, md, m6, m7, m8, hat⟩ := rest'
  refine ⟨m1, m2, m3, m4, m5, by simpa [memoryExtend_zero, memoryReadBytes] using md, m6, m7, m8,
    ?_⟩
  simpa [memoryExtend_zero, memoryWrite] using hat

/-- STATICCALL is no instruction of the frame alone: it sends a message. -/
theorem instruction_staticcall : instruction (Meter := Nat) fork .staticcall = none := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
    selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Byzantium, STATICCALL runs the step of a static call. -/
theorem messageInstruction_staticcall (hfork : .byzantium ≤ fork) :
    messageInstruction (Meter := Nat) fork .staticcall = some (callStep .staticcall) := by
  simp [messageInstruction, callInstruction, HOrElse.hOrElse, OrElse.orElse, Option.orElse, hfork]

/-- From Berlin to before Glamsterdam, STATICCALL to `to`, with a range of input and one of output.

The callee runs the code of `to`, which the state holds, and is no delegation.

Memory grows for both ranges, and the message carries the bytes of the input range as its data.

The message carries no value, and it is static.

The rule holds for every frame that ends the message and meets the assumption.

The caller pushes 1 when the callee ends with no error, and 0 otherwise.

It writes the start of the output of the callee at the start of the output range.

It writes as many bytes as both the output and the range hold, and leaves the rest of memory.

It gets back the gas that the callee leaves, and its state and substate come from the callee.

The rule says nothing more of them, since the callee is arbitrary. -/
theorem staticcallWith (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (if cold then 2600 else 100)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        msg.value = 0 ∧ msg.depth = message.depth + 1 ∧ msg.isStatic = true ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (if cold then 2600 else 100)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  apply HoareUnder.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  have hcost := callBaseCost_of_berlin hfork hglam cold
  subst hm hg hs hss hcold hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, mt,
      mca, m4, md, m5, m6, m7⟩ :=
    callStep_staticcall hfork hglam hst hcode hdel hdepth (by rw [hcost]; omega)
  refine ⟨hrun, caller, msg, resumeCall fork caller 0 outputStart outputSize, ?_, ?_⟩
  · have hin : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
    have hdec : Op.ofByte fork evm.code[evm.pc] = some .staticcall := by
      simp only [hc, hpc, hbyte]
      exact ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)
    rw [step_of_messageInstruction hin hdec instruction_staticcall
      (messageInstruction_staticcall (Nat.le_trans (by decide) hfork))]
    exact hstep
  · intro child hchild hcallee
    have hlen : caller.stack.val.length < STACK_LIMIT := by
      have := evm.stack.property
      rw [hst] at this
      rw [c5]
      simp at this
      omega
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
      resumeCall_eq (child := child) (o := outputStart) (osz := outputSize) hlen
    refine .inl ⟨after, hres, caller, msg, child, hcallee, hchild, c10, c11, ?_, m2, m3, mt, mca,
      m4, md, m5, m6, m7, ?_⟩
    · rw [m1, hcost]
    · refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
        by rw [a5, c5], by rw [a6, c6], ?_, by rw [a8, c8, hrun], by rw [a9, c9, herr],
        by rw [ao, co, hout], a10, a11⟩
      rw [a7, c7, hcost]

/-- From Berlin to before Glamsterdam, STATICCALL with empty ranges of input and output, to `to`.

The callee runs the code of `to`, which the state holds, and is no delegation.

The message carries no value, and it is static.

The rule holds for every frame that ends the message and meets the assumption.

The caller pushes 1 when the callee ends with no error, and 0 otherwise.

It gets back the gas that the callee leaves, and its state and substate come from the callee.

The rule says nothing more of them, since the callee is arbitrary. -/
theorem staticcall (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart outputStart : U256} {rest : List U256} {cold : Bool}
    {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) ≤ gas) :
    HoareUnder fork callee
      (At code message pc (asked :: to :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas 0 (if cold then 2600 else 100)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧ msg.data = .empty ∧ msg.value = 0 ∧
        msg.depth = message.depth + 1 ∧ msg.isStatic = true ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (messageCallGas fork 0 asked.toNat gas 0 (if cold then 2600 else 100)).cost +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  have hext : extendMemory memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have h := staticcallWith (callee := callee) (asked := asked) (inputSize := 0) (outputSize := 0)
    (rest := rest) hfork hglam hlt hbyte hcode hdel hdepth hcold (by rw [hext]; exact hgas)
  rw [hext] at h
  refine h.consequence (fun _ hp => hp) ?_
  rintro evm ⟨caller, msg, child, hc, hle, hst, hss, hmg, rest'⟩
  refine ⟨caller, msg, child, hc, hle, hst, hss, by simpa using hmg, ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, md, m6, m7, m8, hat⟩ := rest'
  refine ⟨m1, m2, m3, m4, m5, by simpa [memoryExtend_zero, memoryReadBytes] using md, m6, m7, m8,
    ?_⟩
  simpa [memoryExtend_zero, memoryWrite] using hat

/-- CALL with a value `v`, which is not 0, to the address `to`, with ranges of input and output.

The frame may change the state, and the current account holds at least `v`.

The call pays its extra price and the growth of memory.

Its extra price is the access of EIP-2929, 2600 when cold and 100 when warm, from Berlin.

It adds 9000 for the value, from Frontier.

It adds 25000 when the callee is dead, by EIP-161 from Spurious Dragon.

It passes on the gas it asks for, at most all but one 64th of the gas left, by EIP-150.

The message gets that gas and the stipend of 2300, and carries the value.

The rule holds for every frame that ends the message and meets the assumption.

It says nothing of the state beyond what that frame gives, as for CALL with no value. -/
theorem callValue (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to v inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hv : v ≠ 0) (hstatic : message.isStatic = false)
    (hbal : v ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold +
            callNewAccountCost fork state (toAddressMasked to) v + callValueCost fork v) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: v :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountCost fork state (toAddressMasked to) v +
              callValueCost fork v)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        msg.value = v ∧ msg.shouldTransferValue = true ∧ msg.depth = message.depth + 1 ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountCost fork state (toAddressMasked to) v +
              callValueCost fork v)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  apply HoareUnder.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hm hg hs hss hcold hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, mt,
      mca, m4, md, m5, m6, m7⟩ :=
    callStep_value hfork hglam hst hv hstatic hbal hcode hdel hdepth hgas
  refine ⟨hrun, caller, msg, resumeCall fork caller 0 outputStart outputSize, ?_, ?_⟩
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
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
      resumeCall_eq (child := child) (o := outputStart) (osz := outputSize) hlen
    refine .inl ⟨after, hres, caller, msg, child, hcallee, hchild, c10, c11, m1, m2, m3, mt, mca,
      m4, md, m5, m6, m7, ?_⟩
    exact ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
      by rw [a5, c5], by rw [a6, c6], by rw [a7, c7], by rw [a8, c8, hrun], by rw [a9, c9, herr],
      by rw [ao, co, hout], a10, a11⟩

/-- CALL with more value than the current account holds sends no message, and pushes 0.

The frame may change the state, and the call pays as with enough value.

It gets back the gas that it would pass on, with the stipend of 2300.

Its memory has grown for both ranges.

The rule does not state the return data; the step lemma above states that it is empty. -/
theorem callValueLow (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to v inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hv : v ≠ 0) (hstatic : message.isStatic = false)
    (hbal : (state.getAccount message.currentTarget).balance < v)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold +
            callNewAccountCost fork state (toAddressMasked to) v + callValueCost fork v) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    Hoare fork
      (At code message pc
        (asked :: to :: v :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate)
      (At code message (pc + 1) (0 :: rest)
        (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
        (gas - ((messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountCost fork state (toAddressMasked to) v +
              callValueCost fork v)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          (messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountCost fork state (toAddressMasked to) v +
              callValueCost fork v)).subCall)
        ((state.recordAccountRead (toAddressMasked to)).recordAccountRead message.currentTarget)
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) }) := by
  apply Triple.of_step
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hm hg hs hss hcold hmem
  obtain ⟨after, hstep, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, -, a10, a11⟩ :=
    callStep_value_low hfork hglam hst hv hstatic hbal hcode hdel hgas
  refine ⟨after, .next hrun ?_, by rw [a1, hc], by rw [a2, hj], a3, by rw [a4, hpc], a5, a6, a7,
    by rw [a8, hrun], by rw [a9, herr], by rw [ao, hout], a10, a11⟩
  rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
    (by simp only [hc, hpc, hbyte]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _))
    instruction_call messageInstruction_call]
  exact hstep

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
  unfold startState at h
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
