module

public import EthLib.Execution.Proofs.Evm.Logic.Route

/-!
# Proofs: rules for the calls

CALL sends a message to the account at an address, which runs the code of that account.

The rules hold at every fork from Berlin, and count gas with one counter.

From Glamsterdam, that counter also pays the state gas of a new account.

From Glamsterdam the protocol counts gas with the meter of EIP-8037.

These rules do not yet carry to that meter.

Sources: EIP-150, EIP-161, EIP-2929, EIP-7702, EIP-8037 and EIP-8038.

Out of scope: CREATE, CALLCODE with value, and a call out of gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 toAddressMasked)
open GasCosts

variable {fork : Fork}

/-- The step of a call that sends no value of its own sends a message, with its input as data. -/
theorem callStep_child (hfork : .berlin ≤ fork) {kind : CallKind}
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    -- CALL and CALLCODE pop a value, here 0, and DELEGATECALL and STATICCALL pop none.
    (hst : evm.stack.val =
      g :: a :: ((if kind.sendsValue then [0] else []) ++ i :: isz :: o :: osz :: rest))
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    -- The frame pops the operands.
    ∃ stack : Stack, stack.val = rest ∧
      let growth := extendMemory evm.memory.size [(i, isz), (o, osz)]
      let accessed := evm.substate.accessedAddresses.insert (toAddressMasked a)
      let callGas := messageCallGas fork 0 g.toNat evm.gas growth.cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))
      -- The calling frame and the message are those that every call builds after the payment.
      let caller := callerFrame
        { evm with
          stack
          -- The frame pays the access and the growth of memory for both ranges.
          --
          -- It also pays the gas that it passes on.
          gas := evm.gas - (callGas.cost + growth.cost)
          -- It accesses the address and records its read.
          state := evm.state.recordAccountRead (toAddressMasked a)
          substate := { evm.substate with accessedAddresses := accessed } }
        growth.expandBy
      callStep kind evm = .ok (.child caller
        -- The message runs the code of the address, and gets no reservoir.
        (callMessage kind ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩
          ⟨toAddressMasked a, calleeCode, false, 0⟩ callGas.subCall 0 caller)
        (resumeCall fork caller 0 o osz)) := by
  obtain ⟨stack, hstack, h⟩ := callStep_child_of_routes (route := none) hfork hst hcode hdel hdepth
    (by simpa only [routeCost, Nat.add_zero] using hgas)
  exact ⟨stack, hstack, h⟩

/-- The step of CALL with no value sends a message to the address, with its input as data. -/
theorem callStep_call (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    -- The frame pops the operands.
    ∃ stack : Stack, stack.val = rest ∧
      let growth := extendMemory evm.memory.size [(i, isz), (o, osz)]
      let accessed := evm.substate.accessedAddresses.insert (toAddressMasked a)
      let callGas := messageCallGas fork 0 g.toNat evm.gas growth.cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))
      -- The calling frame and the message are those that every call builds after the payment.
      let caller := callerFrame
        { evm with
          stack
          -- The frame pays the access and the growth of memory for both ranges.
          --
          -- It also pays the gas that it passes on.
          gas := evm.gas - (callGas.cost + growth.cost)
          -- It accesses the address and records its read.
          state := evm.state.recordAccountRead (toAddressMasked a)
          substate := { evm.substate with accessedAddresses := accessed } }
        growth.expandBy
      callStep .call evm = .ok (.child caller
        -- The message runs the code of the address, and gets no reservoir.
        (callMessage .call ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩
          ⟨toAddressMasked a, calleeCode, false, 0⟩ callGas.subCall 0 caller)
        (resumeCall fork caller 0 o osz)) :=
  callStep_child (kind := .call) hfork hst hcode hdel hdepth hgas

/-- The step of STATICCALL sends a static message to the address, with its input as data. -/
theorem callStep_staticcall (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    -- The frame pops the operands.
    ∃ stack : Stack, stack.val = rest ∧
      let growth := extendMemory evm.memory.size [(i, isz), (o, osz)]
      let accessed := evm.substate.accessedAddresses.insert (toAddressMasked a)
      let callGas := messageCallGas fork 0 g.toNat evm.gas growth.cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)))
      -- The calling frame and the message are those that every call builds after the payment.
      let caller := callerFrame
        { evm with
          stack
          -- The frame pays the access and the growth of memory for both ranges.
          --
          -- It also pays the gas that it passes on.
          gas := evm.gas - (callGas.cost + growth.cost)
          -- It accesses the address and records its read.
          state := evm.state.recordAccountRead (toAddressMasked a)
          substate := { evm.substate with accessedAddresses := accessed } }
        growth.expandBy
      callStep .staticcall evm = .ok (.child caller
        -- The message runs the code of the address, and gets no reservoir.
        (callMessage .staticcall ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩
          ⟨toAddressMasked a, calleeCode, false, 0⟩ callGas.subCall 0 caller)
        (resumeCall fork caller 0 o osz)) :=
  callStep_child (kind := .staticcall) hfork hst hcode hdel hdepth hgas

/-- One counter refills no state gas, so the caller resumes the same, whatever that state gas.

From Glamsterdam, EIP-8037 refills it; one counter does not model that. -/
theorem resumeCall_newAccount (caller : Evm fork Nat) (newAccount : Nat) (o osz : U256) :
    resumeCall fork caller newAccount o osz = resumeCall fork caller 0 o osz := by
  funext child
  simp only [resumeCall, refillStateGas, GasMeter.refill]

/-- The price that CALL with a value `v` pays for the account of `to`, with one counter of gas.

Before Glamsterdam, from Spurious Dragon, it is 25000 when `v` is not 0 and `to` is dead (EIP-161).

From Glamsterdam, it is the state gas of a new account under the same condition, by EIP-8037.

The step pays the two prices apart; this is the sum that one counter pays. -/
abbrev callNewAccountGas (fork : Fork) (state : State.TransactionState) (to : Base.Address)
    (v : U256) : Nat :=
  callNewAccountCost fork state to v +
    callNewAccountStateGas fork .call state ⟨0, to, v, 0, 0, 0, 0⟩

/-- Before Glamsterdam, CALL pays for a new account in execution gas only. -/
theorem callNewAccountGas_of_lt (hglam : fork < .glamsterdam) (state : State.TransactionState)
    (to : Base.Address) (v : U256) :
    callNewAccountGas fork state to v = callNewAccountCost fork state to v := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [callNewAccountGas, callNewAccountStateGas, hng]

/-- The step of CALL with value sends a message with that value, with its input as data. -/
theorem callStep_value (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a v i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    -- The frame may change the state, and the current account holds at least the value.
    (hstatic : evm.message.isStatic = false)
    (hbal : v ≤ (evm.state.getAccount evm.message.currentTarget).balance)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    -- The extra price is the access of EIP-2929, 2600 when cold and 100 when warm, from Berlin.
    --
    -- From Glamsterdam, a cold access costs 3000, by EIP-8038.
    --
    -- It adds 9000 for the value, from Frontier, and 11300 from Glamsterdam, by EIP-8038.
    --
    -- It adds 25000 when the callee is dead, by EIP-161 from Spurious Dragon.
    --
    -- From Glamsterdam, it adds the state gas of that new account instead, by EIP-8037.
    (hgas : (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountGas fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    -- The frame pops the operands.
    ∃ stack : Stack, stack.val = rest ∧
      let growth := extendMemory evm.memory.size [(i, isz), (o, osz)]
      let accessed := evm.substate.accessedAddresses.insert (toAddressMasked a)
      let callGas := messageCallGas fork v g.toNat evm.gas growth.cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountGas fork evm.state (toAddressMasked a) v + callValueCost fork v)
      -- The calling frame and the message are those that every call builds after the payment.
      let caller := callerFrame
        { evm with
          stack
          -- The frame pays the extra price and the growth of memory for both ranges.
          --
          -- It also pays the gas that it passes on.
          gas := evm.gas - (callGas.cost + growth.cost)
          -- It accesses the address and records its read.
          state := evm.state.recordAccountRead (toAddressMasked a)
          substate := { evm.substate with accessedAddresses := accessed } }
        growth.expandBy
      callStep .call evm = .ok (.child caller
        -- The message gets the gas it passes on, which adds the stipend of 2300, and no reservoir.
        (callMessage .call ⟨g, toAddressMasked a, v, i, isz, o, osz⟩
          ⟨toAddressMasked a, calleeCode, false, 0⟩ callGas.subCall 0 caller)
        (resumeCall fork caller 0 o osz)) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  simp only at hcode hgas hdepth hstatic hbal ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  have hbal' : ¬(state.getAccount message.currentTarget).balance < v := by
    simpa [BitVec.lt_def, BitVec.le_def] using hbal
  by_cases hng : fork ≥ .glamsterdam
  · have hC : callValueCost fork v = ACCOUNT_WRITE + CALL_STIPEND := by
      simp [callValueCost, hv', hng]
    generalize hB : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = B
    generalize hN : (if state.isAccountAlive (toAddressMasked a) = false then NEW_ACCOUNT_STATE_GAS
      else 0) = N
    generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M
    have hgas' : B + N + (ACCOUNT_WRITE + CALL_STIPEND) + M ≤ gas := by
      rw [← hB, ← hN, ← hM]
      simpa [callNewAccountGas, callNewAccountCost, callNewAccountStateGas, hC, hv', hng] using hgas
    have h1 : ¬gas < B + (ACCOUNT_WRITE + CALL_STIPEND) + M := by omega
    have h2 : ¬gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) < N := by omega
    have h3 : ¬gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N < min g.toNat
        (maxMessageCallGas (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)) := by
      have := maxMessageCallGas_le (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)
      omega
    have hL : gas - M - (B + N + (ACCOUNT_WRITE + CALL_STIPEND)) =
        gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N := by
      omega
    have hG : gas - (min g.toNat
          (maxMessageCallGas (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)) +
        (B + N + (ACCOUNT_WRITE + CALL_STIPEND)) + M) =
        gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N - min g.toNat
          (maxMessageCallGas (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)) := by
      omega
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
      accountCode, recordAccountRead, hcode, hdel', htw, Except.mapError,
      callExtraGas, callNewAccountGas, callNewAccountCost, callNewAccountStateGas, hC, hv',
      payCall, messageCallGas, chargeGas, chargeStateGas, GasMeter.charge, GasMeter.chargeState,
      finishCall, genericCall, keepReads, GasMeter.gasLeft, GasMeter.reservoir,
      Nat.not_lt.mpr hdepth, hstatic, hbal', hB, hN, hM, h1, h2, h3, hgas', hL, hG,
      resumeCall_newAccount]
    simp at hl
    omega
  · simp only [callNewAccountGas_of_lt (Nat.lt_of_not_le hng)] at hgas ⊢
    have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
    generalize hE : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
      (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
    have hgas' : E + (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
      rw [← hE]
      simpa [callNewAccountCost, callValueCost, hv', hng, hsd] using hgas
    have hmin : min g.toNat (maxMessageCallGas
        (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E)) + E +
        (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
      have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E) ≤
          gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E := Nat.sub_le _ _
      omega
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
      accountCode, recordAccountRead, hcode, hdel', htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost, hv',
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.reservoir, Nat.not_lt.mpr hdepth, hstatic, hE,
      hgas', Nat.not_lt.mpr hmin, hbal']
    simp at hl
    omega

/-- The step of CALL with more value than the current account holds sends no message.

The caller pays the extra price and the growth of memory.

It gets back the gas it would pass on, with the stipend of 2300.

From Glamsterdam, one counter does not give back the state gas of a new account, unlike EIP-8037.

It pushes 0, keeps its output, and its return data is empty. -/
theorem callStep_value_low (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a v i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hstatic : evm.message.isStatic = false)
    (hbal : (evm.state.getAccount evm.message.currentTarget).balance < v)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hgas : (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountGas fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      after.gas = evm.gas - ((messageCallGas fork v g.toNat evm.gas
          (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
          (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
            callNewAccountGas fork evm.state (toAddressMasked a) v + callValueCost fork v)).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) +
        (messageCallGas fork v g.toNat evm.gas
          (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
          (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
            callNewAccountGas fork evm.state (toAddressMasked a) v +
            callValueCost fork v)).subCall ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.returnData = .empty ∧
      after.state = (evm.state.recordAccountRead (toAddressMasked a)).recordAccountRead
        evm.message.currentTarget ∧
      after.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  simp only at hcode hgas hstatic hbal ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  have hlen : rest.length ≠ STACK_LIMIT := by simp at hl; omega
  by_cases hng : fork ≥ .glamsterdam
  · have hC : callValueCost fork v = ACCOUNT_WRITE + CALL_STIPEND := by
      simp [callValueCost, hv', hng]
    generalize hB : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = B
    generalize hN : (if state.isAccountAlive (toAddressMasked a) = false then NEW_ACCOUNT_STATE_GAS
      else 0) = N
    generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M
    have hgas' : B + N + (ACCOUNT_WRITE + CALL_STIPEND) + M ≤ gas := by
      rw [← hB, ← hN, ← hM]
      simpa [callNewAccountGas, callNewAccountCost, callNewAccountStateGas, hC, hv', hng] using hgas
    have h1 : ¬gas < B + (ACCOUNT_WRITE + CALL_STIPEND) + M := by omega
    have h2 : ¬gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) < N := by omega
    have h3 : ¬gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N < min g.toNat
        (maxMessageCallGas (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)) := by
      have := maxMessageCallGas_le (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)
      omega
    have hL : gas - M - (B + N + (ACCOUNT_WRITE + CALL_STIPEND)) =
        gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N := by
      omega
    have hG : gas - (min g.toNat
          (maxMessageCallGas (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)) +
        (B + N + (ACCOUNT_WRITE + CALL_STIPEND)) + M) =
        gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N - min g.toNat
          (maxMessageCallGas (gas - (B + (ACCOUNT_WRITE + CALL_STIPEND) + M) - N)) := by
      omega
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
      accountCode, recordAccountRead, hcode, hdel', htw, Except.mapError,
      callExtraGas, callNewAccountGas, callNewAccountCost, callNewAccountStateGas, hC, hv',
      payCall, messageCallGas, chargeGas, chargeStateGas, GasMeter.charge, GasMeter.chargeState,
      finishCall, keepReads, GasMeter.gasLeft, GasMeter.drain, hstatic, hbal, hB, hN, hM, h1, h2,
      h3, hgas', hL, hG, skipCall, refillStateGas, GasMeter.refill, GasMeter.credit, pushWord,
      Stack.push, hlen, advance, Functor.map, Except.map]
  · simp only [callNewAccountGas_of_lt (Nat.lt_of_not_le hng)] at hgas ⊢
    have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
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
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
      accountCode, recordAccountRead, hcode, hdel', htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callValueCost, hv',
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, hstatic, hE,
      hgas', Nat.not_lt.mpr hmin, hbal, skipCall, refillStateGas, GasMeter.refill, GasMeter.credit,
      pushWord, Stack.push, hlen, advance, Functor.map, Except.map]

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
  {returnData : ByteArray}

/-- A call that sends no value of its own, to `to`, with a range of input and one of output.

Its cases are CALL and CALLCODE with no value, STATICCALL and DELEGATECALL.

The callee runs arbitrary code.

So the rule takes an assumption on the frame that ends the message. -/
theorem callKindWith (hfork : .berlin ≤ fork) {kind : CallKind}
    {byte : UInt8} {op : Op} {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    -- The opcode at the program counter runs the step of a call of kind `kind`.
    (decoded : Op.ofByte fork byte = some op) (hnone : instruction (Meter := Nat) fork op = none)
    (hrun : messageInstruction (Meter := Nat) fork op = some (callStep kind))
    -- The callee runs the code of `to`, which the state holds.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- From Pectra, that code is no delegation.
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    -- The depth of the frame must leave room for one more frame.
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    -- The access costs 2600 cold and 100 warm by EIP-2929, 3000 cold from Glamsterdam by EIP-8038.
    --
    -- It also pays the growth of memory for both ranges.
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      -- CALL and CALLCODE pop a value, here 0, and DELEGATECALL and STATICCALL pop none.
      (At code message pc (asked :: to :: ((if kind.sendsValue then [0] else []) ++
          inputStart :: inputSize :: outputStart :: outputSize :: rest))
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        -- The call passes on the gas it asks for.
        --
        -- That is at most all but one 64th of the gas left, by EIP-150.
        --
        -- The gas left is counted after the access and the growth of memory.
        msg.gas = (messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).subCall ∧
        -- DELEGATECALL keeps the sender and the value of the current message.
        msg.caller = (if kind = .delegatecall then message.caller else message.currentTarget) ∧
        -- CALL and STATICCALL run the code on `to`.
        --
        -- CALLCODE and DELEGATECALL run it on the current account.
        msg.currentTarget = (if kind = .call ∨ kind = .staticcall then toAddressMasked to
          else message.currentTarget) ∧
        msg.target = some (if kind = .call ∨ kind = .staticcall then toAddressMasked to
          else message.currentTarget) ∧
        msg.codeAddress = some (toAddressMasked to) ∧ msg.code = calleeCode ∧
        -- Memory grows for both ranges.
        --
        -- The message carries the bytes of the input range as its data.
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        msg.value = (if kind = .delegatecall then message.value else 0) ∧
        msg.depth = message.depth + 1 ∧
        -- The message is static for STATICCALL, and otherwise when the frame is.
        msg.isStatic = (kind == .staticcall || message.isStatic) ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            -- It writes the start of the output of the callee at the start of the output range.
            --
            -- It writes as many bytes as both the output and the range hold.
            --
            -- It leaves the rest of memory.
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          --
          -- The callee may even call the caller again.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after := by
  subst hcold
  refine (callKindRoute (route := none) hfork hlt hbyte decoded hnone hrun hcode hdel hdepth
    (by simpa only [routeCost, Nat.add_zero] using hgas)).toUnder.consequence
    (fun _ h => h) ?_
  rintro after ⟨caller, msg, child,
    ⟨s1, s2, m1, -, m2, m3, mt, mca, mc, -, md, m5, -, m6, m7, -, -⟩, hcallee, hchild, hat⟩
  simp only [routeCost, Nat.add_zero, routeState, routeSub, routeAddr,
    routeCode] at s1 s2 m1 mca mc hat
  exact ⟨caller, msg, child, hcallee, hchild, s1, s2, m1, m2, m3, mt, mca, mc, md, m5, m6, m7, hat⟩

/-- CALL with no value, to the address `to`, with a range of input and a range of output. -/
theorem callWith (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    -- The callee runs the code of `to`, which the state holds.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- From Pectra, that code is no delegation.
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧
        -- Memory grows for both ranges.
        --
        -- The message carries the bytes of the input range as its data.
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        -- The message is static when the frame is.
        msg.value = 0 ∧ msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            -- It writes the start of the output of the callee at the start of the output range.
            --
            -- It writes as many bytes as both the output and the range hold.
            --
            -- It leaves the rest of memory.
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after :=
  callKindWith (kind := .call) hfork hlt hbyte
    (ofByte_of_decode (op := .call) rfl (Fork.frontier_le _)) instruction_call
    messageInstruction_call hcode hdel hdepth hcold hgas

/-- CALL with no value, to `to`, along the route `route`, with a range of input and one of output.

It follows an EIP-7702 delegation, at every fork from Berlin.

The message is static when the frame is. -/
theorem callRoute (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {calleeCode : ByteArray} {route : Route} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    -- The state holds the code `calleeCode` for `to`.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- The route goes from it to the code that runs.
    (hroute : Routes fork state calleeCode route)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    -- The gas covers the access to `to`, the price of the route, and the growth of memory.
    (hgas : callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareOn fork callee
      -- The runner may fail on that message, with any error, and then the run ends there.
      (CallSends .call message memory gas state substate asked to inputStart inputSize outputStart
        outputSize calleeCode route)
      (At code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- Otherwise the rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child,
        -- The caller and the message are those of a call along the route.
        CallSends .call message memory gas state substate asked to inputStart inputSize outputStart
          outputSize calleeCode route caller msg ∧
        callee caller msg child ∧ child.gas ≤ msg.gas ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            -- It writes the start of the output of the callee at the start of the output range.
            --
            -- It writes as many bytes as both the output and the range hold.
            --
            -- It leaves the rest of memory.
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after :=
  callKindRoute (kind := .call) hfork hlt hbyte
    (ofByte_of_decode (op := .call) rfl (Fork.frontier_le _)) instruction_call
    messageInstruction_call hcode hroute hdepth hgas

/-- CALL with no value and empty ranges of input and output, to the address `to`. -/
theorem call (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart outputStart : U256} {rest : List U256} {cold : Bool}
    {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    -- The callee runs the code of `to`, which the state holds.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- From Pectra, that code is no delegation.
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) ≤ gas) :
    HoareUnder fork callee
      (At code message pc (asked :: to :: 0 :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas 0 (callBaseCost fork cold)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        -- With empty ranges, memory does not grow and the message has no data.
        msg.code = calleeCode ∧ msg.data = .empty ∧ msg.value = 0 ∧
        -- The message is static when the frame is.
        msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (messageCallGas fork 0 asked.toNat gas 0 (callBaseCost fork cold)).cost +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after := by
  have hext : extendMemory memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have h := callWith (callee := callee) (asked := asked) (inputSize := 0) (outputSize := 0)
    (rest := rest) (returnData := returnData) hfork hlt hbyte hcode hdel hdepth hcold
    (by rw [hext]; exact hgas)
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

/-- From Berlin, STATICCALL to `to`, with ranges of input and output. -/
theorem staticcallWith (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    -- The callee runs the code of `to`, which the state holds.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- From Pectra, that code is no delegation.
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧
        -- Memory grows for both ranges.
        --
        -- The message carries the bytes of the input range as its data.
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        -- The message carries no value, and it is static.
        msg.value = 0 ∧ msg.depth = message.depth + 1 ∧ msg.isStatic = true ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            -- It writes the start of the output of the callee at the start of the output range.
            --
            -- It writes as many bytes as both the output and the range hold.
            --
            -- It leaves the rest of memory.
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after :=
  callKindWith (kind := .staticcall) hfork hlt hbyte
    (ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)) instruction_staticcall
    (messageInstruction_staticcall (Nat.le_trans (by decide) hfork)) hcode hdel hdepth hcold hgas

/-- From Berlin, STATICCALL with empty ranges of input and output, to `to`. -/
theorem staticcall (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart outputStart : U256} {rest : List U256} {cold : Bool}
    {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    -- The callee runs the code of `to`, which the state holds.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- From Pectra, that code is no delegation.
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) ≤ gas) :
    HoareUnder fork callee
      (At code message pc (asked :: to :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas 0 (callBaseCost fork cold)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        -- The message carries no value, and it is static.
        msg.code = calleeCode ∧ msg.data = .empty ∧ msg.value = 0 ∧
        msg.depth = message.depth + 1 ∧ msg.isStatic = true ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (messageCallGas fork 0 asked.toNat gas 0 (callBaseCost fork cold)).cost +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after := by
  have hext : extendMemory memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have h := staticcallWith (callee := callee) (asked := asked) (inputSize := 0) (outputSize := 0)
    (rest := rest) (returnData := returnData) hfork hlt hbyte hcode hdel hdepth hcold
    (by rw [hext]; exact hgas)
  rw [hext] at h
  refine h.consequence (fun _ hp => hp) ?_
  rintro evm ⟨caller, msg, child, hc, hle, hst, hss, hmg, rest'⟩
  refine ⟨caller, msg, child, hc, hle, hst, hss, by simpa using hmg, ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, md, m6, m7, m8, hat⟩ := rest'
  refine ⟨m1, m2, m3, m4, m5, by simpa [memoryExtend_zero, memoryReadBytes] using md, m6, m7, m8,
    ?_⟩
  simpa [memoryExtend_zero, memoryWrite] using hat

/-- DELEGATECALL is no instruction of the frame alone: it sends a message. -/
theorem instruction_delegatecall : instruction (Meter := Nat) fork .delegatecall = none := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
    selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Homestead, DELEGATECALL runs the step of a delegate call. -/
theorem messageInstruction_delegatecall (hfork : .homestead ≤ fork) :
    messageInstruction (Meter := Nat) fork .delegatecall = some (callStep .delegatecall) := by
  simp [messageInstruction, callInstruction, HOrElse.hOrElse, OrElse.orElse, Option.orElse, hfork]

/-- From Berlin, DELEGATECALL to `to`, with ranges of input and output. -/
theorem delegatecallWith (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf4)
    -- The callee runs the code of `to`, which the state holds.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- From Pectra, that code is no delegation.
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).subCall ∧
        -- The message runs that code on the current account, which stays its current target.
        --
        -- It keeps the sender and the value of the current message.
        msg.caller = message.caller ∧ msg.currentTarget = message.currentTarget ∧
        msg.target = some message.currentTarget ∧
        msg.codeAddress = some (toAddressMasked to) ∧ msg.code = calleeCode ∧
        -- Memory grows for both ranges.
        --
        -- The message carries the bytes of the input range as its data.
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        msg.value = message.value ∧
        -- The message is static when the frame is.
        msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            -- It writes the start of the output of the callee at the start of the output range.
            --
            -- It writes as many bytes as both the output and the range hold.
            --
            -- It leaves the rest of memory.
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after :=
  callKindWith (kind := .delegatecall) hfork hlt hbyte
    (ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)) instruction_delegatecall
    (messageInstruction_delegatecall (Nat.le_trans (by decide) hfork)) hcode hdel hdepth hcold hgas

/-- CALLCODE is no instruction of the frame alone: it sends a message. -/
theorem instruction_callcode : instruction (Meter := Nat) fork .callcode = none := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
    selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- CALLCODE runs the step of a call of code. -/
theorem messageInstruction_callcode :
    messageInstruction (Meter := Nat) fork .callcode = some (callStep .callcode) := by
  simp [messageInstruction, callInstruction, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Berlin, CALLCODE with no value to `to`, with two ranges. -/
theorem callcodeWith (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf2)
    -- The callee runs the code of `to`, which the state holds.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- From Pectra, that code is no delegation.
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        msg.gas = (messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).subCall ∧
        -- The message runs that code on the current account.
        --
        -- That account is both its sender and its current target.
        msg.caller = message.currentTarget ∧ msg.currentTarget = message.currentTarget ∧
        msg.target = some message.currentTarget ∧
        msg.codeAddress = some (toAddressMasked to) ∧ msg.code = calleeCode ∧
        -- Memory grows for both ranges.
        --
        -- The message carries the bytes of the input range as its data.
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        -- The message carries no value.
        msg.value = 0 ∧
        -- The message is static when the frame is.
        msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            -- It writes the start of the output of the callee at the start of the output range.
            --
            -- It writes as many bytes as both the output and the range hold.
            --
            -- It leaves the rest of memory.
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          -- The caller gets back the gas that the callee leaves.
          --
          -- Its state and substate come from the callee.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after :=
  callKindWith (kind := .callcode) hfork hlt hbyte
    (ofByte_of_decode (op := .callcode) rfl (Fork.frontier_le _)) instruction_callcode
    messageInstruction_callcode hcode hdel hdepth hcold hgas

/-- CALL with a value `v`, which is not 0, to the address `to`, with ranges of input and output. -/
theorem callValue (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to v inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    -- The frame may change the state, and the current account holds at least `v`.
    (hv : v ≠ 0) (hstatic : message.isStatic = false)
    (hbal : v ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    -- The call pays its extra price and the growth of memory.
    --
    -- Its extra price is the access of EIP-2929, 2600 when cold and 100 when warm, from Berlin.
    --
    -- From Glamsterdam, a cold access costs 3000, by EIP-8038.
    --
    -- It adds 9000 for the value, from Frontier, and 11300 from Glamsterdam, by EIP-8038.
    --
    -- It adds 25000 when the callee is dead, by EIP-161 from Spurious Dragon.
    --
    -- From Glamsterdam, it adds the state gas of that new account instead, by EIP-8037.
    (hgas : (callBaseCost fork cold +
            callNewAccountGas fork state (toAddressMasked to) v + callValueCost fork v) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: v :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- The rule holds for every frame that ends the message and meets the assumption.
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } ∧
        -- The call passes on the gas it asks for.
        --
        -- That is at most all but one 64th of the gas left, by EIP-150.
        --
        -- The message gets that gas and the stipend of 2300, and carries the value.
        msg.gas = (messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountGas fork state (toAddressMasked to) v +
              callValueCost fork v)).subCall ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
        msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
        msg.code = calleeCode ∧
        msg.data = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          inputStart.toNat inputSize.toNat ∧
        msg.value = v ∧ msg.shouldTransferValue = true ∧ msg.depth = message.depth + 1 ∧
        -- The message is not static.
        msg.isStatic = false ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountGas fork state (toAddressMasked to) v +
              callValueCost fork v)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          -- The rule says nothing of the state beyond what that frame gives.
          --
          -- The rule for CALL with no value says no more either.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after := by
  apply HoareUnder.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, -⟩
  subst hm hg hs hss hcold hmem
  obtain ⟨stack, hstack, hstep⟩ :=
    callStep_value hfork hst hv hstatic hbal hcode hdel hdepth hgas
  rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
    (by simp only [hc, hpc, hbyte]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _))
    instruction_call messageInstruction_call, hstep]
  refine ⟨hrun, _, _, _, rfl, fun child hchild hcallee => ?_⟩
  refine .inl ((resumeCall_eq (child := child) (o := outputStart) (osz := outputSize) ?_).elim
    fun after ⟨hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11, a12⟩ =>
      ⟨after, hres, _, _, child, hcallee, hchild, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, by simp [hstatic], a1.trans hc, a2.trans hj, a3,
        a4.trans (by rw [pc_callerFrame, hpc]), a5.trans (by rw [stack_callerFrame, hstack]), a6,
        a7.trans (by rfl), a8.trans hrun, a9.trans herr, ao.trans hout, a10, a11, a12⟩)
  show stack.val.length < STACK_LIMIT
  have := evm.stack.property
  rw [hst] at this
  rw [hstack]
  simp at this
  omega

/-- CALL with more value than the current account holds sends no message, and pushes 0.

From Glamsterdam, one counter does not give back the state gas of a new account, unlike EIP-8037.
-/
theorem callValueLow (hfork : .berlin ≤ fork)
    {asked to v inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    -- The frame may change the state.
    (hv : v ≠ 0) (hstatic : message.isStatic = false)
    (hbal : (state.getAccount message.currentTarget).balance < v)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    -- The call pays as with enough value.
    (hgas : (callBaseCost fork cold +
            callNewAccountGas fork state (toAddressMasked to) v + callValueCost fork v) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    Hoare fork
      (At code message pc
        (asked :: to :: v :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      (At code message (pc + 1) (0 :: rest)
        -- The memory of the frame has grown for both ranges.
        (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
        (gas - ((messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountGas fork state (toAddressMasked to) v +
              callValueCost fork v)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          -- The frame gets back the gas that it would pass on, with the stipend of 2300.
          (messageCallGas fork v asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork cold + callNewAccountGas fork state (toAddressMasked to) v +
              callValueCost fork v)).subCall)
        ((state.recordAccountRead (toAddressMasked to)).recordAccountRead message.currentTarget)
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) }
        -- The return data of the frame is empty.
        .empty) := by
  apply Triple.of_step
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, -⟩
  subst hm hg hs hss hcold hmem
  obtain ⟨after, hstep, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, ar, a10, a11⟩ :=
    callStep_value_low hfork hst hv hstatic hbal hcode hdel hgas
  refine ⟨after, .next hrun ?_, by rw [a1, hc], by rw [a2, hj], a3, by rw [a4, hpc], a5, a6, a7,
    by rw [a8, hrun], by rw [a9, herr], by rw [ao, hout], a10, a11, ar⟩
  rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
    (by simp only [hc, hpc, hbyte]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _))
    instruction_call messageInstruction_call]
  exact hstep

/-- The assumption that a call to no code and no precompile ends with no error and no output. -/
def NoCodeSucceeds {Meter : Type} [GasMeter Meter] (_caller : Evm fork Meter)
    (message : Message fork) (child : Evm fork Meter) : Prop :=
  message.code = .empty → message.target.isSome = true → precompileAddress fork message = none →
    child.error = none ∧ child.output = .empty

/-- A running frame past the end of its code stops at once, and keeps its error and output. -/
theorem runFrame_of_code_le {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {bound : Nat} {runChild : MessageRunner fork Meter bound} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (hsize : evm.code.size ≤ evm.pc)
    (running : evm.running = true)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.error = evm.error ∧ after.output = evm.output := by
  have hs : step fork evm = .ok (.next (advance { evm with running := false })) := by
    unfold step
    simp only [Nat.not_lt.mpr hsize, dite_false]
    rfl
  rw [runFrame_of_step_eq_next running hs, runFrame_of_running_eq_false rfl] at h
  cases h
  exact ⟨rfl, rfl⟩

/-- A running frame past the end of its code stops at once, with no error when it had none. -/
theorem error_runFrame_of_code_le {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {bound : Nat} {runChild : MessageRunner fork Meter bound} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (hsize : evm.code.size ≤ evm.pc)
    (running : evm.running = true) (herr : evm.error = none)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.error = none :=
  (runFrame_of_code_le hsize running h).1.trans herr

/-- A message with no code, to an account that is no precompile, ends with no error and no output.

That holds whenever the interpreter returns a frame for it. -/
theorem processMessage_of_empty {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hcode : message.code = .empty) (hpre : precompileAddress fork message = none)
    (h : processMessage fork message state substate = .ok ended) :
    ended.val.error = none ∧ ended.val.output = .empty := by
  rw [processMessage_unfold] at h
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
      obtain ⟨hnone, hout⟩ := runFrame_of_code_le (by simp [startFrame, hcode]) rfl hrun
      simp [startFrame] at hnone hout
      simp [rollbackOnError, hnone, hout]

/-- A message with no code, to an account that is no precompile, ends with no error.

That holds whenever the interpreter returns a frame for it. -/
theorem error_processMessage_of_empty {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hcode : message.code = .empty) (hpre : precompileAddress fork message = none)
    (h : processMessage fork message state substate = .ok ended) : ended.val.error = none :=
  (processMessage_of_empty hcode hpre h).1

/-- The interpreter meets the assumption that a call to no code ends with no error and no output.

It runs a call or a creation, as the code of a message runs them, for every bound on their gas. -/
theorem meets_process_noCode {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] (fork : Fork)
    (bound : Nat) :
    Meets (bound := bound) (NoCodeSucceeds (fork := fork) (Meter := Meter))
      (processRunner fork (Meter := Meter) bound) := by
  refine ⟨fun caller message _ child h hcode htarget hpre => ?_, (meets_process fork bound).aborts⟩
  unfold processRunner at h
  split at h
  · exact processMessage_of_empty hcode hpre h
  · rename_i hnone
    simp [hnone] at htarget

/-- From Berlin, STATICCALL to no code and no precompile returns no data. -/
theorem staticcall_noCode (hfork : .berlin ≤ fork)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    -- The account at `to` holds no code.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok .empty)
    -- The transaction maps `to` to no precompile of the fork.
    (hpre : ∀ address, message.txEnv.precompiles (toAddressMasked to) = some address →
      Precompiles.isPrecompile fork address.toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    -- Under the assumption that a call to no code ends with no error and no output.
    HoareUnder fork NoCodeSucceeds
      (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- The caller pushes 1, and its return data is empty.
      --
      -- Memory grows for both ranges, and the output range keeps its bytes.
      --
      -- So only a check of the size of the return data rejects the call.
      --
      -- The gas that the callee leaves, and the state and substate after the call, are left open.
      fun after => ∃ childGas state' substate', At code message (pc + 1) (1 :: rest)
        (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
        (gas - ((messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          childGas)
        state' substate' .empty after := by
  subst hcold
  have h := callKindRoute (kind := .staticcall) (route := none) (asked := asked)
    (inputStart := inputStart) (inputSize := inputSize) (outputStart := outputStart)
    (outputSize := outputSize) (memory := memory) (gas := gas) (state := state)
    (substate := substate) (callee := NoCodeSucceeds) (rest := rest) (returnData := returnData)
    hfork hlt hbyte
    (ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)) instruction_staticcall
    (messageInstruction_staticcall (Nat.le_trans (by decide) hfork)) hcode
    (fun _ => rfl) hdepth (by simpa only [routeCost, Nat.add_zero] using hgas)
  refine h.toUnder.consequence (fun _ h => h) ?_
  rintro after ⟨caller, msg, child,
    ⟨-, -, -, -, -, -, mt, mca, mc, -, -, -, -, -, -, -, mtx⟩, hcallee, -, hat⟩
  -- The message runs no code, on `to`, which is no precompile.
  have hp : precompileAddress fork msg = none := by
    unfold precompileAddress
    rw [mca, mtx]
    simp only [routeAddr, Option.bind_some]
    cases h : message.txEnv.precompiles (toAddressMasked to) with
    | none => rfl
    | some address => simp [hpre address h]
  obtain ⟨herr, hout⟩ := hcallee (by simpa [routeCode] using mc) (by simp [mt]) hp
  refine ⟨child.gas, (incorporateChild fork caller child).state,
    (incorporateChild fork caller child).substate, ?_⟩
  simp only [routeCost, Nat.add_zero, herr, hout] at hat
  simpa [memoryWrite] using hat

/-- From Berlin, RETURNDATASIZE after STATICCALL to no code pushes 0.

The callee is no precompile. -/
theorem staticcall_noCode_returndatasize (hfork : .berlin ≤ fork)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} (hlt : pc + 1 < code.size) (hbyte : code[pc] = 0xfa)
    (hbyteNext : code[pc + 1] = 0x3d)
    -- The account at `to` holds no code.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok .empty)
    -- The transaction maps `to` to no precompile of the fork.
    (hpre : ∀ address, message.txEnv.precompiles (toAddressMasked to) = some address →
      Precompiles.isPrecompile fork address.toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas)
    -- The gas left after the call covers RETURNDATASIZE.
    (hgasNext : 2 ≤ gas - ((messageCallGas fork 0 asked.toNat gas
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
      (callBaseCost fork cold)).cost +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost))
    -- The stack has room for the word of RETURNDATASIZE, as it always has after the call.
    (hstack : rest.length + 1 < STACK_LIMIT) :
    HoareUnder fork NoCodeSucceeds
      (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      -- A check that the return data holds 32 bytes then compares 32 with 0, and fails.
      fun after => ∃ memory' gas' state' substate', At code message (pc + 2) (0 :: 1 :: rest)
        memory' gas' state' substate' .empty after := by
  refine (staticcall_noCode hfork (by omega) hbyte hcode hpre hdepth hcold hgas).seq
    (HoareUnder.of_exists (R := fun (x : Nat × State.TransactionState × Substate) =>
      At code message (pc + 1) (1 :: rest)
        (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
        (gas - ((messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          x.1)
        x.2.1 x.2.2 .empty)
      (fun _ ⟨g, st, ss, h⟩ => ⟨(g, st, ss), h⟩) fun ⟨g, st, ss⟩ => ?_)
  refine (HoareUnder.of_hoare (returndatasize (Nat.le_trans (by decide) hfork) hlt hbyteNext
    (by omega) (by simpa using hstack))).consequence (fun _ h => h) ?_
  intro after h
  exact ⟨_, _, _, _, by simpa using h⟩

end EthLib.Execution.Evm.Logic
