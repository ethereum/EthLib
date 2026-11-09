module

public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Logic.FailsOn

/-!
# Proofs: the route of a call to the code that it runs

A call runs the code of the account at its address.

From Pectra, that code may be a delegation indicator of EIP-7702, to a delegate.

The call then runs the code of the delegate instead.

It pays an access to the delegate, cold or warm by EIP-2929, and records the access and the read.

The message keeps the address of the call as its current target.

Its code address is the delegate, and it runs no precompile at that address.

The call follows one delegation only, even when the delegate has an indicator too.

A route names the code that the call runs.

It is either the code of the address, or a delegate and the code that the state holds for it.

The rule here covers a call that sends no value of its own, of every kind, along either route.

It holds at every fork from Berlin, with one counter of gas.

From Glamsterdam the access to an address costs more, by EIP-8038, and the rule pays that price.

The rule names the message that the call sends.

So a run may stop because the runner fails, but only on that message.

Sources: EIP-150, EIP-2929, EIP-7702 and EIP-8038.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address toAddressMasked)
open GasCosts

variable {fork : Fork}

/-! ## The route of a call -/

/-- The code that a call runs.

None is the code of the address itself.

A delegate `d` and a code `c` mean that the call runs `c`, the code of `d`. -/
abbrev Route := Option (Address × ByteArray)

/-- The route of a call to an account with the code `c`, in the state `state`.

Before Pectra, or when `c` is no delegation indicator, the route is the code of the address.

From Pectra, when `c` delegates to `d`, the route is `d` with the code that `state` holds for it. -/
def Routes (fork : Fork) (state : State.TransactionState) (c : ByteArray) : Route → Prop
  | none => .pectra ≤ fork → delegatedAddress c = none
  | some (d, c') => .pectra ≤ fork ∧ delegatedAddress c = some d ∧
      state.getCode (state.getAccount d).codeHash = .ok c'

/-- The account whose code the call runs, for a call to `address`. -/
def routeAddr (address : Address) : Route → Address
  | none => address
  | some (d, _) => d

/-- The code that the call runs, for a call to an account with the code `c`. -/
def routeCode (c : ByteArray) : Route → ByteArray
  | none => c
  | some (_, c') => c'

/-- The price of the route: 0, or the access to the delegate.

The access is cold when the delegate is not in the accessed addresses `accessed`. -/
def routeCost (fork : Fork) (accessed : Std.ExtTreeSet Address) : Route → Nat
  | none => 0
  | some (d, _) => accountAccessCost fork (decide (d ∉ accessed))

/-- The state once the call follows the route, with the read of the delegate recorded. -/
def routeState (state : State.TransactionState) : Route → State.TransactionState
  | none => state
  | some (d, _) => state.recordAccountRead d

/-- The substate once the call follows the route, with the delegate accessed. -/
def routeSub (substate : Substate) : Route → Substate
  | none => substate
  | some (d, _) => { substate with accessedAddresses := substate.accessedAddresses.insert d }

/-- The route depends on the state only through the code that the state holds at each address. -/
theorem Routes.congr {state state' : State.TransactionState} {c : ByteArray} {route : Route}
    (hcode : ∀ a, state'.getCode (state'.getAccount a).codeHash =
      state.getCode (state.getAccount a).codeHash)
    (h : Routes fork state c route) : Routes fork state' c route := by
  rcases route with _ | ⟨d, c'⟩
  · exact h
  · exact ⟨h.1, h.2.1, (hcode d).trans h.2.2⟩

/-- The route does not depend on the reads that the state records. -/
theorem Routes.recordAccountRead {state : State.TransactionState} {address : Address}
    {c : ByteArray} {route : Route} (h : Routes fork state c route) :
    Routes fork (state.recordAccountRead address) c route :=
  h.congr fun _ => rfl

/-! ## The step of a call along a route -/

/-- The frame `caller` and the message `msg` of a call that sends no value of its own.

The call is of kind `kind`, to `to`, along the route `route` to the code `calleeCode`.

Before the step, the frame has the message `message`, memory, gas, state and substate.

The call asks for `asked` gas, with the input and output ranges `(i, isz)` and `(o, osz)`.

The caller has recorded the reads of `to`, of the delegate, and of its own account.

It has accessed `to` and the delegate.

The message gets the gas that EIP-150 allows after the access, the route and the growth of memory.

CALL and STATICCALL run on `to`, and CALLCODE and DELEGATECALL on the current account.

The message runs the code of the route, with the address of the route as its code address.

It runs no precompile when the route is a delegate.

DELEGATECALL keeps the sender and the value of the current message, and moves no value.

The message is static for STATICCALL, and otherwise when the frame is.

It keeps the block and the transaction of the current message. -/
def CallSends (kind : CallKind) (message : Message fork) (memory : ByteArray) (gas : Nat)
    (state : State.TransactionState) (substate : Substate) (asked to i isz o osz : U256)
    (calleeCode : ByteArray) (route : Route) (caller : Evm fork Nat) (msg : Message fork) :
    Prop :=
  caller.state = (routeState (state.recordAccountRead (toAddressMasked to)) route).recordAccountRead
      message.currentTarget ∧
    caller.substate = routeSub { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } route ∧
    msg.gas = (messageCallGas fork 0 asked.toNat gas
      (extendMemory memory.size [(i, isz), (o, osz)]).cost
      (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
        routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route)).subCall ∧
    msg.caller = (if kind = .delegatecall then message.caller else message.currentTarget) ∧
    msg.currentTarget = (if kind = .call ∨ kind = .staticcall then toAddressMasked to
      else message.currentTarget) ∧
    msg.target = some (if kind = .call ∨ kind = .staticcall then toAddressMasked to
      else message.currentTarget) ∧
    msg.codeAddress = some (routeAddr (toAddressMasked to) route) ∧
    msg.code = routeCode calleeCode route ∧ msg.disablePrecompiles = route.isSome ∧
    msg.data = memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
    msg.value = (if kind = .delegatecall then message.value else 0) ∧
    msg.shouldTransferValue = (kind != .delegatecall) ∧
    msg.depth = message.depth + 1 ∧ msg.isStatic = (kind == .staticcall || message.isStatic) ∧
    msg.blockEnv = message.blockEnv ∧ msg.txEnv = message.txEnv

/-- The step of a call that sends no value of its own sends a message along a route.

CALL and CALLCODE pop a value, here 0, and DELEGATECALL and STATICCALL pop none.

The caller has paid the access to the address and the route.

It has paid the growth of memory, and the gas it passes on.

Its memory has grown for both ranges, and it keeps its output.

The caller and the message are those of a call along the route. -/
theorem callStep_child_of_routes (hfork : .berlin ≤ fork) {kind : CallKind}
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {route : Route}
    (hst : evm.stack.val =
      g :: a :: ((if kind.sendsValue then [0] else []) ++ i :: isz :: o :: osz :: rest))
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode route)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ caller msg, callStep kind evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      caller.gas = evm.gas - ((messageCallGas fork 0 g.toNat evm.gas
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route)).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧ caller.output = evm.output ∧
      CallSends kind evm.message evm.memory evm.gas evm.state evm.substate g a i isz o osz
        calleeCode route caller msg := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  simp only at hcode hgas hdepth hroute ⊢
  unfold CallSends
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas ⊢
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  generalize hdc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked a)) route =
    dc at hgas ⊢
  generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M at hgas ⊢
  have hmx : maxMessageCallGas (gas - (cb + dc + M)) ≤ gas - (cb + dc + M) := Nat.sub_le _ _
  have hx : gas - M - (cb + dc) = gas - (cb + dc + M) := by omega
  have hmin : ¬ gas - (cb + dc + M) < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) := by
    omega
  have hk1 : ¬ gas < cb + M := by omega
  have hmin3 : ¬ gas < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) + (cb + dc) + M := by
    omega
  have hk2 : ¬ gas < cb + M + dc := by omega
  have hdel : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) =
      route.map Prod.fst := by
    rcases route with _ | ⟨d, dCode⟩
    · split
      · exact hroute ‹_›
      · rfl
    · simp [hroute.1, hroute.2.1]
  rcases route with _ | ⟨d, dCode⟩
  · simp only [routeCost] at hdc
    subst hdc
    simp only [Nat.add_zero] at hgas hmin hmin3 hx hk2 hmx ⊢
    by_cases hG : fork ≥ .glamsterdam <;> cases kind <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hcode, hdel, htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', Nat.not_lt.mpr hdepth, hM,
      chargeStateGas, GasMeter.chargeState, hgas, hk1, hmin, hmin3, hx, routeState,
      routeSub, routeAddr, routeCode] <;>
    (refine ⟨?_, ?_, ?_⟩; rotate_left 2
     and_intros <;> first | rfl | omega | (dsimp only; omega))
  · have hdcode : state.getCode (state.getAccount d).codeHash = .ok dCode := hroute.2.2
    have hdc' : accountAccessCost fork
        (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
      rw [← hdc, routeCost]
      simp
    by_cases hG : fork ≥ .glamsterdam <;> cases kind <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hcode, hdel, hdcode, htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', hdc', Nat.not_lt.mpr hdepth, hM,
      chargeStateGas, GasMeter.chargeState, hgas, Nat.not_lt.mpr hgas, hk1, hk2, hmin, hmin3, hx,
      routeState, routeSub, routeAddr, routeCode] <;>
    (refine ⟨?_, ?_, ?_⟩; rotate_left 2
     and_intros <;> first | rfl | omega | (dsimp only; omega))

/-! ## The rule of a call along a route -/

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}

/-- A call that sends no value of its own, to `to`, along the route `route`.

The opcode at the program counter runs the step of a call of kind `kind`.

CALL and CALLCODE pop a value, here 0, and DELEGATECALL and STATICCALL pop none.

The state holds the code `calleeCode` for `to`, and the route goes from it to the code that runs.

The frame holds the access to `to`, the price of the route, and the growth of memory.

The call sends one message, and the caller and the message are those of a call along the route.

The runner may fail on that message, with any error, and then the run ends there.

Otherwise the rule holds for every frame that ends the message and meets the assumption.

The caller pushes 1 when the callee ends with no error, and 0 otherwise.

It writes the start of the output of the callee at the start of the output range.

It writes as many bytes as both the output and the range hold, and leaves the rest of memory.

It gets back the gas that the callee leaves, and its state and substate come from the callee.

The rule says nothing more of them, since the callee is arbitrary. -/
theorem callKindRoute (hfork : .berlin ≤ fork) {kind : CallKind} {byte : UInt8} {op : Op}
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {calleeCode : ByteArray} {route : Route} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op) (hnone : instruction (Meter := Nat) fork op = none)
    (hrun : messageInstruction (Meter := Nat) fork op = some (callStep kind))
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hroute : Routes fork state calleeCode route)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareOn fork callee
      (CallSends kind message memory gas state substate asked to inputStart inputSize outputStart
        outputSize calleeCode route)
      (At code message pc (asked :: to :: ((if kind.sendsValue then [0] else []) ++
          inputStart :: inputSize :: outputStart :: outputSize :: rest))
        memory gas state substate returnData)
      fun after => ∃ caller msg child,
        CallSends kind message memory gas state substate asked to inputStart inputSize outputStart
          outputSize calleeCode route caller msg ∧
        callee caller msg child ∧ child.gas ≤ msg.gas ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after := by
  apply HoareOn.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun', herr, hout, hs, hss, -⟩
  subst hm hg hs hss hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, sends⟩ :=
    callStep_child_of_routes hfork hst hcode hroute hdepth hgas
  refine ⟨hrun', caller, msg, resumeCall fork caller 0 outputStart outputSize, ?_, sends, ?_⟩
  · rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
      (by simp only [hc, hpc, hbyte]; exact decoded) hnone hrun]
    exact hstep
  · intro child hchild hcallee
    have hlen : caller.stack.val.length < STACK_LIMIT := by
      have := evm.stack.property
      rw [hst] at this
      rw [c5]
      cases kind <;> simp [CallKind.sendsValue] at this <;> omega
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11, a12⟩ :=
      resumeCall_eq (child := child) (o := outputStart) (osz := outputSize) hlen
    refine .inl ⟨after, hres, caller, msg, child, sends, hcallee, hchild, ?_⟩
    refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
      by rw [a5, c5], by rw [a6, c6], by rw [a7, c7], by rw [a8, c8, hrun'], by rw [a9, c9, herr],
      by rw [ao, co, hout], a10, a11, a12⟩

/-- CALL with no value, to `to`, along the route `route`, with a range of input and one of output.

The state holds the code `calleeCode` for `to`, and the route goes from it to the code that runs.

The frame holds the access to `to`, the price of the route, and the growth of memory.

The caller and the message are those of a call along the route.

The message is static when the frame is.

The runner may fail on that message, with any error, and then the run ends there.

Otherwise the rule holds for every frame that ends the message and meets the assumption.

The caller pushes 1 when the callee ends with no error, and 0 otherwise.

It writes the start of the output of the callee at the start of the output range.

It writes as many bytes as both the output and the range hold, and leaves the rest of memory.

It gets back the gas that the callee leaves, and its state and substate come from the callee. -/
theorem callRoute (hfork : .berlin ≤ fork)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {calleeCode : ByteArray} {route : Route} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hroute : Routes fork state calleeCode route)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareOn fork callee
      (CallSends .call message memory gas state substate asked to inputStart inputSize outputStart
        outputSize calleeCode route)
      (At code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData)
      fun after => ∃ caller msg child,
        CallSends .call message memory gas state substate asked to inputStart inputSize outputStart
          outputSize calleeCode route caller msg ∧
        callee caller msg child ∧ child.gas ≤ msg.gas ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after :=
  callKindRoute (kind := .call) hfork hlt hbyte
    (ofByte_of_decode (op := .call) rfl (Fork.frontier_le _)) instruction_call
    messageInstruction_call hcode hroute hdepth hgas

end EthLib.Execution.Evm.Logic
