module

public import EthLib.Execution.Proofs.Evm.Logic.FailsOn
public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.Evm.Gas.CallGas

/-!
# Proofs: the route of a call to the code that it runs

A call runs the code at its address, or, from Pectra, the code of a delegate of EIP-7702.

The rule here covers a call that sends no value of its own, of every kind, along either route.

It holds at every fork from Berlin, with one counter of gas.

Sources: [EIP-150][eip150], [EIP-2929][eip2929], [EIP-7702][eip7702] and [EIP-8038][eip8038].

[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#delegation-indicator
[eip8038]: https://eips.ethereum.org/EIPS/eip-8038#parameters
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address toAddressMasked)
open GasCosts

variable {fork : Fork}

/-! ## The route of a call -/

/-- The code that a call runs.

`none` is the code of the address itself.

A delegate `d` and a code `c` mean that the call runs `c`, the code of `d`. -/
abbrev Route := Option (Address × ByteArray)

/-- Whether a route is that of a call to an account with the code `c`, in the state `state`.

Before Pectra, or when `c` is no delegation indicator, the route is the code of the address.

From Pectra, when `c` delegates to `d`, the route is `d` with the code that `state` holds for it. -/
def Routes (fork : Fork) (state : State.TransactionState) (c : ByteArray) : Route → Prop
  | none => .pectra ≤ fork → delegatedAddress c = none
  -- When `c` delegates to `d`, the call runs the code of `d` instead.
  --
  -- It follows one delegation only, even when the delegate has an indicator too.
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

/-- The price of the route: 0, or the access to the delegate, cold or warm by EIP-2929.

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

/-- The step of a call that sends no value of its own, along a route, up to its checks of gas. -/
theorem callStep_of_routes (hfork : .berlin ≤ fork) {kind : CallKind}
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {route : Route} {cb dc : Nat} {growth : ExtendMemory}
    (hst : evm.stack.val =
      g :: a :: ((if kind.sendsValue then [0] else []) ++ i :: isz :: o :: osz :: rest))
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode route)
    -- The call pays `cb` for the access to the address.
    (hcb : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) = cb)
    -- It pays `dc` for the route.
    (hdc : routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route = dc)
    -- It pays `growth` for memory.
    (hgrowth : extendMemory evm.memory.size [(i, isz), (o, osz)] = growth) :
    ∃ stack : Stack, stack.val = rest ∧
      let read := { evm with
        stack, state := evm.state.recordAccountRead (toAddressMasked a)
        substate := { evm.substate with
          accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } }
      let pre := { read with
        state := routeState read.state route, substate := routeSub read.substate route }
      let callGas := messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)
      callStep kind evm =
        -- From Glamsterdam, the step fails when the gas misses the access and the memory growth.
        if fork ≥ .glamsterdam ∧ evm.gas < cb + growth.cost then .error .outOfGas
        -- From Glamsterdam, the frame halts with only the address read if the gas misses the route.
        else if fork ≥ .glamsterdam ∧ evm.gas < cb + growth.cost + dc then
          .ok (.next (exceptionalHalt read .outOfGas))
        -- The frame halts with the reads of the route when the gas misses the charge of the call.
        --
        -- That charge is the gas that the call passes on, the access, the route and the growth.
        else if evm.gas < callGas.cost + growth.cost then
          .ok (.next (exceptionalHalt pre .outOfGas))
        -- Otherwise the frame pays the charge, and the step finishes the call along the route.
        else keepReads pre .next (finishCall kind ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩
          ⟨routeAddr (toAddressMasked a) route, routeCode calleeCode route, route.isSome, dc⟩
          callGas.subCall 0 growth.expandBy
          { pre with gas := evm.gas - (callGas.cost + growth.cost) }) := by
  obtain ⟨stack, hstack, hpop⟩ : ∃ stack : Stack, stack.val = rest ∧
      popCallOperands kind evm =
        .ok (⟨g, toAddressMasked a, 0, i, isz, o, osz⟩, { evm with stack }) := by
    rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
      state, substate, error⟩
    simp only at hst
    subst hst
    cases kind <;> exact ⟨_, rfl, rfl⟩
  refine ⟨stack, hstack, ?_⟩
  simp only [callStep, hpop, bind, Except.bind, ne_eq, not_true_eq_false, and_false, ite_false,
    accessAddress, ge_iff_le, hfork, ite_true, hcb, hgrowth, callValueCost, checkGas,
    recordAccountRead, GasMeter.gasLeft, Nat.add_zero]
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hacc : ∀ e : Evm fork Nat, e.state = evm.state.recordAccountRead (toAddressMasked a) →
      e.substate.accessedAddresses = evm.substate.accessedAddresses.insert (toAddressMasked a) →
      e.gas = evm.gas → ¬ (fork ≥ .glamsterdam ∧ evm.gas < cb + growth.cost) →
      accessDelegation e (toAddressMasked a) (cb + growth.cost) =
        if fork ≥ .glamsterdam ∧ evm.gas < cb + growth.cost + dc then .error .outOfGas
        else .ok
          (⟨routeAddr (toAddressMasked a) route, routeCode calleeCode route, route.isSome, dc⟩,
            { e with
              state := routeState e.state route
              substate := routeSub e.substate route }) := by
    intro e hs hsub hg hk1
    have hcode' : e.state.getCode (e.state.getAccount (toAddressMasked a)).codeHash =
        .ok calleeCode := by
      rw [hs]
      simpa using hcode
    rcases route with _ | ⟨d, dCode⟩
    · have hdel : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
        split
        · exact hroute ‹_›
        · rfl
      simp only [routeCost] at hdc
      subst hdc
      simp only [Nat.add_zero, hk1, ↓reduceIte]
      simp [accessDelegation, accountCode, hcode', hdel, Except.mapError, bind, Except.bind,
        pure, Except.pure, routeAddr, routeCode, routeState, routeSub]
    · obtain ⟨hpec, hdel, hdcode⟩ := hroute
      have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = some d := by
        simp [hpec, hdel]
      have hdc' : accountAccessCost fork (!decide (d ∈ e.substate.accessedAddresses)) = dc := by
        rw [hsub, ← hdc, routeCost]
        simp
      have hdcode' : e.state.getCode (e.state.getAccount d).codeHash = .ok dCode := by
        rw [hs]
        simpa using hdcode
      simp [accessDelegation, accountCode, hcode', hdel', Except.mapError, bind, Except.bind,
        pure, Except.pure, routeAddr, routeCode, routeState, routeSub, accessAddress, hfork,
        checkGas, hdc', hg, recordAccountRead, hdcode', GasMeter.gasLeft]
      by_cases hc : Fork.glamsterdam ≤ fork ∧ evm.gas < cb + growth.cost + dc <;>
        simp only [hc, ↓reduceIte] <;> rfl
  have hpay : ∀ e : Evm fork Nat, e.gas = evm.gas →
      ¬ (fork ≥ .glamsterdam ∧ evm.gas < cb + growth.cost + dc) →
      payCall kind ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩ growth.cost (cb + dc) 0 e =
        if evm.gas < (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost +
            growth.cost then .error .outOfGas
        else .ok ((messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).subCall,
          { e with gas := evm.gas - ((messageCallGas fork 0 g.toNat evm.gas growth.cost
            (cb + dc)).cost + growth.cost) }) := by
    intro e hg hk2
    unfold payCall
    by_cases hc : fork ≥ .glamsterdam ∧ kind = .call
    · have h0 : cb + dc + growth.cost ≤ evm.gas :=
        Nat.le_of_not_lt fun h => hk2 ⟨hc.1, by omega⟩
      have hx : evm.gas - growth.cost - (cb + dc) = evm.gas - (cb + dc + growth.cost) := by omega
      have hmx : maxMessageCallGas (evm.gas - (cb + dc + growth.cost)) ≤
          evm.gas - (cb + dc + growth.cost) := Nat.sub_le _ _
      have h1 : ¬ evm.gas - (cb + dc + growth.cost) <
          min g.toNat (maxMessageCallGas (evm.gas - (cb + dc + growth.cost))) := by omega
      have h2 : ¬ evm.gas < min g.toNat (maxMessageCallGas (evm.gas - (cb + dc + growth.cost))) +
          (cb + dc) + growth.cost := by omega
      have h3 : evm.gas - (cb + dc + growth.cost) -
          min g.toNat (maxMessageCallGas (evm.gas - (cb + dc + growth.cost))) = evm.gas -
          (min g.toNat (maxMessageCallGas (evm.gas - (cb + dc + growth.cost))) + (cb + dc) +
            growth.cost) := by omega
      simp [hc, chargeGas, GasMeter.charge, chargeStateGas, GasMeter.chargeState, messageCallGas,
        GasMeter.gasLeft, hg, bind, Except.bind, pure, Except.pure, htw, hx, Nat.not_lt.mpr h0,
        h0, h1, h2, h3]
    · simp only [hc, ↓reduceIte, chargeGas, GasMeter.charge, GasMeter.gasLeft, hg, bind,
        Except.bind, pure, Except.pure]
      by_cases h : evm.gas <
          (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost + growth.cost <;>
        simp only [h, ↓reduceIte]
  have hextra : ∀ st : State.TransactionState, callExtraGas fork kind st
      ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩
      (decide (toAddressMasked a ∉ evm.substate.accessedAddresses))
      ⟨routeAddr (toAddressMasked a) route, routeCode calleeCode route, route.isSome, dc⟩ =
      cb + dc := by
    intro st
    simp [callExtraGas, callNewAccountCost, callValueCost, hsd, ← hcb]
  have hnew : ∀ st : State.TransactionState,
      callNewAccountStateGas fork kind st ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩ = 0 := by
    intro st
    simp [callNewAccountStateGas]
  by_cases hk1 : Fork.glamsterdam ≤ fork ∧ evm.gas < cb + growth.cost
  · simp only [hk1]
    rfl
  simp only [hk1, ↓reduceIte, pure, Except.pure]
  rw [hacc _ ?_ ?_ ?_ hk1]
  rotate_left
  · rfl
  · rfl
  · rfl
  by_cases hk2 : Fork.glamsterdam ≤ fork ∧ evm.gas < cb + growth.cost + dc
  · simp only [hk2]
    rfl
  simp only [hk2, ↓reduceIte, hextra, hnew]
  rw [hpay _ ?_ hk2]
  rotate_left
  · rfl
  by_cases hk3 : evm.gas <
      (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost + growth.cost
  · simp only [hk3, ↓reduceIte]
    rfl
  simp only [hk3, ↓reduceIte]
  generalize finishCall (fork := fork) (Meter := Nat) kind _ _ _ _ _ _ = x
  cases x with
  | error e => by_cases h : e.aborts <;> simp [keepReads, h]
  | ok r => rfl

/-- The frame `caller` and the message `msg` of a call that sends no value of its own.

The call is of kind `kind`, to `to`, along the route `route` to the code `calleeCode`.

Before the step, the frame has the message `message`, memory, gas, state and substate.

The call asks for `asked` gas, with the input and output ranges `(i, isz)` and `(o, osz)`. -/
def CallSends (kind : CallKind) (message : Message fork) (memory : ByteArray) (gas : Nat)
    (state : State.TransactionState) (substate : Substate) (asked to i isz o osz : U256)
    (calleeCode : ByteArray) (route : Route) (caller : Evm fork Nat) (msg : Message fork) :
    Prop :=
  -- The caller has recorded the reads of `to`, of the delegate, and of its own account.
  caller.state = (routeState (state.recordAccountRead (toAddressMasked to)) route).recordAccountRead
      message.currentTarget ∧
    -- It has accessed `to` and the delegate.
    caller.substate = routeSub { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } route ∧
    -- The message gets the gas it asks for, at most all but one 64th of the gas left.
    --
    -- The gas left is what remains after the access, the route and the growth of memory.
    msg.gas = (messageCallGas fork 0 asked.toNat gas
      (extendMemory memory.size [(i, isz), (o, osz)]).cost
      (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
        routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route)).subCall ∧
    -- It gets no reservoir, since the meter has one counter.
    msg.reservoir = 0 ∧
    -- DELEGATECALL keeps the sender of the current message.
    msg.caller = (if kind = .delegatecall then message.caller else message.currentTarget) ∧
    -- CALL and STATICCALL run on `to`, and CALLCODE and DELEGATECALL on the current account.
    --
    -- A delegation keeps the address of the call as the current target.
    msg.currentTarget = (if kind = .call ∨ kind = .staticcall then toAddressMasked to
      else message.currentTarget) ∧
    msg.target = some (if kind = .call ∨ kind = .staticcall then toAddressMasked to
      else message.currentTarget) ∧
    -- The message runs the code of the route, with the address of the route as its code address.
    msg.codeAddress = some (routeAddr (toAddressMasked to) route) ∧
    -- It runs no precompile when the route is a delegate.
    msg.code = routeCode calleeCode route ∧ msg.disablePrecompiles = route.isSome ∧
    msg.data = memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
    -- DELEGATECALL also keeps the value of the current message, and moves no value.
    msg.value = (if kind = .delegatecall then message.value else 0) ∧
    msg.shouldTransferValue = (kind != .delegatecall) ∧
    -- The message is static for STATICCALL, and otherwise when the frame is.
    msg.depth = message.depth + 1 ∧ msg.isStatic = (kind == .staticcall || message.isStatic) ∧
    -- It keeps the block and the transaction of the current message.
    msg.blockEnv = message.blockEnv ∧ msg.txEnv = message.txEnv

/-- The step of a call that sends no value of its own sends a message along a route.

The calling frame and the message are those that every call builds from the frame after payment. -/
theorem callStep_child_of_routes (hfork : .berlin ≤ fork) {kind : CallKind}
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {route : Route}
    -- CALL and CALLCODE pop a value, here 0, and DELEGATECALL and STATICCALL pop none.
    (hst : evm.stack.val =
      g :: a :: ((if kind.sendsValue then [0] else []) ++ i :: isz :: o :: osz :: rest))
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode route)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ stack : Stack, stack.val = rest ∧
      let growth := extendMemory evm.memory.size [(i, isz), (o, osz)]
      let accessed := evm.substate.accessedAddresses.insert (toAddressMasked a)
      let dc := routeCost fork accessed route
      let callGas := messageCallGas fork 0 g.toNat evm.gas growth.cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) + dc)
      let caller := callerFrame
        { evm with
          -- The frame pops the operands.
          stack
          -- It pays the access, the route, the growth of memory, and the gas it passes on.
          gas := evm.gas - (callGas.cost + growth.cost)
          -- It records the read of the address, and follows the route.
          state := routeState (evm.state.recordAccountRead (toAddressMasked a)) route
          -- It accesses the address.
          substate := routeSub { evm.substate with accessedAddresses := accessed } route }
        growth.expandBy
      callStep kind evm = .ok (.child caller
        (callMessage kind ⟨g, toAddressMasked a, 0, i, isz, o, osz⟩
          ⟨routeAddr (toAddressMasked a) route, routeCode calleeCode route, route.isSome, dc⟩
          -- The message gets the gas it asks for, at most all but one 64th of the gas left.
          --
          -- It gets no reservoir.
          callGas.subCall 0 caller)
        (resumeCall fork caller 0 o osz)) := by
  obtain ⟨stack, hstack, h⟩ := callStep_of_routes hfork hst hcode hroute rfl rfl rfl
  refine ⟨stack, hstack, ?_⟩
  simp only at h ⊢
  generalize callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) =
    cb at h hgas ⊢
  generalize routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route =
    dc at h hgas ⊢
  generalize extendMemory evm.memory.size [(i, isz), (o, osz)] = growth at h hgas ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hmx : maxMessageCallGas (evm.gas - growth.cost - (cb + dc)) ≤
      evm.gas - growth.cost - (cb + dc) := Nat.sub_le _ _
  have hcost : (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost =
      min g.toNat (maxMessageCallGas (evm.gas - growth.cost - (cb + dc))) + (cb + dc) := by
    simp [messageCallGas, htw, show cb + dc + growth.cost ≤ evm.gas by omega]
  have c1 : ¬ (fork ≥ .glamsterdam ∧ evm.gas < cb + growth.cost) := by omega
  have c2 : ¬ (fork ≥ .glamsterdam ∧ evm.gas < cb + growth.cost + dc) := by omega
  have c3 : ¬ evm.gas <
      (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost + growth.cost := by omega
  simp only [h, c1, c2, c3, ↓reduceIte, finishCall, genericCall, keepReads, message_callerFrame,
    ne_eq, not_true_eq_false, and_false, Nat.not_lt.mpr hdepth]
  rfl

/-! ## The rule of a call along a route -/

/-- A caller with room on its stack resumes from every frame that ends its message. -/
theorem resumeCall_eq {caller child : Evm fork Nat} {o osz : U256}
    (hlen : caller.stack.val.length < STACK_LIMIT) :
    ∃ after, resumeCall fork caller 0 o osz child = .ok after ∧
      after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.message = caller.message ∧ after.pc = caller.pc + 1 ∧
      -- It pushes 1 for a frame with no error and 0 otherwise.
      after.stack.val = (if child.error.isNone then 1 else 0) :: caller.stack.val ∧
      -- It writes the start of the output of the frame at the start of its output range.
      --
      -- It writes as many bytes as both the output and the range hold.
      after.memory = memoryWrite caller.memory o.toNat
        (child.output.extract 0 (min osz.toNat child.output.size)) ∧
      -- It gets back the gas of the frame.
      after.gas = caller.gas + child.gas ∧
      -- The caller keeps its own output.
      after.running = caller.running ∧ after.error = caller.error ∧ after.output = caller.output ∧
      after.state = (incorporateChild fork caller child).state ∧
      after.substate = (incorporateChild fork caller child).substate ∧
      after.returnData = child.output := by
  have hne : caller.stack.val.length ≠ STACK_LIMIT := Nat.ne_of_lt hlen
  unfold resumeCall incorporateChild
  split <;>
    simp [pushWord, Stack.push, bind, Except.bind, pure, Except.pure, advance, refillStateGas,
      GasMeter.refill, GasMeter.absorb, *]


variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}

/-- A call that sends no value of its own, to `to`, along the route `route`.

The opcode at the program counter runs the step of a call of kind `kind`. -/
theorem callKindRoute (hfork : .berlin ≤ fork) {kind : CallKind} {byte : UInt8} {op : Op}
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {calleeCode : ByteArray} {route : Route} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op) (hnone : instruction (Meter := Nat) fork op = none)
    (hrun : messageInstruction (Meter := Nat) fork op = some (callStep kind))
    -- The state holds the code `calleeCode` for `to`.
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    -- The route goes from that code to the code that runs.
    --
    -- The rules for calls with no delegation are the cases along the code of the address.
    (hroute : Routes fork state calleeCode route)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    -- The gas of the frame covers the access to `to`, the price of the route, and the growth.
    --
    -- From Glamsterdam a cold access costs 3000 instead of 2600, by EIP-8038, and the rule pays it.
    (hgas : callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas) :
    HoareOn fork callee
      -- The call sends one message, and the caller and message are those of a call along the route.
      --
      -- The runner may fail only on that message, with any error, and then the run ends there.
      (CallSends kind message memory gas state substate asked to inputStart inputSize outputStart
        outputSize calleeCode route)
      -- CALL and CALLCODE pop a value, here 0, and DELEGATECALL and STATICCALL pop none.
      (At code message pc (asked :: to :: ((if kind.sendsValue then [0] else []) ++
          inputStart :: inputSize :: outputStart :: outputSize :: rest))
        memory gas state substate returnData)
      -- Unless the runner fails, the rule holds for every frame that ends the message.
      --
      -- Such a frame meets the assumption.
      fun after => ∃ caller msg child,
        CallSends kind message memory gas state substate asked to inputStart inputSize outputStart
          outputSize calleeCode route caller msg ∧
        callee caller msg child ∧ child.gas ≤ msg.gas ∧
        -- The caller pushes 1 when the callee ends with no error, and 0 otherwise.
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          -- It writes the start of the output of the callee at the start of the output range.
          --
          -- It writes as many bytes as both the output and the range hold, and leaves the rest.
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size
              [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
            outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route)).cost +
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
            -- It gets back the gas that the callee leaves.
            child.gas)
          -- Its state and substate come from the callee.
          --
          -- The rule says nothing more of them, since the callee is arbitrary.
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          child.output after := by
  apply HoareOn.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun', herr, hout, hs, hss, -⟩
  subst hm hg hs hss hmem
  obtain ⟨stack, hstack, hstep⟩ := callStep_child_of_routes hfork hst hcode hroute hdepth hgas
  rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
    (by simp only [hc, hpc, hbyte]; exact decoded) hnone hrun, hstep]
  refine ⟨hrun', _, _, _, rfl, by unfold CallSends; and_intros <;> rfl, ?_⟩
  · intro child hchild hcallee
    refine .inl ((resumeCall_eq (child := child) (o := outputStart) (osz := outputSize) ?_).elim
      fun after ⟨hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11, a12⟩ =>
        ⟨after, hres, _, _, child, by unfold CallSends; and_intros <;> rfl, hcallee, hchild,
          a1.trans hc, a2.trans hj, a3, a4.trans (by rw [pc_callerFrame, hpc]),
          a5.trans (by rw [stack_callerFrame, hstack]), a6, a7.trans (by rfl), a8.trans hrun',
          a9.trans herr, ao.trans hout, a10, a11, a12⟩)
    show stack.val.length < STACK_LIMIT
    have := evm.stack.property
    rw [hst] at this
    rw [hstack]
    cases kind <;> simp [CallKind.sendsValue] at this <;> omega

end EthLib.Execution.Evm.Logic
