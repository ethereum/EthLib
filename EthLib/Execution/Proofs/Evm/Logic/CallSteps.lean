module

public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# Proofs: the steps of a call that sends no message

The rule for calls along a route covers a call whose step sends a message.

The facts here cover the other steps of a call that sends no value of its own, of every kind.

They hold at every fork from Berlin, with one counter of gas, along either route.

A call with less gas than its known price fails, or halts the frame with an error.

That price is the access to the address, the price of the route and the growth of memory.

Up to BPO5, the charge of the call fails and the frame halts.

From Glamsterdam, a check of the gas fails first, before the step reads the delegate.

A call at the greatest depth, with the gas of that price, sends no message.

The frame then pushes 0 and goes on.

From Pectra, the address may delegate, and the state may fail to give the code of the delegate.

The call then fails, or halts the frame with an error.

From Glamsterdam, a check of the gas may halt the frame first.

Out of scope: a call that sends value, and a creation.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address toAddressMasked)
open GasCosts

variable {fork : Fork}

/-- The step of a call that sends no value of its own, with less gas than its known price, fails.

It fails, or halts the frame with an error. -/
theorem callStep_fails_of_routes (hfork : .berlin ≤ fork) {kind : CallKind}
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {route : Route}
    (hst : evm.stack.val =
      g :: a :: ((if kind.sendsValue then [0] else []) ++ i :: isz :: o :: osz :: rest))
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode route)
    (hgas : evm.gas <
      callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) :
    StepFails (callStep kind evm) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hroute ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  generalize hdc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked a)) route =
    dc at hgas
  generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M at hgas
  have hab : EvmError.outOfGas.aborts = false := rfl
  by_cases hG : fork ≥ .glamsterdam
  · by_cases hk : gas < cb + M
    · refine .inl ⟨.outOfGas, ?_⟩
      cases kind <;>
      simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, callValueCost, hcb', hM,
        hk, GasMeter.gasLeft, throw, throwThe, MonadExceptOf.throw]
    · refine .inr ?_
      rcases route with _ | ⟨d, dCode⟩
      · simp only [routeCost] at hdc
        omega
      obtain ⟨hpec, hdel, hdcode⟩ := hroute
      have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = some d := by
        simp [hpec, hdel]
      have hdc' : accountAccessCost fork
          (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
        rw [← hdc, routeCost]
        simp
      have hk2 : gas < cb + M + dc := by omega
      cases kind <;>
      simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
        bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hcode, hdel', Except.mapError, callValueCost,
        keepReads, GasMeter.gasLeft, hcb', hdc', hM, hk, hk2, exceptionalHalt, throw, throwThe,
        MonadExceptOf.throw]
  · refine .inr ?_
    have h1 : ¬ (cb + dc + M ≤ gas) := by omega
    have h2 : gas < g.toNat + (cb + dc) + M := by omega
    rcases route with _ | ⟨d, dCode⟩
    · have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
        split
        · exact hroute ‹_›
        · rfl
      simp only [routeCost] at hdc
      subst hdc
      simp only [Nat.add_zero] at h1 h2
      cases kind <;>
      simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
        bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
        callExtraGas, callNewAccountCost, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, keepReads, GasMeter.gasLeft, hcb', hM,
        h1, h2, exceptionalHalt]
    · obtain ⟨hpec, hdel, hdcode⟩ := hroute
      have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = some d := by
        simp [hpec, hdel]
      have hdc' : accountAccessCost fork
          (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
        rw [← hdc, routeCost]
        simp
      cases kind <;>
      simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
        bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode, htw, hsd,
        Except.mapError, callExtraGas, callNewAccountCost, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, keepReads, GasMeter.gasLeft, hcb',
        hdc', hM, h1, h2, exceptionalHalt]

/-- The step of a call that sends no value of its own, at the greatest depth, sends no message.

The gas of the frame covers the known price of the call.

The frame then pushes 0 and goes on to the next opcode. -/
theorem callStep_deep_of_routes (hfork : .berlin ≤ fork) {kind : CallKind}
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {route : Route}
    (hst : evm.stack.val =
      g :: a :: ((if kind.sendsValue then [0] else []) ++ i :: isz :: o :: osz :: rest))
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode route)
    (hdeep : STACK_DEPTH_LIMIT < evm.message.depth + 1)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ after, callStep kind evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hdeep hroute ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  generalize hdc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked a)) route =
    dc at hgas
  generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M at hgas
  have hmx : maxMessageCallGas (gas - (cb + dc + M)) ≤ gas - (cb + dc + M) := Nat.sub_le _ _
  have hmx' : maxMessageCallGas (gas - M - (cb + dc)) ≤ gas - M - (cb + dc) := Nat.sub_le _ _
  have hmin : ¬ gas - (cb + dc + M) < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) := by
    omega
  have hmin2 : ¬ gas < min g.toNat (maxMessageCallGas (gas - M - (cb + dc))) + (cb + dc) + M := by
    omega
  have hk1 : ¬ gas < cb + M := by omega
  have hk2 : ¬ gas < cb + M + dc := by omega
  have hlen : rest.length ≠ STACK_LIMIT := by
    cases kind <;> simp [CallKind.sendsValue] at hl <;> omega
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
    simp only [Nat.add_zero] at hgas hmin hmin2 hk2 ⊢
    by_cases hG : fork ≥ .glamsterdam <;> cases kind <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel, htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, hcb', hM, hgas, Nat.not_lt.mpr hgas,
      hmin, hmin2, hdeep, chargeStateGas, GasMeter.chargeState,
      skipCall, refillStateGas, GasMeter.refill, GasMeter.credit, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map]
  · have hdcode : state.getCode (state.getAccount d).codeHash = .ok dCode := hroute.2.2
    have hdc' : accountAccessCost fork
        (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
      rw [← hdc, routeCost]
      simp
    by_cases hG : fork ≥ .glamsterdam <;> cases kind <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel, hdcode, htw, hsd,
      Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, hcb', hdc', hM, hgas,
      Nat.not_lt.mpr hgas, hmin, hmin2, hk1, hk2, hdeep, chargeStateGas, GasMeter.chargeState,
      skipCall, refillStateGas, GasMeter.refill, GasMeter.credit, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map]

/-- The step of a call that sends no value of its own fails when the delegate has no code.

From Pectra, the code of the address delegates to `d`, and the state fails to give the code of `d`.

The step then fails, or halts the frame with an error.

From Glamsterdam, a check of the gas may halt the frame before the lookup. -/
theorem callStep_fails_of_missing {kind : CallKind}
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {d : Address} {e : State.StateError}
    (hst : evm.stack.val =
      g :: a :: ((if kind.sendsValue then [0] else []) ++ i :: isz :: o :: osz :: rest))
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hpectra : .pectra ≤ fork) (hdelegate : delegatedAddress calleeCode = some d)
    (hmissing : evm.state.getCode (evm.state.getAccount d).codeHash = .error e) :
    StepFails (callStep kind evm) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  simp only at hcode hmissing ⊢
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hpectra
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = some d := by
    simp [hpectra, hdelegate]
  have hab : (EvmError.state e).aborts = true := rfl
  have hab' : EvmError.outOfGas.aborts = false := rfl
  by_cases hG : fork ≥ .glamsterdam
  · by_cases hk1 : gas <
        callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
        (extendMemory memory.size [(i, isz), (o, osz)]).cost
    · refine .inl ⟨.outOfGas, ?_⟩
      cases kind <;>
      simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, callValueCost, hk1,
        GasMeter.gasLeft, throw, throwThe, MonadExceptOf.throw]
    · by_cases hk2 : gas <
          callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
          (extendMemory memory.size [(i, isz), (o, osz)]).cost +
          accountAccessCost fork
            (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses))
      · refine .inr ?_
        cases kind <;>
        simp [hab', callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord,
          Stack.pop, bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG,
          accessDelegation, accountCode, recordAccountRead, hgc, hga, hcode, hdel',
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft, exceptionalHalt,
          throw, throwThe, MonadExceptOf.throw]
      · refine .inl ⟨.state e, ?_⟩
        cases kind <;>
        simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord,
          Stack.pop, bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG,
          accessDelegation, accountCode, recordAccountRead, hgc, hga, hcode, hdel', hmissing,
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft]
  · refine .inl ⟨.state e, ?_⟩
    cases kind <;>
    simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
      bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hcode, hdel', hmissing, Except.mapError, keepReads]

end EthLib.Execution.Evm.Logic
