module

public import EthLib.Execution.Proofs.Evm.Logic.GasMono
public import EthLib.Execution.Proofs.Evm.Logic.Route

/-!
# Proofs: the steps of a call that sends no message

The rule for calls along a route covers a call whose step sends a message.

The facts here cover the other outcomes of that step, for every kind of call that sends no value.

They hold at every fork from Berlin, with one counter of gas, along either route.

A call with less gas than its price before the gas it passes on fails, or halts the frame.

That price is the access to the address and to the delegate if any, and the growth of memory.

Up to BPO5, the charge of the call fails and the frame halts.

From Glamsterdam, a check of the gas fails the step or halts the frame before it reads the delegate.

A call at the greatest depth, with at least that price in gas, sends no message.

The frame then pays that price, pushes 0 and goes on.

From Pectra, the address may delegate, and the state may fail to give the code of the delegate.

The call then fails, or halts the frame with an error.

From Glamsterdam, a check of the gas may come first: the step fails with out of gas, or halts.

Out of scope: a call that sends value, and a creation.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address toAddressMasked)
open GasCosts

variable {fork : Fork}

/-- The step of a call that sends no value of its own, short of its price, does not succeed.

That price is the access to the address and to the delegate if any, and the growth of memory.

The step fails, or halts the frame with an error.

It holds at every fork from Berlin. -/
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
  obtain ⟨stack, -, h⟩ := callStep_of_routes hfork hst hcode hroute rfl rfl rfl
  simp only at h
  generalize callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) =
    cb at h hgas
  generalize routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route =
    dc at h hgas
  generalize extendMemory evm.memory.size [(i, isz), (o, osz)] = growth at h hgas
  rw [h]
  by_cases hG : fork ≥ .glamsterdam
  · by_cases c1 : evm.gas < cb + growth.cost
    · simp only [hG, c1, and_self, ↓reduceIte]
      exact .inl ⟨_, rfl⟩
    have c2 : evm.gas < cb + growth.cost + dc := by omega
    simp only [hG, c1, c2, and_self, and_false, ↓reduceIte]
    exact .inr ⟨_, rfl, rfl, nofun⟩
  have hle : cb + dc ≤ (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost := by
    simp [messageCallGas]
  have c3 : evm.gas <
      (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost + growth.cost := by omega
  simp only [hG, c3, false_and, ↓reduceIte]
  exact .inr ⟨_, rfl, rfl, nofun⟩

/-- The step of a call that sends no value of its own, at the greatest depth, sends no message.

The gas of the frame covers at least the price of the access, the route and memory.

The frame then pushes 0 and goes on to the next opcode, with empty return data.

It pays only that price and grows its memory, and it gets back the gas it would pass on.

It holds at every fork from Berlin. -/
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
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.returnData = .empty ∧
      after.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      after.gas = evm.gas -
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
        routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) := by
  obtain ⟨stack, hstack, h⟩ := callStep_of_routes hfork hst hcode hroute rfl rfl rfl
  simp only at h
  generalize callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) =
    cb at h hgas ⊢
  generalize routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) route =
    dc at h hgas ⊢
  generalize extendMemory evm.memory.size [(i, isz), (o, osz)] = growth at h hgas ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hmx : maxMessageCallGas (evm.gas - growth.cost - (cb + dc)) ≤
      evm.gas - growth.cost - (cb + dc) := Nat.sub_le _ _
  have hcost : (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost =
      (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).subCall + (cb + dc) := by
    simp [messageCallGas]
  have hsub : (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).subCall ≤
      evm.gas - growth.cost - (cb + dc) := by
    simp only [messageCallGas, htw, show cb + dc + growth.cost ≤ evm.gas by omega]
    simp only [and_self, ↓reduceIte, Nat.add_zero]
    omega
  have c1 : ¬ evm.gas < cb + growth.cost := by omega
  have c2 : ¬ evm.gas < cb + growth.cost + dc := by omega
  have c3 : ¬ evm.gas <
      (messageCallGas fork 0 g.toNat evm.gas growth.cost (cb + dc)).cost + growth.cost := by omega
  simp only [c1, c2, c3, and_false, ↓reduceIte] at h
  generalize hf : finishCall (fork := fork) (Meter := Nat) kind _ _ _ _ _ _ = x at h
  cases x with
  | error e =>
    have hlen : stack.val.length ≠ STACK_LIMIT := by
      rw [hstack]
      have := evm.stack.property
      rw [hst] at this
      cases kind <;> simp [CallKind.sendsValue] at this <;> omega
    simp [finishCall, genericCall, skipCall, recordAccountRead, refillStateGas, GasMeter.refill,
      hdeep, pushWord, Stack.push, hlen, bind, Except.bind, pure, Except.pure, Functor.map,
      Except.map] at hf
  | ok r =>
    obtain ⟨after, stack', rfl, hst', rfl⟩ := finishCall_of_skip (.inr (by exact hdeep)) hf
    refine ⟨_, h, ?_⟩
    simp only [advance, hst', hstack, GasMeter.credit, GasMeter.refill, GasMeter.drain, true_and]
    omega

/-- The step of a call that sends no value of its own fails when the state lacks its delegate code.

From Pectra, the code of the address delegates to `d`, and the state fails to give the code of `d`.

The step then fails, or halts the frame with an error.

From Glamsterdam, a check of the gas may come first: the step fails with out of gas, or halts. -/
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
          accessDelegation, accountCode, recordAccountRead, hcode, hdel',
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft, exceptionalHalt,
          throw, throwThe, MonadExceptOf.throw]
      · refine .inl ⟨.state e, ?_⟩
        cases kind <;>
        simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord,
          Stack.pop, bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG,
          accessDelegation, accountCode, recordAccountRead, hcode, hdel', hmissing,
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft]
  · refine .inl ⟨.state e, ?_⟩
    cases kind <;>
    simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
      bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hcode, hdel', hmissing, Except.mapError, keepReads]

end EthLib.Execution.Evm.Logic
