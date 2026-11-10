module

public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.LogData

/-!
# Proofs: a conservative counter for the state gas meter

A one-counter meter pays both execution gas and state gas from its counter.

The state gas meter can pay state gas from its reservoir, and refills can return execution gas.

So its execution gas stays above the counter when it starts above it and makes the same payments.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

/-- A frame with the same fields and a state gas meter in place of its counter. -/
def withStateGas (evm : Evm fork Nat) (meter : StateGasMeter) : Evm fork StateGasMeter :=
  ⟨evm.pc, evm.stack, evm.memory, evm.code, evm.validJumpDestinations, meter, evm.running,
    evm.message, evm.output, evm.returnData, evm.state, evm.substate, evm.error⟩

/-- The frames agree outside their meters, and the execution gas covers the counter. -/
def FollowsMeter (low : Evm fork Nat) (high : Evm fork StateGasMeter) : Prop :=
  ∃ meter, low.gas ≤ meter.gasLeft ∧ high = withStateGas low meter

/-- A payment of execution gas preserves the lower bound given by the counter. -/
theorem charge_followsMeter {gas after amount : Nat} {meter : StateGasMeter}
    (below : gas ≤ meter.gasLeft) (paid : GasMeter.charge gas amount = .ok after) :
    ∃ next, meter.charge amount = .ok next ∧ after ≤ next.gasLeft := by
  simp only [GasMeter.charge] at paid
  split at paid
  · cases paid
  · cases paid
    refine ⟨{ meter with gasLeft := meter.gasLeft - amount }, ?_, ?_⟩
    · simp only [StateGasMeter.charge, ite_eq_right (show ¬meter.gasLeft < amount by omega)]
    · simp only
      omega

/-- A payment of state gas preserves the lower bound given by the counter. -/
theorem chargeState_followsMeter {gas after amount : Nat} {meter : StateGasMeter}
    (below : gas ≤ meter.gasLeft) (paid : GasMeter.chargeState gas amount = .ok after) :
    ∃ next, meter.chargeState amount = .ok next ∧ after ≤ next.gasLeft := by
  simp only [GasMeter.chargeState] at paid
  split at paid
  · cases paid
  · cases paid
    by_cases reservoir : amount ≤ meter.reservoir
    · refine ⟨{ meter with reservoir := meter.reservoir - amount }, ?_, ?_⟩
      · simp only [StateGasMeter.chargeState, ite_eq_left reservoir]
      · simp only
        omega
    · refine ⟨{ meter with
          reservoir := 0
          gasLeft := meter.gasLeft - (amount - meter.reservoir)
          spill := meter.spill + (amount - meter.reservoir) }, ?_, ?_⟩
      · simp only [StateGasMeter.chargeState, ite_eq_right reservoir,
          ite_eq_left (show amount ≤ meter.reservoir + meter.gasLeft by omega)]
      · simp only
        omega

/-- A refill cannot lower the execution gas that covers the counter. -/
theorem refill_followsMeter {gas amount : Nat} {meter : StateGasMeter}
    (below : gas ≤ meter.gasLeft) :
    GasMeter.refill gas amount ≤ (meter.refill amount).gasLeft := by
  simp only [GasMeter.refill, StateGasMeter.refill]
  omega

/-- A frame constructor independent of gas preserves the relation after an execution payment. -/
theorem map_charge_followsMeter {gas cost : Nat} {meter : StateGasMeter}
    {low : Nat → Evm fork Nat} {high : StateGasMeter → Evm fork StateGasMeter}
    {after : Evm fork Nat} (below : gas ≤ meter.gasLeft)
    (same : ∀ g m, high m = withStateGas (low g) m) (gas_low : ∀ g, (low g).gas = g)
    (paid : (GasMeter.charge gas cost).map low = .ok after) :
    ∃ next, (meter.charge cost).map high = .ok next ∧ FollowsMeter after next := by
  cases charge : GasMeter.charge gas cost with
  | error e => simp only [charge, Except.map] at paid; cases paid
  | ok g =>
    simp only [charge, Except.map, Except.ok.injEq] at paid
    subst after
    obtain ⟨m, hm, hbelow⟩ := charge_followsMeter below charge
    exact ⟨high m, by simp only [hm, Except.map], m,
      by simpa only [gas_low] using hbelow, same g m⟩

/-- A frame constructor independent of gas preserves the relation after a state payment. -/
theorem map_chargeState_followsMeter {gas cost : Nat} {meter : StateGasMeter}
    {low : Nat → Evm fork Nat} {high : StateGasMeter → Evm fork StateGasMeter}
    {after : Evm fork Nat} (below : gas ≤ meter.gasLeft)
    (same : ∀ g m, high m = withStateGas (low g) m) (gas_low : ∀ g, (low g).gas = g)
    (paid : (GasMeter.chargeState gas cost).map low = .ok after) :
    ∃ next, (meter.chargeState cost).map high = .ok next ∧ FollowsMeter after next := by
  cases charge : GasMeter.chargeState gas cost with
  | error e => simp only [charge, Except.map] at paid; cases paid
  | ok g =>
    simp only [charge, Except.map, Except.ok.injEq] at paid
    subst after
    obtain ⟨m, hm, hbelow⟩ := chargeState_followsMeter below charge
    exact ⟨high m, by simp only [hm, Except.map], m,
      by simpa only [gas_low] using hbelow, same g m⟩

/-- A binary stack operation gives the same words under the state gas meter. -/
theorem binaryOp_followsMeter {cost : Nat} {f : U256 → U256 → U256}
    {evm after : Evm fork Nat} {meter : StateGasMeter} (below : evm.gas ≤ meter.gasLeft)
    (ok : binaryOp cost f evm = .ok after) :
    ∃ next, binaryOp cost f (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [binaryOp, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [binaryOp, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [binaryOp_cons words] at ok
    rw [binaryOp_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- A unary stack operation gives the same word under the state gas meter. -/
theorem unaryOp_followsMeter {cost : Nat} {f : U256 → U256}
    {evm after : Evm fork Nat} {meter : StateGasMeter} (below : evm.gas ≤ meter.gasLeft)
    (ok : unaryOp cost f evm = .ok after) :
    ∃ next, unaryOp cost f (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [unaryOp, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [unaryOp_cons words] at ok
    rw [unaryOp_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- POP drops the same word under the state gas meter. -/
theorem popStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : popStep evm = .ok after) :
    ∃ next, popStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [popStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [popStep_cons words] at ok
    rw [popStep_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- PUSH reads the same bytes under the state gas meter. -/
theorem pushN_followsMeter {n : Fin 33} {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : pushN n evm = .ok after) :
    ∃ next, pushN n (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  by_cases room : evm.stack.val.length < STACK_LIMIT
  · rw [pushN_of_length_lt room] at ok
    rw [pushN_of_length_lt (evm := withStateGas evm meter) room]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok
  · have full : evm.stack.val.length = STACK_LIMIT := by have := evm.stack.property; omega
    rcases paid : GasMeter.charge evm.gas
        (if n = 0 then GasCosts.OPCODE_PUSH0 else GasCosts.OPCODE_PUSH) with _ | _ <;>
      simp [pushN, chargeGas, paid, bind, Except.bind, pure, Except.pure, pushWord,
        Stack.push, full] at ok

/-- DUP reads the same stack depth under the state gas meter. -/
theorem dupN_followsMeter {n : Fin 16} {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : dupN n evm = .ok after) :
    ∃ next, dupN n (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  cases value : evm.stack.val[n.val]? with
  | none =>
    rcases paid : GasMeter.charge evm.gas GasCosts.OPCODE_DUP with _ | _ <;>
      simp [dupN, chargeGas, paid, bind, Except.bind, pure, Except.pure, value] at ok
  | some x =>
    by_cases room : evm.stack.val.length < STACK_LIMIT
    · rw [dupN_of_getElem? value room] at ok
      rw [dupN_of_getElem? (evm := withStateGas evm meter) value room]
      exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok
    · have full : evm.stack.val.length = STACK_LIMIT := by have := evm.stack.property; omega
      rcases paid : GasMeter.charge evm.gas GasCosts.OPCODE_DUP with _ | _ <;>
        simp [dupN, chargeGas, paid, bind, Except.bind, pure, Except.pure, value,
          pushWord, Stack.push, full] at ok

/-- SWAP exchanges the same words under the state gas meter. -/
theorem swapN_followsMeter {n : Fin 16} {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : swapN n evm = .ok after) :
    ∃ next, swapN n (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨top, rest⟩, hp⟩
  · rcases paid : GasMeter.charge evm.gas GasCosts.OPCODE_SWAP with _ | _ <;>
      simp [swapN, chargeGas, paid, bind, Except.bind, pure, Except.pure, stack] at ok
  · have words : evm.stack.val = top :: rest := by rw [stack]
    cases value : rest[n.val]? with
    | none =>
      rcases paid : GasMeter.charge evm.gas GasCosts.OPCODE_SWAP with _ | _ <;>
        simp [swapN, chargeGas, paid, bind, Except.bind, pure, Except.pure, stack, value] at ok
    | some x =>
      rw [swapN_of_getElem? words value] at ok
      rw [swapN_of_getElem? (evm := withStateGas evm meter) words value]
      exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- CALLDATALOAD reads the same word under the state gas meter. -/
theorem calldataloadStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : calldataloadStep evm = .ok after) :
    ∃ next, calldataloadStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [calldataloadStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [calldataloadStep_cons words] at ok
    rw [calldataloadStep_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- MSTORE writes the same word under the state gas meter. -/
theorem mstoreStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : mstoreStep evm = .ok after) :
    ∃ next, mstoreStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [mstoreStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [mstoreStep, popWord, Stack.pop, stack, bind, Except.bind, pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [mstoreStep_cons words] at ok
    rw [mstoreStep_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- MSTORE8 writes the same byte under the state gas meter. -/
theorem mstore8Step_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : mstore8Step evm = .ok after) :
    ∃ next, mstore8Step (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [mstore8Step, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [mstore8Step, popWord, Stack.pop, stack, bind, Except.bind, pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [mstore8Step_cons words] at ok
    rw [mstore8Step_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- RETURN gives the same bytes under the state gas meter. -/
theorem returnStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : returnStep evm = .ok after) :
    ∃ next, returnStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [returnStep, haltWithOutput, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [returnStep, haltWithOutput, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [returnStep_cons words] at ok
    rw [returnStep_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- STOP gives the same halt under the state gas meter. -/
theorem stopStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : stopStep evm = .ok after) :
    ∃ next, stopStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  simp only [stopStep_eq, Except.ok.injEq] at ok
  subst after
  exact ⟨_, rfl, meter, below, rfl⟩

/-- JUMPDEST gives the same next opcode under the state gas meter. -/
theorem jumpdestStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : jumpdestStep evm = .ok after) :
    ∃ next, jumpdestStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rw [jumpdestStep_eq] at ok
  rw [jumpdestStep_eq]
  exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- A read of a field independent of gas gives the same word under the state gas meter. -/
theorem readFrame_followsMeter {cost : Nat} {value : Evm fork Nat → U256}
    {highValue : Evm fork StateGasMeter → U256} {evm after : Evm fork Nat}
    {meter : StateGasMeter} (below : evm.gas ≤ meter.gasLeft)
    (values : ∀ g m, highValue (withStateGas evm m) = value { evm with gas := g })
    (ok : readFrame cost value evm = .ok after) :
    ∃ next, readFrame cost highValue (withStateGas evm meter) = .ok next ∧
      FollowsMeter after next := by
  by_cases room : evm.stack.val.length < STACK_LIMIT
  · rw [readFrame_of_length_lt room] at ok
    rw [readFrame_of_length_lt (evm := withStateGas evm meter) room]
    apply map_charge_followsMeter below _ (fun _ => rfl) ok
    intro g m
    rw [show highValue { withStateGas evm meter with gas := m } =
      value { evm with gas := g } from values g m]
    rfl
  · have full : evm.stack.val.length = STACK_LIMIT := by have := evm.stack.property; omega
    rcases paid : GasMeter.charge evm.gas cost with _ | _ <;>
      simp [readFrame, chargeGas, paid, bind, Except.bind, pure, Except.pure, pushWord,
        Stack.push, full] at ok

/-- Copying bytes to memory writes the same bytes under the state gas meter. -/
theorem copyToMemory_followsMeter {base : Nat} {data : ByteArray}
    {evm after : Evm fork Nat} {meter : StateGasMeter} (below : evm.gas ≤ meter.gasLeft)
    (ok : copyToMemory base data evm = .ok after) :
    ∃ next, copyToMemory base data (withStateGas evm meter) = .ok next ∧
      FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩, hp⟩
  · simp [copyToMemory, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [copyToMemory, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · simp [copyToMemory, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: z :: rest := by rw [stack]
    rw [copyToMemory_cons words] at ok
    rw [copyToMemory_cons (evm := withStateGas evm meter) words]
    exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- SLOAD accesses the same slot under the state gas meter. -/
theorem sloadStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : sloadStep evm = .ok after) :
    ∃ next, sloadStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [sloadStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [sloadStep_cons words] at ok
    rw [sloadStep_cons (evm := withStateGas evm meter) words]
    by_cases berlin : fork ≥ .berlin <;>
      simp only [accessStorageKey, berlin, ↓reduceIte] at ok ⊢ <;>
      exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

/-- JUMP reaches the same destination under the state gas meter. -/
theorem jumpStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : jumpStep evm = .ok after) :
    ∃ next, jumpStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨destination, rest⟩, hp⟩
  · simp [jumpStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = destination :: rest := by rw [stack]
    cases paid : GasMeter.charge evm.gas GasCosts.OPCODE_JUMP with
    | error e =>
      simp [jumpStep, popWord, Stack.pop, stack, chargeGas, paid, bind, Except.bind,
        pure, Except.pure] at ok
    | ok gas =>
      cases valid : isValidJumpDest evm.validJumpDestinations destination.toNat with
      | false =>
        simp [jumpStep, popWord, Stack.pop, stack, chargeGas, paid, bind, Except.bind,
          pure, Except.pure, valid, throw, throwThe, MonadExceptOf.throw] at ok
      | true =>
        rw [jumpStep_of_isValidJumpDest words paid valid] at ok
        cases ok
        obtain ⟨m, hm, hb⟩ := charge_followsMeter below paid
        rw [jumpStep_of_isValidJumpDest (evm := withStateGas evm meter) words hm valid]
        exact ⟨_, rfl, m, hb, rfl⟩

/-- JUMPI takes the same branch under the state gas meter. -/
theorem jumpiStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : jumpiStep evm = .ok after) :
    ∃ next, jumpiStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rcases stack : evm.stack with ⟨_ | ⟨destination, _ | ⟨condition, rest⟩⟩, hp⟩
  · simp [jumpiStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [jumpiStep, popWord, Stack.pop, stack, bind, Except.bind, pure, Except.pure] at ok
  · have words : evm.stack.val = destination :: condition :: rest := by rw [stack]
    by_cases zero : condition = 0
    · subst condition
      rw [jumpiStep_zero words] at ok
      rw [jumpiStep_zero (evm := withStateGas evm meter) words]
      exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok
    · cases paid : GasMeter.charge evm.gas GasCosts.OPCODE_JUMPI with
      | error e =>
        simp [jumpiStep, popWord, Stack.pop, stack, chargeGas, paid, bind, Except.bind,
          pure, Except.pure] at ok
      | ok gas =>
        cases valid : isValidJumpDest evm.validJumpDestinations destination.toNat with
        | false =>
          have nz : ¬condition = 0#256 := zero
          simp [jumpiStep, popWord, Stack.pop, stack, chargeGas, paid, bind, Except.bind,
            pure, Except.pure, valid, nz, throw, throwThe, MonadExceptOf.throw] at ok
        | true =>
          rw [jumpiStep_of_isValidJumpDest words zero paid valid] at ok
          cases ok
          obtain ⟨m, hm, hb⟩ := charge_followsMeter below paid
          rw [jumpiStep_of_isValidJumpDest
            (evm := withStateGas evm meter) words zero hm valid]
          exact ⟨_, rfl, m, hb, rfl⟩

/-- REVERT gives the same bytes and error under the state gas meter. -/
theorem revertStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : revertStep evm = .ok after) :
    ∃ next, revertStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  rw [revertStep_eq] at ok
  cases returned : returnStep evm with
  | error e => simp only [returned, Except.map] at ok; cases ok
  | ok stopped =>
    simp only [returned, Except.map, Except.ok.injEq] at ok
    subst after
    obtain ⟨next, hn, m, hb, rfl⟩ := returnStep_followsMeter below returned
    rw [revertStep_eq, hn]
    exact ⟨_, rfl, m, hb, rfl⟩

/-- LOG0 pays, grows memory, and records a log with no topics. -/
private theorem logStep_zero_cons {Meter : Type} [GasMeter Meter]
    {evm : Evm fork Meter} {start size : U256} {rest : List U256}
    (words : evm.stack.val = start :: size :: rest) (static : evm.message.isStatic = false) :
    logStep 0 evm =
      let growth := extendMemory evm.memory.size [(start, size)]
      let memory := memoryExtend evm.memory growth.expandBy
      (GasMeter.charge evm.gas (logCost 0 size + growth.cost)).map fun gas =>
        { evm with
          stack := ⟨rest, by have := evm.stack.property; rw [words] at this; simp at this; omega⟩
          gas
          memory
          substate := { evm.substate with
            logs := evm.substate.logs.push
              ⟨evm.message.currentTarget, [], memoryReadBytes memory start.toNat size.toNat⟩ }
          pc := evm.pc + 1 } := by
  have stack : evm.stack = ⟨start :: size :: rest, words ▸ evm.stack.property⟩ := Subtype.ext words
  simp only [logStep, popWord, popTopics, chargeGasAndMemory, chargeGas, stack, Stack.pop]
  rcases paid : GasMeter.charge evm.gas
      (logCost 0 size + (extendMemory evm.memory.size [(start, size)]).cost) with _ | _ <;>
    simp [paid, static, bind, Except.bind, pure, Except.pure, Except.map, advance]

/-- LOG0 records the same log under the state gas meter. -/
theorem logStep_zero_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : logStep 0 evm = .ok after) :
    ∃ next, logStep 0 (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  cases static : evm.message.isStatic with
  | true => exact (logStep_ne_ok_of_isStatic static ok).elim
  | false =>
    rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
    · simp [logStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
    · simp [logStep, popWord, Stack.pop, stack, bind, Except.bind, pure, Except.pure] at ok
    · have words : evm.stack.val = x :: y :: rest := by rw [stack]
      rw [logStep_zero_cons words static] at ok
      rw [logStep_zero_cons (evm := withStateGas evm meter) words static]
      exact map_charge_followsMeter below (fun _ _ => rfl) (fun _ => rfl) ok

end EthLib.Execution.Evm.Logic
