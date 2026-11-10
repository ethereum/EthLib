module

public import EthLib.Execution.Proofs.Evm.Logic.MeterStorage
public import EthLib.Execution.Proofs.Evm.Machine.JumpDest

/-!
# Proofs: supported instructions keep opcode boundaries

The opcode scan skips the data of PUSH instructions.

A supported instruction keeps the code and its jump-destination flags.

A running result advances past one opcode or reaches a valid jump destination.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 byteAt)

variable {fork : Fork}

/-- The instructions whose normal runs have the same effects under both meters. -/
def meterSupported : Op → Bool
  | .stop | .add | .mul | .sub | .div | .mod | .lt | .gt | .eq | .iszero | .and
  | .shl | .shr | .caller | .callvalue | .calldataload | .calldatasize | .calldatacopy
  | .timestamp | .number | .pop | .mstore | .mstore8 | .sload | .sstore | .jump | .jumpi
  | .jumpdest | .push _ | .dup _ | .swap _ | .«return» | .revert => true
  | .log n => n == 0
  | _ => false

/-- Every opcode position contains a supported instruction, or an invalid opcode. -/
def SupportedCode (code : ByteArray) : Bool :=
  (opcodePositions code).all fun pc => (Op.decode (byteAt code pc)).all meterSupported

/-- The code and flags stay, and a running result advances or reaches a valid jump destination.

A normal result can only follow a frame with no error. -/
def MeterFields (before after : Evm fork Nat) (next : Nat) : Prop :=
  after.code = before.code ∧ after.validJumpDestinations = before.validJumpDestinations ∧
    (after.running = true → after.pc = next ∨
      isValidJumpDest before.validJumpDestinations after.pc = true) ∧
    (after.error = none → before.error = none)

private theorem meterFields_map {α : Type} {result : Except EvmError α}
    {build : α → Evm fork Nat} {before after : Evm fork Nat} {next : Nat}
    (ok : result.map build = .ok after) (fields : ∀ x, MeterFields before (build x) next) :
    MeterFields before after next := by
  cases result with
  | error e => cases ok
  | ok x => cases ok; exact fields x

/-- A binary stack operation keeps the opcode scan and the code. -/
private theorem binaryOp_meterFields {cost : Nat} {f : U256 → U256 → U256}
    {evm after : Evm fork Nat} (ok : binaryOp cost f evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [binaryOp, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [binaryOp, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [binaryOp_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- A unary stack operation keeps the opcode scan and the code. -/
private theorem unaryOp_meterFields {cost : Nat} {f : U256 → U256}
    {evm after : Evm fork Nat} (ok : unaryOp cost f evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [unaryOp, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [unaryOp_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- POP keeps the opcode scan and the code. -/
private theorem popStep_meterFields
    {evm after : Evm fork Nat} (ok : popStep evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [popStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [popStep_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- PUSH keeps the opcode scan and the code. -/
private theorem pushN_meterFields {n : Fin 33}
    {evm after : Evm fork Nat} (ok : pushN n evm = .ok after) :
    MeterFields evm after (evm.pc + (1 + n.val)) := by
  by_cases room : evm.stack.val.length < STACK_LIMIT
  · rw [pushN_of_length_lt room] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]
  · have full : evm.stack.val.length = STACK_LIMIT := by have := evm.stack.property; omega
    rcases paid : GasMeter.charge evm.gas
        (if n = 0 then GasCosts.OPCODE_PUSH0 else GasCosts.OPCODE_PUSH) with _ | _ <;>
      simp [pushN, chargeGas, paid, bind, Except.bind, pure, Except.pure, pushWord,
        Stack.push, full] at ok

/-- DUP keeps the opcode scan and the code. -/
private theorem dupN_meterFields {n : Fin 16}
    {evm after : Evm fork Nat} (ok : dupN n evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  cases value : evm.stack.val[n.val]? with
  | none =>
    rcases paid : GasMeter.charge evm.gas GasCosts.OPCODE_DUP with _ | _ <;>
      simp [dupN, chargeGas, paid, bind, Except.bind, pure, Except.pure, value] at ok
  | some x =>
    by_cases room : evm.stack.val.length < STACK_LIMIT
    · rw [dupN_of_getElem? value room] at ok
      exact meterFields_map ok fun _ => by simp [MeterFields]
    · have full : evm.stack.val.length = STACK_LIMIT := by have := evm.stack.property; omega
      rcases paid : GasMeter.charge evm.gas GasCosts.OPCODE_DUP with _ | _ <;>
        simp [dupN, chargeGas, paid, bind, Except.bind, pure, Except.pure, value,
          pushWord, Stack.push, full] at ok

/-- SWAP keeps the opcode scan and the code. -/
private theorem swapN_meterFields {n : Fin 16}
    {evm after : Evm fork Nat} (ok : swapN n evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
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
      exact meterFields_map ok fun _ => by simp [MeterFields]

/-- CALLDATALOAD keeps the opcode scan and the code. -/
private theorem calldataloadStep_meterFields
    {evm after : Evm fork Nat} (ok : calldataloadStep evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [calldataloadStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [calldataloadStep_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- MSTORE keeps the opcode scan and the code. -/
private theorem mstoreStep_meterFields
    {evm after : Evm fork Nat} (ok : mstoreStep evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [mstoreStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [mstoreStep, popWord, Stack.pop, stack, bind, Except.bind, pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [mstoreStep_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- MSTORE8 keeps the opcode scan and the code. -/
private theorem mstore8Step_meterFields
    {evm after : Evm fork Nat} (ok : mstore8Step evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [mstore8Step, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [mstore8Step, popWord, Stack.pop, stack, bind, Except.bind, pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [mstore8Step_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- RETURN keeps the opcode scan and the code. -/
private theorem returnStep_meterFields
    {evm after : Evm fork Nat} (ok : returnStep evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · simp [returnStep, haltWithOutput, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [returnStep, haltWithOutput, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: rest := by rw [stack]
    rw [returnStep_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- A copy of bytes to memory keeps the opcode scan and the code. -/
private theorem copyToMemory_meterFields {base : Nat} {data : ByteArray}
    {evm after : Evm fork Nat} (ok : copyToMemory base data evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩, hp⟩
  · simp [copyToMemory, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [copyToMemory, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · simp [copyToMemory, popWord, Stack.pop, stack, bind, Except.bind,
      pure, Except.pure] at ok
  · have words : evm.stack.val = x :: y :: z :: rest := by rw [stack]
    rw [copyToMemory_cons words] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]

/-- SLOAD keeps the opcode scan and the code. -/
private theorem sloadStep_meterFields
    {evm after : Evm fork Nat} (ok : sloadStep evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · simp [sloadStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · have words : evm.stack.val = x :: rest := by rw [stack]
    rw [sloadStep_cons words] at ok
    by_cases berlin : fork ≥ .berlin <;>
      simp only [accessStorageKey, berlin, ↓reduceIte] at ok <;>
      exact meterFields_map ok fun _ => by simp [MeterFields]

private theorem stopStep_meterFields {evm after : Evm fork Nat}
    (ok : stopStep evm = .ok after) : MeterFields evm after (evm.pc + 1) := by
  cases ok
  simp [MeterFields, advance]

private theorem jumpdestStep_meterFields {evm after : Evm fork Nat}
    (ok : jumpdestStep evm = .ok after) : MeterFields evm after (evm.pc + 1) := by
  rw [jumpdestStep_eq] at ok
  exact meterFields_map ok fun _ => by simp [MeterFields]

private theorem readFrame_meterFields {cost : Nat} {value : Evm fork Nat → U256}
    {evm after : Evm fork Nat} (ok : readFrame cost value evm = .ok after) :
    MeterFields evm after (evm.pc + 1) := by
  by_cases room : evm.stack.val.length < STACK_LIMIT
  · rw [readFrame_of_length_lt room] at ok
    exact meterFields_map ok fun _ => by simp [MeterFields]
  · have full : evm.stack.val.length = STACK_LIMIT := by have := evm.stack.property; omega
    rcases paid : GasMeter.charge evm.gas cost with _ | _ <;>
      simp [readFrame, chargeGas, paid, bind, Except.bind, pure, Except.pure, pushWord,
        Stack.push, full] at ok

private theorem revertStep_meterFields {evm after : Evm fork Nat}
    (ok : revertStep evm = .ok after) : MeterFields evm after (evm.pc + 1) := by
  rw [revertStep_eq] at ok
  cases returned : returnStep evm with
  | error e => simp only [returned, Except.map] at ok; cases ok
  | ok stopped =>
    simp only [returned, Except.map, Except.ok.injEq] at ok
    subst after
    have fields := returnStep_meterFields (after := stopped) returned
    exact ⟨fields.1, fields.2.1, fields.2.2.1, fun h => by cases h⟩

private def FixedPosition (before after : Evm fork Nat) : Prop :=
  after.pc = before.pc ∧ after.code = before.code ∧
    after.validJumpDestinations = before.validJumpDestinations ∧ after.error = before.error

private theorem FixedPosition.trans {a b c : Evm fork Nat}
    (h : FixedPosition a b) (h' : FixedPosition b c) : FixedPosition a c :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

private theorem popWord_fixedPosition {evm after : Evm fork Nat} {word : U256}
    (ok : popWord evm = .ok (word, after)) : FixedPosition evm after := by
  unfold popWord at ok
  obtain ⟨⟨x, st⟩, _, h⟩ := EthLib.Base.bind_ok_iff.mp ok
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem chargeGas_fixedPosition {evm after : Evm fork Nat} {amount : Nat}
    (ok : chargeGas evm amount = .ok after) : FixedPosition evm after := by
  change (GasMeter.charge evm.gas amount).map (fun gas => { evm with gas }) = .ok after at ok
  obtain ⟨gas, _, rfl⟩ := EthLib.Base.map_ok_iff.mp ok
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem chargeStateGas_fixedPosition {evm after : Evm fork Nat} {amount : Nat}
    (ok : chargeStateGas evm amount = .ok after) : FixedPosition evm after := by
  change (GasMeter.chargeState evm.gas amount).map (fun gas => { evm with gas }) = .ok after at ok
  obtain ⟨gas, _, rfl⟩ := EthLib.Base.map_ok_iff.mp ok
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem chargeGasAndMemory_fixedPosition {evm after : Evm fork Nat} {amount : Nat}
    {ranges : List (U256 × U256)} (ok : chargeGasAndMemory evm amount ranges = .ok after) :
    FixedPosition evm after := by
  obtain ⟨e, paid, h⟩ := EthLib.Base.bind_ok_iff.mp ok
  cases h
  exact chargeGas_fixedPosition (after := e) paid

private theorem sstoreStep_meterFields {evm after : Evm fork Nat}
    (ok : sstoreStep evm = .ok after) : MeterFields evm after (evm.pc + 1) := by
  unfold sstoreStep at ok
  split at ok
  · cases ok
  obtain ⟨⟨word, e1⟩, hp1, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  obtain ⟨⟨new, e2⟩, hp2, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  dsimp only at ok
  split at ok
  · cases ok
  have p2 := (popWord_fixedPosition hp1).trans (popWord_fixedPosition hp2)
  have pRead : FixedPosition evm
      (recordStorageRead (accessStorageKey e2 e2.message.currentTarget word.toBeBytes).2
        e2.message.currentTarget word.toBeBytes) := by
    unfold accessStorageKey
    split <;> exact p2
  rcases keepReads_eq_ok ok with ok | ⟨error, rfl⟩
  · obtain ⟨e3, he, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
    obtain ⟨e4, hs, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
    have p3 := pRead.trans (chargeGas_fixedPosition he)
    have p4 := p3.trans (chargeStateGas_fixedPosition hs)
    split at ok
    · cases ok
    obtain ⟨state, _, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
    cases ok
    exact ⟨p4.2.1, p4.2.2.1, fun _ => .inl (congrArg (· + 1) p4.1),
      fun h => p4.2.2.2.symm.trans h⟩
  · exact ⟨pRead.2.1, pRead.2.2.1, (fun h => by cases h), (fun h => by cases h)⟩

private theorem logStep_zero_meterFields {evm after : Evm fork Nat}
    (ok : logStep 0 evm = .ok after) : MeterFields evm after (evm.pc + 1) := by
  obtain ⟨⟨start, e1⟩, hp1, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  obtain ⟨⟨size, e2⟩, hp2, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  obtain ⟨⟨topics, e3⟩, hp3, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  change Except.ok ([], e2) = Except.ok (topics, e3) at hp3
  cases hp3
  obtain ⟨e4, paid, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  have p4 := ((popWord_fixedPosition hp1).trans (popWord_fixedPosition hp2)).trans
    (chargeGasAndMemory_fixedPosition paid)
  split at ok
  · cases ok
  cases ok
  exact ⟨p4.2.1, p4.2.2.1, fun _ => .inl (congrArg (· + 1) p4.1),
      fun h => p4.2.2.2.symm.trans h⟩

private theorem jumpStep_meterFields {evm after : Evm fork Nat}
    (ok : jumpStep evm = .ok after) : MeterFields evm after (evm.pc + 1) := by
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
        exact ⟨rfl, rfl, fun _ => .inr valid, fun h => h⟩

private theorem jumpiStep_meterFields {evm after : Evm fork Nat}
    (ok : jumpiStep evm = .ok after) : MeterFields evm after (evm.pc + 1) := by
  rcases stack : evm.stack with ⟨_ | ⟨destination, _ | ⟨condition, rest⟩⟩, hp⟩
  · simp [jumpiStep, popWord, Stack.pop, stack, bind, Except.bind] at ok
  · simp [jumpiStep, popWord, Stack.pop, stack, bind, Except.bind, pure, Except.pure] at ok
  · have words : evm.stack.val = destination :: condition :: rest := by rw [stack]
    by_cases zero : condition = 0
    · subst condition
      rw [jumpiStep_zero words] at ok
      exact meterFields_map ok fun _ => by simp [MeterFields]
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
          exact ⟨rfl, rfl, fun _ => .inr valid, fun h => h⟩

/-- A supported instruction keeps the code, flags and opcode boundary, and never clears an error. -/
theorem instruction_meterFields {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {low after : Evm fork Nat}
    (supported : meterSupported op = true) (since : op.since ≤ fork)
    (dispatch : instruction fork op = some run)
    (decoded : Op.decode (byteAt low.code low.pc) = some op) (ok : run low = .ok after) :
    MeterFields low after (nextOpcode low.code low.pc) := by
  cases op <;> simp only [meterSupported] at supported <;> try contradiction
  all_goals
    simp only [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
      environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
      selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at dispatch
  all_goals
    try (simp only [Option.some.injEq] at dispatch; subst run)
  all_goals simp only [nextOpcode, decoded]
  case add | mul | sub | div | mod | lt | gt | eq | and | shl | shr =>
    exact binaryOp_meterFields ok
  case iszero => exact unaryOp_meterFields ok
  case stop => exact stopStep_meterFields ok
  case pop => exact popStep_meterFields ok
  case push n =>
    simpa only [Nat.add_comm n.val 1, Nat.add_assoc] using pushN_meterFields ok
  case dup => exact dupN_meterFields ok
  case swap => exact swapN_meterFields ok
  case calldataload => exact calldataloadStep_meterFields ok
  case calldatacopy => exact copyToMemory_meterFields ok
  case mstore => exact mstoreStep_meterFields ok
  case mstore8 => exact mstore8Step_meterFields ok
  case sload => exact sloadStep_meterFields ok
  case sstore => exact sstoreStep_meterFields ok
  case jump => exact jumpStep_meterFields ok
  case jumpi => exact jumpiStep_meterFields ok
  case jumpdest => exact jumpdestStep_meterFields ok
  case «return» => exact returnStep_meterFields ok
  case caller | callvalue | calldatasize | timestamp | number => exact readFrame_meterFields ok
  case log n =>
    have hz : n = 0 := by simpa using supported
    subst n
    exact logStep_zero_meterFields ok
  case revert =>
    have since' : Fork.byzantium ≤ fork := since
    simp only [since', ↓reduceIte, Option.some.injEq] at dispatch
    subst run
    exact revertStep_meterFields ok

end EthLib.Execution.Evm.Logic
