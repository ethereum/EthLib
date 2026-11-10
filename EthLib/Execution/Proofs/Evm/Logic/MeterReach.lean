module

public import EthLib.Execution.Proofs.Evm.Logic.MeterBoundary
public import EthLib.Execution.Proofs.Evm.Machine.JumpDest

/-!
# Proofs: contract runs under the state gas meter

A successful run of supported instructions can use the state gas meter instead of one counter.

The execution gas of the state gas meter must initially cover the counter.

The instructions do not read gas or send messages, so the two runs agree outside their meters.

The code check reads only opcode positions, skipping the data of PUSH instructions.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 byteAt)

variable {fork : Fork}

/-- A supported opcode that exists at the fork has an instruction without a message. -/
theorem instruction_isSome_of_meterSupported {op : Op}
    (supported : meterSupported op = true) (since : op.since ≤ fork) :
    (instruction (Meter := Nat) fork op).isSome := by
  cases op <;> simp only [meterSupported] at supported <;> try contradiction
  all_goals
    simp only [Op.since] at since
    simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
      environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
      selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
      since]

/-- A normal result of a supported instruction has the same effects under the state gas meter. -/
theorem instruction_followsMeter {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    {low after : Evm fork Nat} {meter : StateGasMeter}
    (supported : meterSupported op = true) (since : op.since ≤ fork)
    (dispatch : instruction fork op = some run) (ok : run low = .ok after)
    (normal : after.error = none) (below : low.gas ≤ meter.gasLeft) :
    ∃ highRun next, instruction fork op = some highRun ∧
      highRun (withStateGas low meter) = .ok next ∧ FollowsMeter after next := by
  cases op <;> simp only [meterSupported] at supported <;> try contradiction
  all_goals
    simp only [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
      environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
      selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at dispatch ⊢
  all_goals
    try (simp only [Option.some.injEq] at dispatch; subst run)
  case add | mul | sub | div | mod | lt | gt | eq | and | shl | shr =>
    obtain ⟨next, hn, hf⟩ := binaryOp_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case iszero =>
    obtain ⟨next, hn, hf⟩ := unaryOp_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case stop =>
    obtain ⟨next, hn, hf⟩ := stopStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case pop =>
    obtain ⟨next, hn, hf⟩ := popStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case push =>
    obtain ⟨next, hn, hf⟩ := pushN_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case dup =>
    obtain ⟨next, hn, hf⟩ := dupN_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case swap =>
    obtain ⟨next, hn, hf⟩ := swapN_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case calldataload =>
    obtain ⟨next, hn, hf⟩ := calldataloadStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case calldatacopy =>
    obtain ⟨next, hn, hf⟩ := copyToMemory_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case mstore =>
    obtain ⟨next, hn, hf⟩ := mstoreStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case mstore8 =>
    obtain ⟨next, hn, hf⟩ := mstore8Step_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case sload =>
    obtain ⟨next, hn, hf⟩ := sloadStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case sstore =>
    obtain ⟨next, hn, hf⟩ := sstoreStep_followsMeter below ok normal
    exact ⟨_, next, rfl, hn, hf⟩
  case jump =>
    obtain ⟨next, hn, hf⟩ := jumpStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case jumpi =>
    obtain ⟨next, hn, hf⟩ := jumpiStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case jumpdest =>
    obtain ⟨next, hn, hf⟩ := jumpdestStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case «return» =>
    obtain ⟨next, hn, hf⟩ := returnStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case caller =>
    obtain ⟨next, hn, hf⟩ := readFrame_followsMeter
      (highValue := fun e => e.message.caller.toU256) below (fun _ _ => rfl) ok
    exact ⟨_, next, rfl, hn, hf⟩
  case callvalue =>
    obtain ⟨next, hn, hf⟩ := readFrame_followsMeter
      (highValue := fun e => e.message.value) below (fun _ _ => rfl) ok
    exact ⟨_, next, rfl, hn, hf⟩
  case calldatasize =>
    obtain ⟨next, hn, hf⟩ := readFrame_followsMeter
      (highValue := fun e => BitVec.ofNat 256 e.message.data.size) below (fun _ _ => rfl) ok
    exact ⟨_, next, rfl, hn, hf⟩
  case timestamp =>
    obtain ⟨next, hn, hf⟩ := readFrame_followsMeter
      (highValue := fun e => e.message.blockEnv.timestamp) below (fun _ _ => rfl) ok
    exact ⟨_, next, rfl, hn, hf⟩
  case number =>
    obtain ⟨next, hn, hf⟩ := readFrame_followsMeter
      (highValue := fun e => BitVec.ofNat 256 e.message.blockEnv.number)
      below (fun _ _ => rfl) ok
    exact ⟨_, next, rfl, hn, hf⟩
  case log n =>
    have hz : n = 0 := by simpa using supported
    subst n
    obtain ⟨next, hn, hf⟩ := logStep_zero_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩
  case revert =>
    have since' : Fork.byzantium ≤ fork := since
    simp only [since', ↓reduceIte, Option.some.injEq] at dispatch ⊢
    subst run
    obtain ⟨next, hn, hf⟩ := revertStep_followsMeter below ok
    exact ⟨_, next, rfl, hn, hf⟩

/-- An opcode decoded at a listed position passes the code check. -/
theorem meterSupported_of_supportedCode {code : ByteArray} {pc : Nat} {op : Op}
    (supported : SupportedCode code = true) (boundary : pc ∈ opcodePositions code)
    (decoded : Op.ofByte fork (byteAt code pc) = some op) : meterSupported op = true := by
  have h := List.all_eq_true.mp supported pc boundary
  have hd := (Option.filter_eq_some_iff.mp decoded).1
  simpa only [hd, Option.all_some] using h

/-- A normal step of checked code has the same effects under the state gas meter. -/
theorem Step.followsMeter {low after : Evm fork Nat} {meter : StateGasMeter}
    (h : Step fork low after) (supported : SupportedCode low.code = true)
    (boundary : low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code)
    (normal : after.error = none) (below : low.gas ≤ meter.gasLeft) :
    ∃ m, after.gas ≤ m.gasLeft ∧
      Step fork (withStateGas low meter) (withStateGas after m) := by
  cases h with
  | halt running failed aborts => simp only [exceptionalHalt, reduceCtorEq] at normal
  | next running hs =>
    by_cases inside : low.pc < low.code.size
    · have boundary := boundary.resolve_left (by omega)
      cases decoded : Op.ofByte fork low.code[low.pc] with
      | none => rw [step_of_ofByte_eq_none inside decoded] at hs; cases hs
      | some op =>
        have supportedOp := meterSupported_of_supportedCode supported boundary
          (by simpa only [byteAt, dite_eq_left inside] using decoded)
        have since := since_le_of_ofByte_eq_some decoded
        obtain ⟨run, dispatch⟩ := Option.isSome_iff_exists.mp
          (instruction_isSome_of_meterSupported supportedOp since)
        rw [step_of_instruction inside decoded dispatch] at hs
        cases ok : run low with
        | error e => simp only [ok, Functor.map, Except.map] at hs; cases hs
        | ok next =>
          simp only [ok, Functor.map, Except.map, Except.ok.injEq,
            StepResult.next.injEq] at hs
          subst next
          obtain ⟨highRun, _, dispatchHigh, highOk, m, hb, rfl⟩ :=
            instruction_followsMeter supportedOp since dispatch ok normal below
          refine ⟨m, hb, .next running ?_⟩
          rw [step_of_instruction (evm := withStateGas low meter) inside decoded dispatchHigh,
            highOk]
          rfl
    · rw [step_of_size_le (by omega)] at hs
      cases hs
      refine ⟨meter, below, .next running ?_⟩
      exact step_of_size_le (evm := withStateGas low meter) (by exact Nat.le_of_not_gt inside)

private theorem boundaryFrom_next {code : ByteArray} {start pc : Nat}
    (boundary : BoundaryFrom code start pc) (inside : nextOpcode code pc < code.size) :
    BoundaryFrom code start (nextOpcode code pc) := by
  induction boundary with
  | here h => exact .step h (.here inside)
  | step h _ ih => exact .step h (ih inside)

private def MeterReady (evm : Evm fork Nat) : Prop :=
  SupportedCode evm.code = true ∧
    evm.validJumpDestinations = validJumpDestinations evm.code ∧
    (evm.running = true → evm.code.size ≤ evm.pc ∨ evm.pc ∈ opcodePositions evm.code)

/-- Checked code keeps its scan, and a normal result can come only from a normal frame. -/
private theorem step_meterReady {low after : Evm fork Nat} (h : Step fork low after)
    (ready : MeterReady low) : MeterReady after ∧ (after.error = none → low.error = none) := by
  obtain ⟨supported, flags, boundary⟩ := ready
  cases h with
  | halt running failed aborts =>
    exact ⟨⟨supported, flags, fun h => by cases h⟩, fun h => by cases h⟩
  | next running hs =>
    by_cases inside : low.pc < low.code.size
    · have boundary := (boundary running).resolve_left (by omega)
      cases decoded : Op.ofByte fork low.code[low.pc] with
      | none => rw [step_of_ofByte_eq_none inside decoded] at hs; cases hs
      | some op =>
        have decodedAt : Op.ofByte fork (byteAt low.code low.pc) = some op := by
          simpa only [byteAt, dite_eq_left inside] using decoded
        have supportedOp := meterSupported_of_supportedCode supported boundary decodedAt
        have since := since_le_of_ofByte_eq_some decoded
        obtain ⟨run, dispatch⟩ := Option.isSome_iff_exists.mp
          (instruction_isSome_of_meterSupported supportedOp since)
        rw [step_of_instruction inside decoded dispatch] at hs
        cases ok : run low with
        | error e => simp only [ok, Functor.map, Except.map] at hs; cases hs
        | ok next =>
          simp only [ok, Functor.map, Except.map, Except.ok.injEq,
            StepResult.next.injEq] at hs
          subst next
          obtain ⟨code, sameFlags, pc, normal⟩ := instruction_meterFields supportedOp since
            dispatch (Option.filter_eq_some_iff.mp decodedAt).1 ok
          refine ⟨⟨by simpa only [code] using supported,
            by simpa only [code, sameFlags] using flags, ?_⟩, normal⟩
          intro runs
          rcases pc runs with hn | hj
          · rw [code, hn]
            by_cases fits : nextOpcode low.code low.pc < low.code.size
            · exact .inr (mem_opcodePositions_iff.mpr
                (boundaryFrom_next (mem_opcodePositions_iff.mp boundary) fits))
            · exact .inl (Nat.le_of_not_gt fits)
          · rw [flags] at hj
            exact .inr (by rw [code]; exact (isValidJumpDest_iff.mp hj).1)
    · rw [step_of_size_le (by omega)] at hs
      cases hs
      exact ⟨⟨supported, flags, fun h => by cases h⟩, id⟩

/-- Every frame of a normal reach through checked code has no error. -/
private theorem normal_of_meterReady {low after : Evm fork Nat}
    (r : Reaches (Step fork) low after) (ready : MeterReady low)
    (normal : after.error = none) : low.error = none := by
  induction r with
  | refl => exact normal
  | step hs _ ih =>
    obtain ⟨nextReady, backward⟩ := step_meterReady hs ready
    exact backward (ih nextReady normal)

private theorem followsMeter_of_meterReady {low after : Evm fork Nat}
    (r : Reaches (Step fork) low after) (ready : MeterReady low)
    (normal : after.error = none) {meter : StateGasMeter} (below : low.gas ≤ meter.gasLeft) :
    ∃ m, after.gas ≤ m.gasLeft ∧
      Reaches (Step fork) (withStateGas low meter) (withStateGas after m) := by
  induction r generalizing meter with
  | refl => exact ⟨meter, below, .refl _⟩
  | step hs rest ih =>
    have nextReady := (step_meterReady hs ready).1
    have nextNormal := normal_of_meterReady rest nextReady normal
    obtain ⟨nextMeter, nextBelow, first⟩ :=
      hs.followsMeter ready.1 (ready.2.2 hs.running) nextNormal below
    obtain ⟨lastMeter, lastBelow, remaining⟩ := ih nextReady normal nextBelow
    exact ⟨lastMeter, lastBelow, .step first remaining⟩

/-- A normal reach through checked code has the same effects under the state gas meter. -/
theorem Reaches.followsMeter {low after : Evm fork Nat} {meter : StateGasMeter}
    (r : Reaches (Step fork) low after) (supported : SupportedCode low.code = true)
    (flags : low.validJumpDestinations = validJumpDestinations low.code)
    (boundary : low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code)
    (normal : after.error = none) (below : low.gas ≤ meter.gasLeft) :
    ∃ m, after.gas ≤ m.gasLeft ∧
      Reaches (Step fork) (withStateGas low meter) (withStateGas after m) :=
  followsMeter_of_meterReady r ⟨supported, flags, fun _ => boundary⟩ normal below

end EthLib.Execution.Evm.Logic
