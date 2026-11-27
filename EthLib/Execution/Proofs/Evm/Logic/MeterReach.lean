module

public import EthLib.Execution.Proofs.Evm.Logic.MeterStorage
public import EthLib.Base.Proofs.Except

/-!
# Proofs: contract runs under the state gas meter

A successful run of supported instructions can use the state gas meter instead of one counter.

The execution gas of the state gas meter must initially cover the counter.

The supported instructions are all but GAS, the calls, the creations, DUPN, SWAPN and EXCHANGE.

The code check reads only opcode positions, skipping the data of PUSH instructions.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 byteAtOrZero)
open GasCosts

variable {fork : Fork}

/-- The instructions whose runs under one counter carry to the state gas meter. -/
def meterSupported : Op → Bool
  -- GAS pushes the execution gas left, which the state gas meter can make larger.
  | .gas => false
  -- From Glamsterdam, these read an immediate byte, so they move two bytes on.
  | .dupn | .swapn | .exchange => false
  -- The calls and the creations send a message.
  | .create | .create2 | .call | .callcode | .delegatecall | .staticcall => false
  | _ => true

/-- Every opcode position contains a supported instruction, or an invalid opcode. -/
def SupportedCode (code : ByteArray) : Bool :=
  (opcodePositions code).all fun pc => (Op.decode (byteAtOrZero code pc)).all meterSupported

/-- The bytes that an opcode takes: its own, and the data of a PUSH. -/
def opWidth : Op → Nat
  | .push n => 1 + n.val
  | _ => 1

/-- The next opcode starts past the bytes that the opcode at the program counter takes. -/
theorem nextOpcode_eq {code : ByteArray} {pc : Nat} {op : Op}
    (decoded : Op.decode (byteAtOrZero code pc) = some op) :
    nextOpcode code pc = pc + opWidth op := by
  cases op <;> simp only [nextOpcode, decoded, opWidth]
  omega

/-- A supported opcode that exists at the fork has an instruction without a message. -/
theorem instruction_isSome_of_meterSupported {op : Op}
    (supported : meterSupported op = true) (since : op.since ≤ fork) :
    (instruction (Meter := Nat) fork op).isSome := by
  cases op <;> simp only [meterSupported] at supported <;> try contradiction
  all_goals
    simp only [Op.since] at since
    simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
      environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
      selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse, since]
  all_goals by_cases paris : Fork.paris ≤ fork <;> simp [paris]

/-- Two optional instructions that are both absent, or both present and a bridge. -/
def Bridges (width : Nat) :
    Option (Evm fork Nat → Except EvmError (Evm fork Nat)) →
      Option (Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)) → Prop
  | some low, some high => Bridge width low high
  | none, none => True
  | _, _ => False

/-- The first present instruction of two choices, under each meter. -/
theorem Bridges.orElse {width : Nat} {a a' : Option (Evm fork Nat → Except EvmError (Evm fork Nat))}
    {b b' : Option (Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter))}
    (first : Bridges width a b) (second : Bridges width a' b') :
    Bridges width (a <|> a') (b <|> b') := by
  cases a <;> cases b <;> simp_all [Bridges, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

set_option hygiene false in
/-- Unfold one table of instructions on a supported opcode, one goal for each instruction. -/
local macro "table_bridges" table:ident : tactic => `(tactic| (
  cases op <;> simp only [meterSupported] at supported <;> try contradiction
  all_goals simp only [$table:ident, opWidth]
  all_goals (try split) <;> simp only [Bridges, *, dite_true, dite_false, ↓reduceIte,
    ↓reduceDIte]))

private theorem stackOnlyStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (opWidth op) (stackOnlyStep fork op) (stackOnlyStep fork op) := by
  table_bridges stackOnlyStep
  all_goals first
    | trivial
    | with_reducible exact unaryOp_bridge _ _
    | with_reducible exact binaryOp_bridge _ _
    | with_reducible exact ternaryOp_bridge _ _
    | with_reducible exact expStep_bridge
    | with_reducible exact keccak256Step_bridge
    | with_reducible exact popStep_bridge
    | with_reducible exact pushN_bridge _
    | with_reducible exact dupN_bridge _
    | with_reducible exact swapN_bridge _

private theorem controlFlowStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (fork := fork) (opWidth op) (controlFlowStep op) (controlFlowStep op) := by
  table_bridges controlFlowStep
  all_goals first
    | trivial
    | with_reducible exact stopStep_bridge
    | with_reducible exact jumpStep_bridge
    | with_reducible exact jumpiStep_bridge
    | with_reducible exact jumpdestStep_bridge
    | with_reducible exact readFrame_bridge fun _ _ => rfl

private theorem memoryDataStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (fork := fork) (opWidth op) (memoryDataStep op) (memoryDataStep op) := by
  table_bridges memoryDataStep
  all_goals first
    | trivial
    | with_reducible exact mloadStep_bridge
    | with_reducible exact mstoreStep_bridge
    | with_reducible exact mstore8Step_bridge
    | with_reducible exact mcopyStep_bridge
    | with_reducible exact calldataloadStep_bridge
    | with_reducible exact copyToMemory_bridge _ _ _ fun _ _ => rfl
    | with_reducible exact returndatacopyStep_bridge
    | with_reducible exact readFrame_bridge fun _ _ => rfl

private theorem returnOpStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (opWidth op) (returnOpStep fork op) (returnOpStep fork op) := by
  table_bridges returnOpStep
  all_goals first
    | trivial
    | with_reducible exact returnStep_bridge
    | with_reducible exact revertStep_bridge

private theorem environmentStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (opWidth op) (environmentStep fork op) (environmentStep fork op) := by
  table_bridges environmentStep
  all_goals first
    | trivial
    | with_reducible exact blockhashStep_bridge
    | with_reducible exact blobhashStep_bridge _
    | with_reducible exact readFrame_bridge fun _ _ => rfl
    | with_reducible exact readNumber_bridge fun _ _ => rfl

private theorem accountStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (opWidth op) (accountStep fork op) (accountStep fork op) := by
  table_bridges accountStep
  all_goals first
    | trivial
    | with_reducible exact balanceStep_bridge
    | with_reducible exact selfbalance_bridge
    | with_reducible exact extcodesizeStep_bridge
    | with_reducible exact extcodecopyStep_bridge
    | with_reducible exact extcodehashStep_bridge

private theorem storageStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (fork := fork) (opWidth op) (storageStep op) (storageStep op) := by
  table_bridges storageStep
  all_goals first
    | trivial
    | with_reducible exact sloadStep_bridge
    | with_reducible exact sstoreStep_bridge

private theorem transientStorageStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (opWidth op) (transientStorageStep fork op) (transientStorageStep fork op) := by
  table_bridges transientStorageStep
  all_goals first
    | trivial
    | with_reducible exact tloadStep_bridge
    | with_reducible exact tstoreStep_bridge

private theorem logOpStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (fork := fork) (opWidth op) (logOpStep op) (logOpStep op) := by
  table_bridges logOpStep
  all_goals first
    | trivial
    | with_reducible exact logStep_bridge _

private theorem selfdestructOpStep_bridges {op : Op} (supported : meterSupported op = true) :
    Bridges (opWidth op) (selfdestructOpStep fork op) (selfdestructOpStep fork op) := by
  table_bridges selfdestructOpStep
  all_goals first
    | trivial
    | with_reducible exact selfdestructStep_bridge

/-- A supported instruction under one counter is the same instruction under the state gas meter. -/
theorem instruction_bridge {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (supported : meterSupported op = true) (dispatch : instruction fork op = some run) :
    ∃ highRun, instruction fork op = some highRun ∧ Bridge (opWidth op) run highRun := by
  have h : Bridges (opWidth op) (instruction fork op) (instruction fork op) :=
    (stackOnlyStep_bridges supported).orElse <| (controlFlowStep_bridges supported).orElse <|
      (memoryDataStep_bridges supported).orElse <| (returnOpStep_bridges supported).orElse <|
      (environmentStep_bridges supported).orElse <| (accountStep_bridges supported).orElse <|
      (storageStep_bridges supported).orElse <|
      (transientStorageStep_bridges supported).orElse <|
      (logOpStep_bridges supported).orElse (selfdestructOpStep_bridges supported)
  rw [dispatch] at h
  cases high : instruction (Meter := StateGasMeter) fork op with
  | none => rw [high] at h; exact h.elim
  | some highRun => rw [high] at h; exact ⟨highRun, rfl, h⟩

/-- An opcode decoded at a listed position passes the code check. -/
theorem meterSupported_of_supportedCode {code : ByteArray} {pc : Nat} {op : Op}
    (supported : SupportedCode code = true) (boundary : pc ∈ opcodePositions code)
    (decoded : Op.ofByte fork (byteAtOrZero code pc) = some op) : meterSupported op = true := by
  have h := List.all_eq_true.mp supported pc boundary
  have hd := (Option.filter_eq_some_iff.mp decoded).1
  simpa only [hd, Option.all_some] using h

private theorem boundaryFrom_next {code : ByteArray} {start pc : Nat}
    (boundary : BoundaryFrom code start pc) (inside : nextOpcode code pc < code.size) :
    BoundaryFrom code start (nextOpcode code pc) := by
  induction boundary with
  | here h => exact .step h (.here inside)
  | step h _ ih => exact .step h (ih inside)

/-- Checked code with the flags of its scan, at an opcode position when the frame runs. -/
private def MeterReady (evm : Evm fork Nat) : Prop :=
  SupportedCode evm.code = true ∧
    evm.validJumpDestinations = validJumpDestinations evm.code ∧
    (evm.running = true → evm.code.size ≤ evm.pc ∨ evm.pc ∈ opcodePositions evm.code)

/-- A step of checked code keeps its scan, and a normal result can come only from a normal frame.

Under a state gas meter that covers the counter, a normal result also has a step. -/
private theorem step_meterReady {low after : Evm fork Nat} (h : Step fork low after)
    (ready : MeterReady low) :
    MeterReady after ∧ (after.error = none → low.error = none ∧
      ∀ meter : StateGasMeter, low.gas ≤ meter.gasLeft → ∃ m, after.gas ≤ m.gasLeft ∧
        Step fork (withStateGas low meter) (withStateGas after m)) := by
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
        have decodedAt : Op.ofByte fork (byteAtOrZero low.code low.pc) = some op := by
          simpa only [byteAtOrZero, dite_eq_left inside] using decoded
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
          obtain ⟨highRun, dispatchHigh, bridge⟩ := instruction_bridge supportedOp dispatch
          have next := nextOpcode_eq (Option.filter_eq_some_iff.mp decodedAt).1
          obtain ⟨⟨code, sameFlags, pc, normal⟩, -⟩ :=
            bridge low (StateGasMeter.start low.gas 0) (Nat.le_refl _) after ok
          refine ⟨⟨by simpa only [code] using supported,
            by simpa only [code, sameFlags] using flags, ?_⟩, fun hn => ⟨normal hn, ?_⟩⟩
          · intro runs
            rcases pc runs with hn | hj
            · rw [code, hn, ← next]
              by_cases fits : nextOpcode low.code low.pc < low.code.size
              · exact .inr (mem_opcodePositions_iff.mpr
                  (boundaryFrom_next (mem_opcodePositions_iff.mp boundary) fits))
              · exact .inl (Nat.le_of_not_gt fits)
            · rw [flags] at hj
              exact .inr (by rw [code]; exact (isValidJumpDest_iff.mp hj).1)
          · intro meter below
            obtain ⟨highNext, highOk, m, hb, rfl⟩ := (bridge low meter below after ok).2 hn
            refine ⟨m, hb, .next running ?_⟩
            rw [step_of_instruction (evm := withStateGas low meter) inside decoded dispatchHigh,
              highOk]
            rfl
    · rw [step_of_size_le (by omega)] at hs
      cases hs
      refine ⟨⟨supported, flags, fun h => by simp [advance] at h⟩, fun hn => ⟨hn, ?_⟩⟩
      intro meter below
      refine ⟨meter, below, .next running ?_⟩
      exact step_of_size_le (evm := withStateGas low meter) (by exact Nat.le_of_not_gt inside)

private theorem followsMeter_of_meterReady {low after : Evm fork Nat}
    (r : Reaches (Step fork) low after) (ready : MeterReady low)
    (normal : after.error = none) :
    low.error = none ∧ ∀ meter : StateGasMeter, low.gas ≤ meter.gasLeft → ∃ m,
      after.gas ≤ m.gasLeft ∧
        Reaches (Step fork) (withStateGas low meter) (withStateGas after m) := by
  induction r with
  | refl => exact ⟨normal, fun meter below => ⟨meter, below, .refl _⟩⟩
  | step hs _ ih =>
    obtain ⟨nextReady, back⟩ := step_meterReady hs ready
    obtain ⟨nextNormal, rest⟩ := ih nextReady normal
    obtain ⟨lowNormal, first⟩ := back nextNormal
    refine ⟨lowNormal, fun meter below => ?_⟩
    obtain ⟨m, hm, firstStep⟩ := first meter below
    obtain ⟨last, hl, remaining⟩ := rest m hm
    exact ⟨last, hl, .step firstStep remaining⟩

/-- A normal reach through checked code has the same effects under the state gas meter. -/
theorem Reaches.followsMeter {low after : Evm fork Nat} {meter : StateGasMeter}
    (r : Reaches (Step fork) low after) (supported : SupportedCode low.code = true)
    (flags : low.validJumpDestinations = validJumpDestinations low.code)
    (boundary : low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code)
    (normal : after.error = none) (below : low.gas ≤ meter.gasLeft) :
    ∃ m, after.gas ≤ m.gasLeft ∧
      Reaches (Step fork) (withStateGas low meter) (withStateGas after m) :=
  (followsMeter_of_meterReady r ⟨supported, flags, fun _ => boundary⟩ normal).2 meter below

end EthLib.Execution.Evm.Logic
