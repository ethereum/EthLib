module

public import EthLib.Execution.Proofs.Evm.Logic.MeterStorage
public import EthLib.Execution.Proofs.Evm.Logic.MeterCall
public import EthLib.Base.Proofs.Except

/-!
# Proofs: contract runs under the state gas meter

A successful run of supported instructions can use the state gas meter instead of one counter.

A run that ends in a revert carries too.

The execution gas of the state gas meter must initially cover the counter.

The supported instructions are all but GAS and the creations.

A call that sends a message ends such a run.

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
  -- The creations send a message.
  --
  -- A call is supported: in a run of steps without a message, it sends none or halts.
  | .create | .create2 => false
  | _ => true

/-- The kind of a call opcode, or none for any other opcode. -/
def callKindOf : Op → Option CallKind
  | .call => some .call
  | .callcode => some .callcode
  | .delegatecall => some .delegatecall
  | .staticcall => some .staticcall
  | _ => none

/-- A step on a call opcode that exists at the fork runs the step of that call. -/
theorem step_of_callKindOf {Meter : Type} [GasMeter Meter] {evm : Evm fork Meter} {op : Op}
    {kind : CallKind} (inside : evm.pc < evm.code.size)
    (decoded : Op.ofByte fork evm.code[evm.pc] = some op) (call : callKindOf op = some kind) :
    step fork evm = callStep kind evm := by
  have since := since_le_of_ofByte_eq_some decoded
  cases op <;> simp only [callKindOf, reduceCtorEq, Option.some.injEq] at call <;> subst call <;>
    simp only [Op.since] at since <;>
    exact step_of_messageInstruction inside decoded
      (by simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
        environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
        selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse])
      (by simp [messageInstruction, callInstruction, HOrElse.hOrElse, OrElse.orElse,
        Option.orElse, since])

/-- Every opcode position contains a supported instruction, or an invalid opcode. -/
def SupportedCode (code : ByteArray) : Bool :=
  -- EIP-8024 keeps the jump analysis, so the immediate byte of DUPN, SWAPN or EXCHANGE is read too.
  --
  -- So a byte of GAS or of a creation there fails the check.
  (opcodePositions code).all fun pc => (Op.decode (byteAtOrZero code pc)).all meterSupported

/-- The bytes that an instruction takes: its own, the data of a PUSH, or an immediate byte. -/
def opWidth : Op → Nat
  | .push n => 1 + n.val
  -- From Glamsterdam, DUPN, SWAPN and EXCHANGE read the byte after them and move two bytes on.
  | .dupn | .swapn | .exchange => 2
  | _ => 1

/-- The next opcode starts past the bytes that an opcode with no immediate byte takes. -/
theorem nextOpcode_eq {code : ByteArray} {pc : Nat} {op : Op}
    (decoded : Op.decode (byteAtOrZero code pc) = some op)
    (plain : op ≠ .dupn ∧ op ≠ .swapn ∧ op ≠ .exchange) :
    nextOpcode code pc = pc + opWidth op := by
  cases op <;> simp only [nextOpcode, decoded, opWidth] at plain ⊢
  all_goals first | omega | simp at plain

/-- An immediate byte outside 91 to 127 is no PUSH, so an opcode follows it. -/
theorem nextOpcode_succ_of_immediate {code : ByteArray} {pc : Nat}
    (depth : ¬(90 < (immediateByte code pc).toNat ∧ (immediateByte code pc).toNat < 128)) :
    nextOpcode code (pc + 1) = pc + 2 := by
  rw [EthLib.Execution.Evm.nextOpcode_eq]
  simp only [immediateByte] at depth
  split <;> omega

/-- A success of DUPN, SWAPN or EXCHANGE read an immediate byte outside 91 to 127. -/
theorem immediateByte_range_of_ok {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    {evm after : Evm fork Nat} (reads : op = .dupn ∨ op = .swapn ∨ op = .exchange)
    (dispatch : instruction fork op = some run) (ok : run evm = .ok after) :
    ¬(90 < (immediateByte evm.code evm.pc).toNat ∧
      (immediateByte evm.code evm.pc).toNat < 128) := by
  intro depth
  rcases reads with rfl | rfl | rfl <;> by_cases glam : Fork.glamsterdam ≤ fork <;>
    simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
      environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
      selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse, glam] at dispatch
  all_goals
    subst dispatch
    obtain ⟨charged, paid, rest⟩ := EthLib.Base.bind_ok_iff.mp ok
    obtain ⟨gas, -, rfl⟩ := chargeGas_eq_ok_iff_charge.mp paid
  · simp [decodeSingle, depth] at rest
  · simp [decodeSingle, depth] at rest
  · simp [decodePair, show 81 < (immediateByte evm.code evm.pc).toNat by omega, depth.2] at rest

/-- A supported opcode that exists at the fork, and is no call, has an instruction of the frame. -/
theorem instruction_isSome_of_meterSupported {op : Op}
    (supported : meterSupported op = true) (noCall : callKindOf op = none)
    (since : op.since ≤ fork) :
    (instruction (Meter := Nat) fork op).isSome := by
  cases op <;> simp only [meterSupported] at supported <;> try contradiction
  all_goals simp only [callKindOf] at noCall
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
    | with_reducible exact dupnStep_bridge
    | with_reducible exact swapnStep_bridge
    | with_reducible exact exchangeStep_bridge

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

/-- The opcode after an opcode position starts in the code or past its end. -/
private theorem next_boundary {code : ByteArray} {pc : Nat} (boundary : pc ∈ opcodePositions code) :
    code.size ≤ nextOpcode code pc ∨ nextOpcode code pc ∈ opcodePositions code := by
  by_cases fits : nextOpcode code pc < code.size
  · exact .inr (mem_opcodePositions_iff.mpr
      (boundaryFrom_next (mem_opcodePositions_iff.mp boundary) fits))
  · exact .inl (Nat.le_of_not_gt fits)

/-- A success at an opcode position moves on to an opcode position, or past the end. -/
private theorem landing {low after : Evm fork Nat} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (boundary : low.pc ∈ opcodePositions low.code)
    (decoded : Op.decode (byteAtOrZero low.code low.pc) = some op)
    (dispatch : instruction fork op = some run) (ok : run low = .ok after) :
    low.code.size ≤ low.pc + opWidth op ∨ low.pc + opWidth op ∈ opcodePositions low.code := by
  by_cases reads : op = .dupn ∨ op = .swapn ∨ op = .exchange
  · have first : nextOpcode low.code low.pc = low.pc + 1 := by
      rcases reads with rfl | rfl | rfl <;> simp [nextOpcode, decoded]
    have second := nextOpcode_succ_of_immediate (immediateByte_range_of_ok reads dispatch ok)
    have width : opWidth op = 2 := by rcases reads with rfl | rfl | rfl <;> rfl
    rw [width]
    rcases next_boundary boundary with h | h
    · rw [first] at h
      exact .inl (by omega)
    · rw [first] at h
      rw [← second]
      exact next_boundary h
  · rw [← nextOpcode_eq decoded (by simpa only [not_or] using reads)]
    exact next_boundary boundary

/-- Checked code with the flags of its scan, at an opcode position when the frame runs. -/
private def MeterReady (evm : Evm fork Nat) : Prop :=
  SupportedCode evm.code = true ∧
    evm.validJumpDestinations = validJumpDestinations evm.code ∧
    (evm.running = true → evm.code.size ≤ evm.pc ∨ evm.pc ∈ opcodePositions evm.code)

/-- A step of checked code keeps its scan, and a normal result can come only from a normal frame.

A running result keeps the error of the frame.

A result whose error is none or a revert has a step under a state gas meter that covers the counter.
-/
private theorem step_meterReady {low after : Evm fork Nat} (h : Step fork low after)
    (ready : MeterReady low) :
    MeterReady after ∧ (after.error = none → low.error = none) ∧
      (after.running = true → after.error = low.error) ∧
      (Carried after.error → ∀ meter : StateGasMeter, low.gas ≤ meter.gasLeft → ∃ m,
        after.gas ≤ m.gasLeft ∧ Step fork (withStateGas low meter) (withStateGas after m)) := by
  obtain ⟨supported, flags, boundary⟩ := ready
  have running := h.running
  -- An exceptional halt stops the frame, and carries an error other than a revert.
  have halted : ∀ e : EvmError, e ≠ .revert →
      MeterReady (exceptionalHalt low e) ∧ ((exceptionalHalt low e).error = none →
        low.error = none) ∧ ((exceptionalHalt low e).running = true →
        (exceptionalHalt low e).error = low.error) ∧ (Carried (exceptionalHalt low e).error →
        ∀ meter : StateGasMeter, low.gas ≤ meter.gasLeft → ∃ m,
          (exceptionalHalt low e).gas ≤ m.gasLeft ∧
          Step fork (withStateGas low meter) (withStateGas (exceptionalHalt low e) m)) :=
    fun e other => ⟨⟨supported, flags, fun h => (by cases h)⟩, fun h => (by cases h),
      fun h => (by cases h), fun carried => by
        rcases carried with h | h <;> simp only [exceptionalHalt, reduceCtorEq,
          Option.some.injEq] at h
        exact absurd h other⟩
  by_cases inside : low.pc < low.code.size
  · have boundary := (boundary running).resolve_left (by omega)
    cases decoded : Op.ofByte fork low.code[low.pc] with
    | none =>
      have hs := step_of_ofByte_eq_none inside decoded
      cases h with
      | next _ hn => rw [hs] at hn; cases hn
      | halt _ failed _ => rw [hs] at failed; cases failed; exact halted _ (by intro h; cases h)
    | some op =>
      have decodedAt : Op.ofByte fork (byteAtOrZero low.code low.pc) = some op := by
        simpa only [byteAtOrZero, dite_eq_left inside] using decoded
      have supportedOp := meterSupported_of_supportedCode supported boundary decodedAt
      cases kindOf : callKindOf op with
      | some kind =>
        -- A call that sends no message lifts by the bridge of its step.
        have hs := step_of_callKindOf inside decoded kindOf
        have never := (callStep_bridge kind (evm := low) (meter := StateGasMeter.start low.gas 0)
          (Nat.le_refl _)).2
        have width : nextOpcode low.code low.pc = low.pc + 1 := by
          have plain : op ≠ .dupn ∧ op ≠ .swapn ∧ op ≠ .exchange := by
            cases op <;> simp_all [callKindOf]
          rw [nextOpcode_eq (Option.filter_eq_some_iff.mp decodedAt).1 plain]
          cases op <;> simp_all [callKindOf, opWidth]
        cases h with
        | halt _ failed _ =>
          rw [hs] at failed
          exact halted _ fun h => never (h ▸ failed)
        | next _ hn =>
          rw [hs] at hn
          have lifted := (callStep_bridge kind (evm := low) (meter := StateGasMeter.start low.gas 0)
            (Nat.le_refl _)).1 _ hn
          obtain ⟨⟨code, sameFlags, pc, normal, keeps⟩, -⟩ := lifted
          refine ⟨⟨by simpa only [code] using supported,
            by simpa only [code, sameFlags] using flags, ?_⟩, normal, keeps, ?_⟩
          · intro runs
            rcases pc runs with hn | hj
            · rw [code, hn, ← width]
              exact next_boundary boundary
            · rw [flags] at hj
              exact .inr (by rw [code]; exact (isValidJumpDest_iff.mp hj).1)
          · intro carried meter below
            obtain ⟨-, highNext⟩ :=
              (callStep_bridge kind (evm := low) (meter := meter) below).1 _ hn
            obtain ⟨b, highOk, m, hb, rfl⟩ := highNext carried
            exact ⟨m, hb, .next running (by
              rw [step_of_callKindOf (evm := withStateGas low meter) inside decoded kindOf]
              exact highOk)⟩
      | none =>
        have since := since_le_of_ofByte_eq_some decoded
        obtain ⟨run, dispatch⟩ := Option.isSome_iff_exists.mp
          (instruction_isSome_of_meterSupported supportedOp kindOf since)
        obtain ⟨highRun, dispatchHigh, bridge⟩ := instruction_bridge supportedOp dispatch
        have hs := step_of_instruction inside decoded dispatch
        -- The run under one counter never fails with a revert.
        have never := (bridge low (StateGasMeter.start low.gas 0) (Nat.le_refl _)).2
        cases h with
        | halt _ failed _ =>
          rw [hs] at failed
          cases ok : run low with
          | ok _ => simp only [ok, Functor.map, Except.map] at failed; cases failed
          | error e =>
            simp only [ok, Functor.map, Except.map] at failed
            cases failed
            exact halted _ fun h => never (h ▸ ok)
        | next _ hn =>
          rw [hs] at hn
          cases ok : run low with
          | error e => simp only [ok, Functor.map, Except.map] at hn; cases hn
          | ok next =>
            simp only [ok, Functor.map, Except.map, Except.ok.injEq,
              StepResult.next.injEq] at hn
            subst next
            obtain ⟨code, sameFlags, pc, normal, keeps⟩ :=
              ((bridge low (StateGasMeter.start low.gas 0) (Nat.le_refl _)).1 after ok).1
            refine ⟨⟨by simpa only [code] using supported,
              by simpa only [code, sameFlags] using flags, ?_⟩, normal, keeps, ?_⟩
            · intro runs
              rcases pc runs with hn | hj
              · rw [code, hn]
                exact landing boundary (Option.filter_eq_some_iff.mp decodedAt).1 dispatch ok
              · rw [flags] at hj
                exact .inr (by rw [code]; exact (isValidJumpDest_iff.mp hj).1)
            · intro carried meter below
              obtain ⟨highNext, highOk, m, hb, rfl⟩ :=
                ((bridge low meter below).1 after ok).2 carried
              refine ⟨m, hb, .next running ?_⟩
              rw [step_of_instruction (evm := withStateGas low meter) inside decoded dispatchHigh,
                highOk]
              rfl
  · have hs := step_of_size_le (evm := low) (by omega)
    cases h with
    | halt _ failed _ => rw [hs] at failed; cases failed
    | next _ hn =>
      rw [hs] at hn
      cases hn
      refine ⟨⟨supported, flags, fun h => by simp [advance] at h⟩, id, fun h => by
        simp [advance] at h, fun _ meter below => ⟨meter, below, .next running ?_⟩⟩
      exact step_of_size_le (evm := withStateGas low meter) (by exact Nat.le_of_not_gt inside)

/-- A normal end of a reach through checked code comes from a normal frame. -/
private theorem normal_of_meterReady {low after : Evm fork Nat}
    (r : Reaches (Step fork) low after) (ready : MeterReady low)
    (normal : after.error = none) : low.error = none := by
  induction r with
  | refl => exact normal
  | step hs _ ih =>
    obtain ⟨nextReady, back, -⟩ := step_meterReady hs ready
    exact back (ih nextReady normal)

/-- A reach through checked code, from a frame that runs only with no error, to a carried frame. -/
private theorem carried_of_meterReady {low after : Evm fork Nat}
    (r : Reaches (Step fork) low after) (ready : MeterReady low)
    (start : low.running = true → low.error = none) (ends : Carried after.error) :
    ∀ meter : StateGasMeter, low.gas ≤ meter.gasLeft → ∃ m, after.gas ≤ m.gasLeft ∧
      Reaches (Step fork) (withStateGas low meter) (withStateGas after m) := by
  induction r with
  | refl => exact fun meter below => ⟨meter, below, .refl _⟩
  | @step _ next _ hs rest ih =>
    obtain ⟨nextReady, -, keeps, lift⟩ := step_meterReady hs ready
    have nextStart : next.running = true → next.error = none := fun runs =>
      (keeps runs).trans (start hs.running)
    -- A frame that steps on runs, so it has no error.
    --
    -- Otherwise it is the last frame.
    have nextCarried : Carried next.error := by
      cases rest with
      | refl => exact ends
      | step further _ => exact .inl (nextStart further.running)
    intro meter below
    obtain ⟨m, hm, first⟩ := lift nextCarried meter below
    obtain ⟨last, hl, remaining⟩ := ih nextReady nextStart ends m hm
    exact ⟨last, hl, .step first remaining⟩

/-- A normal reach through checked code has the same effects under the state gas meter. -/
theorem Reaches.followsMeter {low after : Evm fork Nat} {meter : StateGasMeter}
    (r : Reaches (Step fork) low after) (supported : SupportedCode low.code = true)
    (flags : low.validJumpDestinations = validJumpDestinations low.code)
    (boundary : low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code)
    (normal : after.error = none) (below : low.gas ≤ meter.gasLeft) :
    ∃ m, after.gas ≤ m.gasLeft ∧
      Reaches (Step fork) (withStateGas low meter) (withStateGas after m) :=
  carried_of_meterReady r ⟨supported, flags, fun _ => boundary⟩
    (fun _ => normal_of_meterReady r ⟨supported, flags, fun _ => boundary⟩ normal) (.inl normal)
    meter below

/-- A reach through checked code from a normal frame to a revert has the same effects.

It holds under a state gas meter whose execution gas covers the counter. -/
theorem Reaches.followsMeter_revert {low after : Evm fork Nat} {meter : StateGasMeter}
    (r : Reaches (Step fork) low after) (supported : SupportedCode low.code = true)
    (flags : low.validJumpDestinations = validJumpDestinations low.code)
    (boundary : low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code)
    (start : low.error = none) (reverted : after.error = some .revert)
    (below : low.gas ≤ meter.gasLeft) :
    ∃ m, after.gas ≤ m.gasLeft ∧
      Reaches (Step fork) (withStateGas low meter) (withStateGas after m) :=
  carried_of_meterReady r ⟨supported, flags, fun _ => boundary⟩ (fun _ => start) (.inr reverted)
    meter below

/-- The start of a code is an opcode position, or past the end of an empty code. -/
theorem zero_boundary (code : ByteArray) : code.size ≤ 0 ∨ 0 ∈ opcodePositions code := by
  by_cases empty : code.size = 0
  · exact .inl (by omega)
  · exact .inr (mem_opcodePositions_iff.mpr (.here (by omega)))

/-- A frame of checked code at an opcode position is ready for the state gas meter. -/
theorem At.ready {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {returnData : ByteArray} {low : Evm fork Nat}
    (hat : At code message pc stack memory gas state substate returnData low)
    (supported : SupportedCode code = true)
    (boundary : code.size ≤ pc ∨ pc ∈ opcodePositions code) :
    SupportedCode low.code = true ∧ low.validJumpDestinations = validJumpDestinations low.code ∧
      (low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code) ∧ low.error = none := by
  obtain ⟨hc, hf, -, hp, -, -, -, -, he, -⟩ := hat
  subst hc hp
  exact ⟨supported, hf, boundary, he⟩

/-- A frame under the state gas meter that follows a frame of `P` under one counter. -/
def Covered (P : Evm fork Nat → Prop) (high : Evm fork StateGasMeter) : Prop :=
  ∃ low, P low ∧ FollowsMeter low high

/-- A specification over checked code holds under each state gas meter that covers the counter.

Each frame of the postcondition must stop with no error or with a revert. -/
theorem Spec.covered {P Q : Evm fork Nat → Prop} (h : Spec fork P Q)
    -- Each frame of the precondition has checked code, its flags, an opcode position and no error.
    (ready : ∀ low, P low → SupportedCode low.code = true ∧
      low.validJumpDestinations = validJumpDestinations low.code ∧
      (low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code) ∧ low.error = none)
    (ends : ∀ low, Q low → Carried low.error) :
    Spec (Meter := StateGasMeter) fork (Covered P) (Covered Q) := by
  rintro _ ⟨low, hp, meter, below, rfl⟩
  obtain ⟨supported, flags, boundary, start⟩ := ready low hp
  obtain ⟨stopped, reached, halted, hq⟩ := h low hp
  have lifted : ∃ m, stopped.gas ≤ m.gasLeft ∧
      Reaches (Step fork) (withStateGas low meter) (withStateGas stopped m) := by
    rcases ends stopped hq with normal | reverted
    · exact reached.followsMeter supported flags boundary normal below
    · exact reached.followsMeter_revert supported flags boundary start reverted below
  obtain ⟨m, hm, highReached⟩ := lifted
  exact ⟨_, highReached, halted, stopped, hq, m, hm, rfl⟩

end EthLib.Execution.Evm.Logic
