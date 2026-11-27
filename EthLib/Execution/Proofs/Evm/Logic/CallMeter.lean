module

public import EthLib.Execution.Proofs.Evm.Logic.MeterRun
public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Logic.Callee

/-!
# Proofs: rules for the calls under the state gas meter

The runner meets the assumption that a call to no code ends with no error and no output.

It also meets the assumption that a call runs as a specification of checked callee code says.

Under it, STATICCALL to no code returns no data under the state gas meter of EIP-8037, from Berlin.

A check that it returned 32 bytes then fails closed at every fork from Berlin.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 toAddressMasked byteAtOrZero)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- A frame that ends a covering message to no code ends the message under one counter too. -/
theorem NoCodeSucceeds.lowerMeter {caller : Evm fork Nat} {caller' : Evm fork StateGasMeter}
    {message message' : Message fork} {child : Evm fork StateGasMeter}
    (covers : MessageCovers message message') (h : NoCodeSucceeds caller' message' child) :
    NoCodeSucceeds caller message (lowerMeter child message) := by
  intro hcode htarget hpre
  rw [covers.2] at h
  exact h hcode htarget hpre

/-! ## Callees with a specification of their code -/

/-- The assumption, under the state gas meter, that a call runs as a specification of its code says.

The specification is one under one counter, of the code `code`.

The frame that ends the message follows a stopped frame of the specification. -/
def RunsAsMeter (code : ByteArray) (G : Message fork → TransactionState → Substate → Prop)
    (Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop)
    (caller : Evm fork StateGasMeter) (message : Message fork) (child : Evm fork StateGasMeter) :
    Prop :=
  message.code = code → message.target.isSome →
    ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) →
    precompileAddress fork message = none → G message caller.state caller.substate.child →
    -- The gas of the message fits a word.
    message.gas < 2 ^ 256 →
    -- The frame that ends it is a stopped frame of `Q` with a meter.
    --
    -- A failure is rolled back.
    ∃ stopped meter, Q message caller.state caller.substate.child stopped ∧
      stopped.gas ≤ meter.gasLeft ∧
      child = rollbackOnError caller.state (withStateGas stopped meter)

/-- A frame that ends a covering message as a specification says ends the message under one counter.

It does so up to gas, seen under one counter with its gas capped.

`G` must carry from a message to a covering one. -/
theorem RunsAsMeter.lowerMeter {code : ByteArray}
    {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    (gCovers : ∀ message message' state substate, MessageCovers message message' →
      G message state substate → G message' state substate)
    {caller : Evm fork Nat} {caller' : Evm fork StateGasMeter} {message message' : Message fork}
    {child : Evm fork StateGasMeter} (follows : FollowsMeter caller caller')
    (covers : MessageCovers message message') (fits : message'.gas < 2 ^ 256)
    (h : RunsAsMeter code G Q caller' message' child) :
    RunsAsUpToGas code G Q caller message (lowerMeter child message) := by
  intro hcode htarget noValue noPrecompile hg
  obtain ⟨meter, -, rfl⟩ := follows
  have same := covers.2
  obtain ⟨stopped, meter', hq, below, rfl⟩ := h (by rw [same]; exact hcode)
    (by rw [same]; exact htarget) (by rw [same]; exact noValue) (by rw [same]; exact noPrecompile)
    (gCovers _ _ _ _ covers hg) fits
  refine ⟨message', stopped, covers, hq, ?_, ?_, ?_⟩
  · by_cases failed : stopped.error.isSome <;>
      simp [rollbackOnError, Logic.lowerMeter, withStateGas, failed, GasMeter.rollback]
  · by_cases failed : stopped.error.isSome <;> simp [rollbackOnError, Logic.lowerMeter, failed]
  -- A rollback of a revert credits the spill back, so it keeps the bound on the gas left.
  · have kept : ∀ snapshot,
        stopped.gas ≤ (rollbackOnError snapshot (withStateGas stopped meter')).gas.gasLeft := by
      intro snapshot
      unfold rollbackOnError
      split
      · split
        · exact rollback_followsMeter below
        · exact below
      · exact below
    have := kept (withStateGas caller meter).state
    simp only [Logic.lowerMeter]
    omega

/-- The runner of the state gas meter meets the assumption of a specification of a callee code.

The specification is a triple under one counter, over checked code.

It holds under an assumption `A` on the messages of the callee.

Its stopped frames have no error, or a revert. -/
theorem meets_runsAsMeter {code : ByteArray}
    {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    {A : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {AH : Evm fork StateGasMeter → Message fork → Evm fork StateGasMeter → Prop}
    (supported : SupportedCode code = true)
    -- The specification holds of every message with that code and `G`, from the frame it starts.
    (hspec : ∀ message state substate, message.code = code → G message state substate →
      SpecUnder fork A
        (At code message 0 [] .empty message.gas (startState fork message state) substate
          .empty)
        (Q message state substate))
    (ends : ∀ message state substate stopped, Q message state substate stopped →
      Carried stopped.error)
    -- A frame that ends a covering message of the callee meets `A`, seen under one counter.
    (compat : ∀ caller caller' message message' child, FollowsMeter caller caller' →
      MessageCovers message message' → message'.gas < 2 ^ 256 → AH caller' message' child →
      A caller message (lowerMeter child message))
    -- The runner of the state gas meter must meet `AH` for every bound on the gas of messages.
    (meets : ∀ bound, Meets AH (processRunner (Meter := StateGasMeter) fork bound))
    (bound : Nat) :
    Meets (RunsAsMeter code G Q) (processRunner (Meter := StateGasMeter) fork bound) := by
  refine ⟨fun caller message _ child ran hcode htarget noValue noPrecompile hg fits => ?_,
    (meets_process fork bound).aborts⟩
  obtain ⟨target, ht⟩ := Option.isSome_iff_exists.mp htarget
  simp only [processRunner, ht] at ran
  have covered := (hspec message caller.state caller.substate.child hcode hg).covered
    (fun _ hat => hat.ready supported (zero_boundary code)) (fun _ hq => ends _ _ _ _ hq) compat
  -- The frame that the message starts covers the same frame under one counter.
  have start : Covered (At code message 0 [] .empty message.gas
      (startState fork message caller.state) caller.substate.child .empty)
      (startFrame message (startState fork message caller.state) caller.substate.child
        (GasMeter.start message.gas message.reservoir)) :=
    ⟨_, at_startFrame hcode _ _, ⟨_, Nat.le_refl _, rfl⟩, by
      simpa [startFrame, GasMeter.gasHeld, GasMeter.start, StateGasMeter.gasHeld,
        StateGasMeter.start] using fits⟩
  rcases covered.runFrame (meets message.gas) start
      (Nat.le_of_eq (LawfulGasMeter.gasHeld_start _ _)) with
    ⟨stopped, hrun, low, hq, ⟨meter, below, rfl⟩, -⟩ | ⟨e, hrun, -⟩
  · have h := processMessage_map_val (state := caller.state) noValue noPrecompile hrun
    rw [ran] at h
    exact ⟨low, meter, hq, below, Except.ok.inj h⟩
  · have h := processMessage_map_val (state := caller.state) noValue noPrecompile hrun
    rw [ran] at h
    cases h

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A covering frame right after a byte that decodes to no GAS follows its frame under one counter.
-/
private theorem followsMeter_of_byte {low : Evm fork Nat} {high : Evm fork StateGasMeter}
    {p : Nat} {byte : UInt8} {stack : List U256} {memory' : ByteArray} {gas' : Nat}
    {state' : State.TransactionState} {substate' : Substate} {returnData' : ByteArray}
    (hlt : p < code.size) (hbyte : code[p] = byte) (notGas : Op.decode byte ≠ some .gas)
    (hat : At code message (p + 1) stack memory' gas' state' substate' returnData' low)
    (covers : MeterCovers low high) : FollowsMeter low high := by
  refine covers.followsMeter_of_prev fun _ _ => ?_
  obtain ⟨hc, -, -, hp, -⟩ := hat
  have before : low.pc - 1 = p := by omega
  rw [hc, before, byteAtOrZero, dite_eq_left hlt, hbyte]
  exact notGas

/-- From Berlin, STATICCALL to no code and no precompile returns no data, under the state gas meter.

The code passes the check of the state gas meter, and the call is at an opcode position. -/
theorem staticcall_noCode_meter (hfork : .berlin ≤ fork)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok .empty)
    (hpre : ∀ address, message.txEnv.precompiles (toAddressMasked to) = some address →
      Precompiles.isPrecompile fork address.toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
        gas)
    (supported : SupportedCode code = true) (boundary : pc ∈ opcodePositions code) :
    HoareUnder (Meter := StateGasMeter) fork NoCodeSucceeds
      (Covered (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData))
      -- Under one counter, the caller pushes 1, and its return data is empty.
      (Covered fun after => ∃ childGas state' substate', At code message (pc + 1) (1 :: rest)
        (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
        (gas - ((messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork cold)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          childGas)
        state' substate' .empty after) := by
  refine (HoareUnder.meterCovers (staticcall_noCode hfork hlt hbyte hcode hpre hdepth hcold hgas)
    (fun _ hat => hat.ready supported (.inr boundary))
    (fun _ ⟨_, _, _, hat⟩ => .inl hat.2.2.2.2.2.2.2.2.1)
    fun _ _ _ _ _ _ covers _ h => h.lowerMeter covers).consequence (fun _ hp => hp) ?_
  rintro high ⟨low, ⟨childGas, state', substate', hat⟩, covers⟩
  exact ⟨low, ⟨childGas, state', substate', hat⟩,
    followsMeter_of_byte hlt hbyte (by decide) hat covers, covers.1⟩

/-- From Berlin, RETURNDATASIZE after STATICCALL to no code pushes 0, under the state gas meter.

So a check that the call returned 32 bytes fails closed.

The code passes the check of the state gas meter, and the call is at an opcode position. -/
theorem staticcall_noCode_returndatasize_meter (hfork : .berlin ≤ fork)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {cold : Bool} (hlt : pc + 1 < code.size) (hbyte : code[pc] = 0xfa)
    (hbyteNext : code[pc + 1] = 0x3d)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok .empty)
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
    (hstack : rest.length + 1 < STACK_LIMIT)
    (supported : SupportedCode code = true) (boundary : pc ∈ opcodePositions code) :
    HoareUnder (Meter := StateGasMeter) fork NoCodeSucceeds
      (Covered (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
        memory gas state substate returnData))
      -- Under one counter, the frame compares 32 with 0, and the check fails.
      (Covered fun after => ∃ memory' gas' state' substate', At code message (pc + 2)
        (0 :: 1 :: rest) memory' gas' state' substate' .empty after) := by
  refine (HoareUnder.meterCovers (staticcall_noCode_returndatasize hfork hlt hbyte hbyteNext hcode
    hpre hdepth hcold hgas hgasNext hstack)
    (fun _ hat => hat.ready supported (.inr boundary))
    (fun _ ⟨_, _, _, _, hat⟩ => .inl hat.2.2.2.2.2.2.2.2.1)
    fun _ _ _ _ _ _ covers _ h => h.lowerMeter covers).consequence (fun _ hp => hp) ?_
  rintro high ⟨low, ⟨memory', gas', state', substate', hat⟩, covers⟩
  exact ⟨low, ⟨memory', gas', state', substate', hat⟩,
    followsMeter_of_byte hlt hbyteNext (by decide) hat covers, covers.1⟩

end EthLib.Execution.Evm.Logic
