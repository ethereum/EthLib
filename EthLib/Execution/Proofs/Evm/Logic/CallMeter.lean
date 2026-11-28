module

public import EthLib.Execution.Proofs.Evm.Logic.MeterRun
public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Region
public import EthLib.Execution.Proofs.Evm.Gas.Memory

/-!
# Proofs: rules for the calls under the state gas meter

The runner meets the assumption that a call to no code ends with no error and no output.

Under it, STATICCALL to no code returns no data under the state gas meter of EIP-8037, from Berlin.

A check that it returned 32 bytes then fails closed at every fork from Berlin.

The runner also meets the assumption that a call runs as the specification of its code says.

Under that one, STATICCALL to a callee that returns a word leaves 32 and 1 on the stack.

The word is then in memory and in the return data.
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

/-- A triple under the assumption of a callee specification, over checked code, carries further.

It holds under the state gas meter, under the assumption of that specification there.

Its frames of the postcondition must have no error, or a revert.

`G` must carry from a message to a covering one. -/
theorem HoareUnder.runsAsMeter {code : ByteArray}
    {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    {P R : Evm fork Nat → Prop} (h : HoareUnder fork (RunsAsUpToGas code G Q) P R)
    -- Each frame of the precondition has checked code, its flags, an opcode position and no error.
    (ready : ∀ low, P low → SupportedCode low.code = true ∧
      low.validJumpDestinations = validJumpDestinations low.code ∧
      (low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code) ∧ low.error = none)
    (ends : ∀ low, R low → Carried low.error)
    (gCovers : ∀ message message' state substate, MessageCovers message message' →
      G message state substate → G message' state substate) :
    HoareUnder (Meter := StateGasMeter) fork (RunsAsMeter code G Q) (Covered P)
      fun high => ∃ low, R low ∧ MeterCovers low high :=
  HoareUnder.meterCovers h ready ends fun _ _ _ _ _ follows covers fits h =>
    h.lowerMeter gCovers follows covers fits

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

/-! ## A callee that returns a word -/

/-- From Berlin, STATICCALL then RETURNDATASIZE, to a callee whose specification returns a word.

The callee code has a specification under one counter.

Its stopped frames have no error, and the 32 bytes of `word` as output.

So the call pushes 1 and RETURNDATASIZE pushes 32.

The output range and the return data hold `word`.

The callee is no precompile and, from Pectra, no delegation.

The output range has 32 bytes, and memory has a size that is a multiple of 32. -/
theorem staticcall_returnsWord (hfork : .berlin ≤ fork) {calleeCode : ByteArray}
    {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop} {word : U256}
    {asked to inputStart inputSize outputStart : U256} {rest : List U256}
    {cold : Bool} (hlt : pc + 1 < code.size) (hbyte : code[pc] = 0xfa)
    (hbyteNext : code[pc + 1] = 0x3d)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hpre : ∀ address, message.txEnv.precompiles (toAddressMasked to) = some address →
      Precompiles.isPrecompile fork address.toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    -- The output range has 32 bytes.
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost ≤ gas)
    -- The gas left after the call covers RETURNDATASIZE, before the callee gives any back.
    (hgasNext : 2 ≤ gas - ((messageCallGas fork 0 asked.toNat gas
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost
      (callBaseCost fork cold)).cost +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost))
    (hstack : rest.length + 1 < STACK_LIMIT) (hmod : memory.size % 32 = 0)
    -- `G` holds of a static message from the current account to `to`, with the input as data.
    (hG : ∀ msg state' substate', msg.caller = message.currentTarget →
      msg.currentTarget = toAddressMasked to → msg.isStatic = true →
      msg.depth = message.depth + 1 →
      msg.gas = (messageCallGas fork 0 asked.toNat gas
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost
        (callBaseCost fork cold)).subCall →
      msg.data = memoryReadBytes (memoryExtend memory
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy)
        inputStart.toNat inputSize.toNat →
      -- The message keeps the block and the transaction, carries no value, and runs that code.
      msg.blockEnv = message.blockEnv → msg.txEnv = message.txEnv → msg.value = 0 →
      msg.code = calleeCode →
      -- The state is the one of the caller, which has read `to` and its own account.
      state' = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
        message.currentTarget →
      -- The substate starts from the one of the caller, which has accessed `to`.
      substate' = ({ substate with
        accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } :
          Substate).child →
      G msg state' substate')
    -- Each stopped frame of the specification has no error, and the 32 bytes of `word` as output.
    (hQ : ∀ msg state' substate' stopped, Q msg state' substate' stopped →
      stopped.error = none ∧ stopped.output = wordBytes word) :
    HoareUnder fork (RunsAsUpToGas calleeCode G Q)
      (At code message pc (asked :: to :: inputStart :: inputSize :: outputStart :: 32 :: rest)
        memory gas state substate returnData)
      -- The stack holds 32 and 1, and the output range holds `word`.
      fun after => ∃ childGas state' substate', At code message (pc + 2)
        (32 :: 1 :: rest)
        (memoryWrite (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy)
          outputStart.toNat (wordBytes word))
        -- The frame keeps at least the gas left after the call, and pays 2 for RETURNDATASIZE.
        (gas - ((messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost
          (callBaseCost fork cold)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost) +
          childGas - 2)
        state' substate' (wordBytes word) after ∧
        Holds (memoryWrite (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy)
          outputStart.toNat (wordBytes word)) outputStart.toNat (wordBytes word) := by
  subst hcold
  have h := callKindRoute (kind := .staticcall) (route := none) (asked := asked)
    (inputStart := inputStart) (inputSize := inputSize) (outputStart := outputStart)
    (outputSize := 32) (memory := memory) (gas := gas) (state := state)
    (substate := substate) (callee := RunsAsUpToGas calleeCode G Q) (rest := rest)
    (returnData := returnData) hfork (by omega) hbyte
    (ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)) instruction_staticcall
    (messageInstruction_staticcall (Nat.le_trans (by decide) hfork)) hcode
    hdel hdepth (by simpa only [routeCost, Nat.add_zero] using hgas)
  -- Memory holds the word in the output range, which memory grows to hold.
  have fit : outputStart.toNat + (wordBytes word).size ≤ memory.size +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy := by
    have h := le_ceil32_add_expandBy memory.size [(inputStart, inputSize), (outputStart, 32)]
      (outputStart, 32) (by simp) (by simp)
    rw [ceil32_of_mod hmod] at h
    rw [size_wordBytes]
    exact h
  -- After the call, the frame holds the word in the output range and as return data.
  have called : HoareUnder fork (RunsAsUpToGas calleeCode G Q)
      (At code message pc (asked :: to :: inputStart :: inputSize :: outputStart :: 32 :: rest)
        memory gas state substate returnData)
      fun after => ∃ x : Nat × TransactionState × Substate, At code message (pc + 1) (1 :: rest)
        (memoryWrite (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy)
          outputStart.toNat (wordBytes word))
        (gas - ((messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost
          (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)))).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost) +
          x.1)
        x.2.1 x.2.2 (wordBytes word) after := by
    refine h.toUnder.consequence (fun _ h => h) ?_
    rintro after ⟨caller, msg, child,
      ⟨s1, s2, m1, -, m2, m3, mt, mca, mc, -, md, m5, -, m6, m7, mb, mtx⟩, hcallee, -, hat⟩
    -- The message runs the code of `to`, which is no precompile.
    have hp : precompileAddress fork msg = none := by
      unfold precompileAddress
      rw [mca, mtx]
      simp only [routeAddr, Option.bind_some]
      cases h : message.txEnv.precompiles (toAddressMasked to) with
      | none => rfl
      | some address => simp [hpre address h]
    obtain ⟨_, stopped, -, hq, hchild, -, -⟩ := hcallee (by simpa [routeCode] using mc)
      (by simp [mt]) (by simp [m5]) hp
      (hG _ _ _ (by simpa using m2) (by simpa using m3) (by simpa using m7) m6
        (by simpa only [routeCost, Nat.add_zero] using m1) md mb mtx (by simpa using m5)
        (by simpa [routeCode] using mc) (by simpa [routeState] using s1)
        (by rw [s2]; rfl))
    obtain ⟨herr, hout⟩ := hQ _ _ _ _ hq
    -- The callee stops with no error, so the frame that ends the message is its stopped frame.
    have cerr : child.error = none := by
      rw [hchild]
      simp [rollbackOnError, herr]
    have cout : child.output = wordBytes word := by
      rw [hchild]
      simp [rollbackOnError, herr, hout]
    refine ⟨(child.gas, (incorporateChild fork caller child).state,
      (incorporateChild fork caller child).substate), ?_⟩
    simp only [routeCost, Nat.add_zero, cerr, cout, Option.isNone_none, ite_true,
      size_wordBytes] at hat
    rw [show (32 : U256).toNat = 32 from rfl, Nat.min_self,
      show (wordBytes word).extract 0 32 = wordBytes word by
      rw [← size_wordBytes word]
      exact ByteArray.extract_zero_size] at hat
    exact hat
  -- Then RETURNDATASIZE pushes the 32 bytes of the return data.
  refine called.seq (HoareUnder.of_exists (fun _ h => h) fun ⟨g, st, ss⟩ => ?_)
  refine (HoareUnder.of_hoare (returndatasize (Nat.le_trans (by decide) hfork) hlt hbyteNext
    (by omega) (by simpa using hstack))).consequence (fun _ h => h) ?_
  intro after h
  exact ⟨g, st, ss, by simpa [size_wordBytes] using h, holds_extend_write fit⟩

/-- From Berlin, the rule of a callee that returns a word, under the state gas meter.

The code of the frame passes the check of the state gas meter.

The callee runs as its specification says, under that meter (`RunsAsMeter`).

`G` must carry from a message to a covering one. -/
theorem staticcall_returnsWord_meter (hfork : .berlin ≤ fork) {calleeCode : ByteArray}
    {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop} {word : U256}
    {asked to inputStart inputSize outputStart : U256} {rest : List U256}
    {cold : Bool} (hlt : pc + 1 < code.size) (hbyte : code[pc] = 0xfa)
    (hbyteNext : code[pc + 1] = 0x3d)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hpre : ∀ address, message.txEnv.precompiles (toAddressMasked to) = some address →
      Precompiles.isPrecompile fork address.toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : (callBaseCost fork cold) +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost ≤ gas)
    -- The gas left after the call covers RETURNDATASIZE, before the callee gives any back.
    (hgasNext : 2 ≤ gas - ((messageCallGas fork 0 asked.toNat gas
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost
      (callBaseCost fork cold)).cost +
      (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost))
    (hstack : rest.length + 1 < STACK_LIMIT) (hmod : memory.size % 32 = 0)
    (hG : ∀ msg state' substate', msg.caller = message.currentTarget →
      msg.currentTarget = toAddressMasked to → msg.isStatic = true →
      msg.depth = message.depth + 1 →
      msg.gas = (messageCallGas fork 0 asked.toNat gas
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost
        (callBaseCost fork cold)).subCall →
      msg.data = memoryReadBytes (memoryExtend memory
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy)
        inputStart.toNat inputSize.toNat →
      -- The message keeps the block and the transaction, carries no value, and runs that code.
      msg.blockEnv = message.blockEnv → msg.txEnv = message.txEnv → msg.value = 0 →
      msg.code = calleeCode →
      -- The state is the one of the caller, which has read `to` and its own account.
      state' = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
        message.currentTarget →
      -- The substate starts from the one of the caller, which has accessed `to`.
      substate' = ({ substate with
        accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } :
          Substate).child →
      G msg state' substate')
    (hQ : ∀ msg state' substate' stopped, Q msg state' substate' stopped →
      stopped.error = none ∧ stopped.output = wordBytes word)
    (gCovers : ∀ message message' state substate, MessageCovers message message' →
      G message state substate → G message' state substate)
    (supported : SupportedCode code = true) (boundary : pc ∈ opcodePositions code) :
    HoareUnder (Meter := StateGasMeter) fork (RunsAsMeter calleeCode G Q)
      (Covered (At code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: 32 :: rest)
        memory gas state substate returnData))
      -- Under one counter, the stack holds 32 and 1, and the output range holds `word`.
      (Covered fun after => ∃ childGas state' substate', At code message (pc + 2)
        (32 :: 1 :: rest)
        (memoryWrite (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy)
          outputStart.toNat (wordBytes word))
        -- The frame keeps at least the gas left after the call, and pays 2 for RETURNDATASIZE.
        (gas - ((messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost
          (callBaseCost fork cold)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).cost) +
          childGas - 2)
        state' substate' (wordBytes word) after ∧
        Holds (memoryWrite (memoryExtend memory
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, 32)]).expandBy)
          outputStart.toNat (wordBytes word)) outputStart.toNat (wordBytes word)) := by
  refine ((staticcall_returnsWord hfork hlt hbyte hbyteNext hcode hdel hpre hdepth hcold hgas
    hgasNext hstack hmod hG hQ).runsAsMeter (fun _ hat => hat.ready supported (.inr boundary))
    (fun _ ⟨_, _, _, hat, _⟩ => .inl hat.2.2.2.2.2.2.2.2.1) gCovers).consequence
    (fun _ hp => hp) ?_
  rintro high ⟨low, ⟨childGas, state', substate', hat, holds⟩, covers⟩
  exact ⟨low, ⟨childGas, state', substate', hat, holds⟩,
    followsMeter_of_byte hlt hbyteNext (by decide) hat covers, covers.1⟩

end EthLib.Execution.Evm.Logic
