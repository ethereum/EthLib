module

public import EthLib.Execution.Proofs.Evm.Logic.MeterRun
public import EthLib.Execution.Proofs.Evm.Logic.Call

/-!
# Proofs: rules for the calls under the state gas meter

The runner meets the assumption that a call to no code ends with no error and no output.

Under it, STATICCALL to no code returns no data under the state gas meter of EIP-8037, from Berlin.

A check that it returned 32 bytes then fails closed at every fork from Berlin.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 toAddressMasked byteAtOrZero)
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
    fun _ _ _ _ _ _ covers h => h.lowerMeter covers).consequence (fun _ hp => hp) ?_
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
    fun _ _ _ _ _ _ covers h => h.lowerMeter covers).consequence (fun _ hp => hp) ?_
  rintro high ⟨low, ⟨memory', gas', state', substate', hat⟩, covers⟩
  exact ⟨low, ⟨memory', gas', state', substate', hat⟩,
    followsMeter_of_byte hlt hbyteNext (by decide) hat covers, covers.1⟩

end EthLib.Execution.Evm.Logic
