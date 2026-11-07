module

public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallFlag

/-!
# Proofs: a contract that sends value to an address and returns whether the call succeeded

This example proves the rules for CALL with value.

- At 0, `60 00` four times pushes empty ranges of output and input.
- At 8, `60 00 35` reads the value `v`, the word of call data at offset 0.
- At 11, `60 20 35` reads the address, the word of call data at offset 32.
- At 14, `61 ff ff f1` asks to pass on 65535 gas and calls with the value `v`.
- At 18, `60 00 52 60 20 60 00 f3` returns the word that CALL pushed.

The value is not 0, and the frame may change the state.

When the current account holds less than `v`, the call sends no message and the contract returns 0.

When it holds at least `v`, the call sends `v` with the message.

When the address holds no code and is no precompile, that message ends with no error.

Then, with the runner of messages of the interpreter, the contract returns 1, or the run aborts.

The call pays 9000 for the value, and 25000 more when the callee is dead, by EIP-161.

The price reads from the state whether the callee is dead, so both cases are covered.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Pay

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x35,
  0x60, 0x20, 0x35, 0x61, 0xff, 0xff, 0xf1, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The value that the contract sends: the word of call data at offset 0. -/
def value (data : ByteArray) : U256 := loadWord data 0 32

/-- The address that the contract calls: the word of call data at offset 32. -/
def target (data : ByteArray) : U256 := loadWord data 32 32

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The extra price of the CALL of the code, in the terms of the specification.

It is the access to the address, the price of a new account, and the price of the value. -/
abbrev price (fork : Fork) (state : TransactionState) (message : Message fork) (cold : Bool) :
    Nat :=
  callBaseCost fork cold + callNewAccountCost fork state (toAddressMasked (target message.data))
    (value message.data) + callValueCost fork (value message.data)

/-- The code pushes the operands of CALL, for 27 gas. -/
theorem operands {gas : Nat} (hgas : 27 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 17 [65535, target message.data, value message.data, 0, 0, 0, 0] .empty
        (gas - 27) state substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 2) (stack := [0]) (memory := .empty) (gas := gas - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 4) (stack := [0, 0]) (memory := .empty) (gas := gas - 3 - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 6) (stack := [0, 0, 0]) (memory := .empty)
    (gas := gas - 3 - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 8) (stack := [0, 0, 0, 0]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h6 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 10) (start := 0) (rest := [0, 0, 0, 0])
    (gas := gas - 3 - 3 - 3 - 3 - 3) (by decide) rfl (by omega)
  have h7 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 11) (stack := [value message.data, 0, 0, 0, 0])
    (memory := .empty) (gas := gas - 3 - 3 - 3 - 3 - 3 - 3) (byte := 0x20) (by decide) rfl rfl
    (by omega) (by simp [STACK_LIMIT])
  have h8 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 13) (start := 32)
    (rest := [value message.data, 0, 0, 0, 0]) (gas := gas - 3 - 3 - 3 - 3 - 3 - 3 - 3)
    (by decide) rfl (by omega)
  have h9 := Logic.push (fork := fork) (code := CODE) (message := message) (pc := 14)
    (stack := [target message.data, value message.data, 0, 0, 0, 0]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3) (state := state) (substate := substate) (n := 2)
    (word := 65535) (by decide) (by decide) rfl rfl (by decide) (by omega)
    (by simp [STACK_LIMIT])
  have hg : gas - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 = gas - 27 := by omega
  have h := h1.seq h2 |>.seq h3 |>.seq h4 |>.seq h5 |>.seq h6 |>.seq h7 |>.seq h8 |>.seq h9
  rw [hg] at h
  exact h

/-- The code after CALL writes the word that CALL pushed and returns it, for 15 gas. -/
theorem finish {word : U256} {memory : ByteArray} (hmemory : memory = .empty) {gas : Nat}
    {state : TransactionState} {substate : Substate} (hgas : 15 ≤ gas) :
    Spec fork (At CODE message 18 [word] memory gas state substate)
      (Halted false (wordBytes word) (gas - 15) state substate) := by
  subst hmemory
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 18) (stack := [word]) (memory := .empty) (gas := gas)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h2 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 20)
    (start := 0) (value := word) (rest := []) (memory := .empty) (gas := gas - 3) (state := state)
    (substate := substate) (by decide) rfl (by simp only [hext]; omega)
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [hext, h0, CallFlag.memoryWrite_word] at h2
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 21) (stack := []) (memory := wordBytes word)
    (gas := gas - 3 - (3 + 3)) (byte := 0x20) (by decide) rfl rfl (by omega) (by decide)
  have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 23) (stack := [32]) (memory := wordBytes word)
    (gas := gas - 3 - (3 + 3) - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have hext' : extendMemory (wordBytes word).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have h5 := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 25)
    (start := 0) (size := 32) (rest := []) (memory := wordBytes word)
    (gas := gas - 3 - (3 + 3) - 3 - 3) (state := state) (substate := substate) (by decide) rfl
    (by rw [hext']; exact Nat.zero_le _)
  rw [hext'] at h5
  have hread : memoryReadBytes (memoryExtend (wordBytes word) 0) (0 : U256).toNat
      (32 : U256).toNat = wordBytes word := by
    rw [memoryExtend_zero]
    have h := memoryReadBytes_whole (memory := wordBytes word)
    rwa [size_wordBytes] at h
  have hg : gas - 3 - (3 + 3) - 3 - 3 - 0 = gas - 15 := by omega
  exact Spec.seq (((h1.seq h2).seq h3).seq h4)
    (h5.consequence (fun _ hp => hp) fun _ hq => by rw [hread, hg] at hq; exact hq)

/-- The extendMemory of two empty ranges grows nothing. -/
theorem extendMemory_empty (size : Nat) :
    extendMemory size [((0 : U256), (0 : U256)), ((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
  simp [extendMemory]

/-- When the current account holds less than the value, the contract returns 0.

The call sends no message, so this holds with every runner of messages. -/
theorem spec_low (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    {calleeCode : ByteArray} (hv : value message.data ≠ 0) (hstatic : message.isStatic = false)
    (hbal : (state.getAccount message.currentTarget).balance < value message.data)
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 27 + price fork state message cold + 15 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0)
        (gas - 27 - ((messageCallGas fork (value message.data) (65535 : U256).toNat (gas - 27) 0
          (price fork state message cold)).cost + 0) +
          (messageCallGas fork (value message.data) (65535 : U256).toNat (gas - 27) 0
          (price fork state message cold)).subCall - 15)
        ((state.recordAccountRead (toAddressMasked (target message.data))).recordAccountRead
          message.currentTarget)
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (toAddressMasked (target message.data)) }) := by
  have h := callValueLow (fork := fork) (code := CODE) (message := message) (pc := 17)
    (memory := .empty) (gas := gas - 27) (state := state) (substate := substate) (asked := 65535)
    (to := target message.data) (v := value message.data) (inputStart := 0) (inputSize := 0)
    (outputStart := 0) (outputSize := 0) (rest := []) hfork hglam (by decide) rfl hv hstatic hbal
    hcode hdel hcold (by rw [extendMemory_empty]; show _ + 0 ≤ _; unfold price at hgas; omega)
  rw [extendMemory_empty, memoryExtend_zero] at h
  have htw : fork ≥ .tangerineWhistle := Nat.le_trans (by decide) hfork
  have hle := cost_add_memoryCost_le htw (value := value message.data)
    (gas := (65535 : U256).toNat) (stipend := CALL_STIPEND)
    (enough := show price fork state message cold + 0 ≤ gas - 27 by unfold price at hgas ⊢; omega)
  have hfin := finish (fork := fork) (message := message) (word := 0) (memory := .empty) rfl
    (state := (state.recordAccountRead (toAddressMasked (target message.data))).recordAccountRead
      message.currentTarget)
    (substate := { substate with
      accessedAddresses :=
        substate.accessedAddresses.insert (toAddressMasked (target message.data)) })
    (gas := gas - 27 - ((messageCallGas fork (value message.data) (65535 : U256).toNat (gas - 27) 0
          (price fork state message cold)).cost + 0) +
      (messageCallGas fork (value message.data) (65535 : U256).toNat (gas - 27) 0
          (price fork state message cold)).subCall) (by
        rw [messageCallGas_of_le htw (by unfold price at hgas ⊢; omega)] at hle ⊢
        simp only [CALL_STIPEND] at hle ⊢
        split <;> omega)
  exact Spec.seq ((operands (by omega)).seq h) hfin

/-- What the run with enough value ends with, for an assumption on the callee.

Some caller and some frame that ends the message meet the assumption.

The message runs `calleeCode` at the address, with the value.

The contract returns the word that CALL pushed for that frame.

The gas, the state and the substate are those that CALL gives. -/
def Returned (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop) (calleeCode : ByteArray)
    (cold : Bool) (gas : Nat) (evm : Evm fork Nat) : Prop :=
  ∃ caller msg child, callee caller msg child ∧
    msg.target = some (toAddressMasked (target message.data)) ∧
    msg.codeAddress = some (toAddressMasked (target message.data)) ∧ msg.code = calleeCode ∧
    msg.value = value message.data ∧
    Halted false (wordBytes (CallFlag.flag child))
      (gas - 27 - ((messageCallGas fork (value message.data) (65535 : U256).toNat (gas - 27) 0
          (price fork state message cold)).cost + 0) +
        child.gas - 15)
      (incorporateChild fork caller child).state (incorporateChild fork caller child).substate evm

/-- When the current account holds at least the value, the contract sends it.

It returns the word that CALL pushed, under any assumption on the frame that ends the message. -/
theorem spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {cold : Bool}
    {calleeCode : ByteArray} (hv : value message.data ≠ 0) (hstatic : message.isStatic = false)
    (hbal : value message.data ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 27 + price fork state message cold + 960 ≤ gas) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      (Returned (state := state) (message := message) callee calleeCode cold gas) := by
  have h := callValue (fork := fork) (code := CODE) (message := message) (pc := 17)
    (memory := .empty) (gas := gas - 27) (state := state) (substate := substate) (callee := callee)
    (asked := 65535) (to := target message.data) (v := value message.data) (inputStart := 0)
    (inputSize := 0) (outputStart := 0) (outputSize := 0) (rest := []) hfork hglam (by decide) rfl
    hv hstatic hbal hcode hdel hdepth hcold
    (by rw [extendMemory_empty]; show _ + 0 ≤ _; unfold price at hgas; omega)
  rw [extendMemory_empty, memoryExtend_zero] at h
  refine SpecUnder.seq (HoareUnder.of_hoare (operands (by omega))) (HoareUnder.seq h ?_)
  apply HoareUnder.of_hoare
  rintro evm ⟨caller, msg, child, hcallee, -, -, -, -, -, -, hmtg, hmca, hmcode, -, hmv, -, -,
    hat⟩
  have hleft : 15 ≤ gas - 27 - ((messageCallGas fork (value message.data) (65535 : U256).toNat
      (gas - 27) 0 (price fork state message cold)).cost + 0) + child.gas := by
    have htw : fork ≥ .tangerineWhistle := Nat.le_trans (by decide) hfork
    rw [messageCallGas_of_le htw (by unfold price at hgas ⊢; omega)]
    simp only [maxMessageCallGas]
    unfold price at hgas ⊢
    omega
  have hmem : memoryWrite ByteArray.empty (0 : U256).toNat
      (child.output.extract 0 (min (0 : U256).toNat child.output.size)) = .empty := by
    simp [memoryWrite]
  rw [hmem] at hat
  obtain ⟨stopped, hreach, halted, hq⟩ := finish (fork := fork) (message := message)
    (word := CallFlag.flag child) rfl hleft evm hat
  exact ⟨stopped, hreach, halted, caller, msg, child, hcallee, hmtg, hmca, hmcode, hmv, hq⟩

/-- The contract sends the value to an address with no code and returns 1, or the run aborts.

That holds with the runner of messages of the interpreter.

The address is no precompile, and the current account holds at least the value. -/
theorem runFrame_process_noCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {cold : Bool} (hv : value message.data ≠ 0) (hstatic : message.isStatic = false)
    (hbal : value message.data ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok .empty)
    (hpre : Precompiles.isPrecompile fork
      (toAddressMasked (target message.data)).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 27 + price fork state message cold + 960 ≤ gas) {bound : Nat}
    {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ stopped.error = none ∧ stopped.output = wordBytes 1) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true := by
  have hdel : Fork.pectra ≤ fork → delegatedAddress ByteArray.empty = none := fun _ => by
    simp [delegatedAddress, isValidDelegation, DELEGATION_SIZE]
  rcases (spec (callee := NoCodeSucceeds) hfork hglam hv hstatic hbal hcode hdel hdepth hcold
      hgas).runFrame (meets_process_noCode fork bound) start within with
    ⟨stopped, ran, caller, msg, child, hcallee, hmtg, hmca, hmcode, -, hhalt⟩ | aborted
  · have hnone : child.error = none :=
      hcallee hmcode (by simp [hmtg]) (by simp [precompileAddress, hmca, hpre])
    have hflag : CallFlag.flag child = 1 := by simp [CallFlag.flag, hnone]
    exact .inl ⟨stopped, ran, hhalt.2.1, by rw [hhalt.2.2.1, hflag]⟩
  · exact .inr aborted

end EthLib.Execution.Evm.Logic.Pay
