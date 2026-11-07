module

public import EthLib.Execution.Proofs.Evm.Logic.Call

/-!
# Proofs: a contract that calls an address and returns whether the call succeeded

This example shows that the logic proves a contract that sends a message to arbitrary code.

The contract calls the address in the word of call data at offset 0, with no value and no input.

It asks to pass on 65535 gas, and keeps no output of the callee.

It then returns the word that CALL pushed: 1 when the callee ended with no error, 0 otherwise.

- At 0, `60 00` five times pushes the sizes and starts of output and input, and the value 0.
- At 10, `60 00 35` reads the address, the word of call data at offset 0.
- At 13, `61 ff ff` pushes the gas that the call asks for, 65535.
- At 16, `f1` is CALL.
- At 17, `60 00 52` writes the word that CALL pushed at offset 0 of memory.
- At 20, `60 20 60 00 f3` returns those 32 bytes.

The code of the callee is arbitrary, and it may call this contract again.

So the specification takes an assumption on the frame that ends the message.

It holds for every runner of messages that meets the assumption.

It says nothing of the state and substate after the call beyond what the frame of the callee gives.

With the assumption that always holds, it says only that the contract returns 1 or 0 by that frame.

When the address holds no code and is no precompile, the call ends with no error.

The runner of the interpreter meets that assumption, and then the contract returns 1.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.

The code runs 24 gas before CALL and 15 gas after it.

CALL pays 2600 for a cold address or 100 for a warm one, and the gas it passes on.

The callee gives back the gas it leaves.

Out of scope here: CREATE, a call with value, DELEGATECALL, STATICCALL, and a run out of gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.CallFlag

open EthLib.Base (Fork U256 toAddressMasked)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00,
  0x60, 0x00, 0x35, 0x61, 0xff, 0xff, 0xf1, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The address that the contract calls: the word of call data at offset 0. -/
def target (data : ByteArray) : U256 := loadWord data 0 32

/-- The price of the access to the address: 2600 when cold, 100 when warm. -/
def accessCost (cold : Bool) : Nat := if cold then 2600 else 100

/-- The word that CALL pushes for a frame that ends a message. -/
def flag {Meter : Type} (child : Evm fork Meter) : U256 := if child.error.isNone then 1 else 0

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- The code pushes the operands of CALL, for 24 gas. -/
theorem operands {gas : Nat} (hgas : 24 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 16 [65535, target message.data, 0, 0, 0, 0, 0] .empty (gas - 24) state
        substate) := by
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
  have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 10) (stack := [0, 0, 0, 0, 0]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h7 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 12) (start := 0) (rest := [0, 0, 0, 0, 0])
    (gas := gas - 3 - 3 - 3 - 3 - 3 - 3) (by decide) rfl (by omega)
  have h8 := Logic.push (fork := fork) (code := CODE) (message := message) (pc := 13)
    (stack := [loadWord message.data 0 32, 0, 0, 0, 0, 0]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3 - 3 - 3 - 3) (state := state) (substate := substate) (n := 2)
    (word := 65535) (by decide) (by decide) rfl rfl (by decide) (by omega)
    (by simp [STACK_LIMIT])
  have hg : gas - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 = gas - 24 := by omega
  have h := (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8)
  rw [hg] at h
  exact h

/-- The memory after the MSTORE of the code: the word on 32 bytes. -/
theorem memoryWrite_word (word : U256) :
    memoryWrite (memoryExtend .empty 32) 0 (wordBytes word) = wordBytes word :=
  memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])

/-- The code after CALL writes the word that CALL pushed and returns it, for 15 gas. -/
theorem finish {word : U256} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    (hgas : 15 ≤ gas) :
    Spec fork (At CODE message 17 [word] .empty gas state substate)
      (Halted false (wordBytes word) (gas - 15) state substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 17) (stack := [word]) (memory := .empty) (gas := gas)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  -- Memory grows from no word to one word, for 3 gas.
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h2 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 19)
    (start := 0) (value := word) (rest := []) (memory := .empty) (gas := gas - 3) (state := state)
    (substate := substate) (by decide) rfl (by simp only [hext]; omega)
  rw [hext] at h2
  have h2' : Hoare fork (At CODE message 19 [0, word] .empty (gas - 3) state substate)
      (At CODE message 20 [] (wordBytes word) (gas - 3 - (3 + 3)) state substate) := by
    have hm := memoryWrite_word word
    have h0 : (0 : U256).toNat = 0 := rfl
    rw [h0, hm] at h2
    exact h2
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 20) (stack := []) (memory := wordBytes word)
    (gas := gas - 3 - (3 + 3)) (byte := 0x20) (by decide) rfl rfl (by omega) (by decide)
  have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 22) (stack := [32]) (memory := wordBytes word)
    (gas := gas - 3 - (3 + 3) - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  -- Memory already holds the word, so it does not grow.
  have hext' : extendMemory (wordBytes word).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have h5 := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 24)
    (start := 0) (size := 32) (rest := []) (memory := wordBytes word)
    (gas := gas - 3 - (3 + 3) - 3 - 3) (state := state) (substate := substate) (by decide) rfl
    (by rw [hext']; exact Nat.zero_le _)
  have hread : memoryReadBytes (memoryExtend (wordBytes word) 0) (0 : U256).toNat
      (32 : U256).toNat = wordBytes word := by
    rw [memoryExtend_zero]
    have := memoryReadBytes_whole (memory := wordBytes word)
    rwa [size_wordBytes] at this
  rw [hext'] at h5
  have hg : gas - 3 - (3 + 3) - 3 - 3 - 0 = gas - 15 := by omega
  have h := (((h1.seq h2').seq h3).seq h4)
  exact Spec.seq h (h5.consequence (fun _ hp => hp) fun _ hq => by
    rw [hread, hg] at hq
    exact hq)

/-- What the run ends with, for an assumption on the callee and the code `calleeCode` it runs.

Some caller and some frame that ends the message meet the assumption.

The message calls the address and runs `calleeCode`, with no value and no data, one frame deeper.

The contract returns the word that CALL pushed for that frame.

The gas, the state and the substate are those that CALL gives. -/
def Returned (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop) (calleeCode : ByteArray)
    (cold : Bool) (gas : Nat) (evm : Evm fork Nat) : Prop :=
  ∃ caller msg child, callee caller msg child ∧ child.gas ≤ msg.gas ∧
    caller.state =
      (state.recordAccountRead (toAddressMasked (target message.data))).recordAccountRead
        message.currentTarget ∧
    msg.gas = (messageCallGas fork 0 (65535 : U256).toNat (gas - 24) 0 (accessCost cold)).subCall ∧
    msg.currentTarget = toAddressMasked (target message.data) ∧
    msg.target = some (toAddressMasked (target message.data)) ∧
    msg.codeAddress = some (toAddressMasked (target message.data)) ∧ msg.code = calleeCode ∧
    msg.value = 0 ∧ msg.data = .empty ∧ msg.depth = message.depth + 1 ∧
    Halted false (wordBytes (flag child))
      (gas - 24 - (messageCallGas fork 0 (65535 : U256).toNat (gas - 24) 0 (accessCost cold)).cost +
        child.gas - 15)
      (incorporateChild fork caller child).state (incorporateChild fork caller child).substate evm

/-- The specification of the code, under any assumption on the frame that ends its message.

The address it calls holds the code `calleeCode`, which is no delegation.

The access to that address is cold when the transaction has not accessed it yet.

The frame must have at least 24 gas, the access, and 960 gas, from Berlin to before Glamsterdam.

Of that, the call passes on at most all but one 64th, so the code keeps the 15 gas it needs. -/
theorem spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {cold : Bool}
    {calleeCode : ByteArray}
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 24 + accessCost cold + 960 ≤ gas) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      (Returned (state := state) (message := message) callee calleeCode cold gas) := by
  have hcall := Logic.call (fork := fork) (code := CODE) (message := message) (pc := 16)
    (memory := .empty) (gas := gas - 24) (state := state) (substate := substate) (callee := callee)
    (asked := 65535) (to := target message.data) (inputStart := 0) (outputStart := 0) (rest := [])
    hfork hglam (by decide) rfl hcode hdel hdepth hcold
    (by cases cold <;> simp only [accessCost, ite_true, Bool.false_eq_true, ite_false] at hgas ⊢ <;>
      omega)
  refine SpecUnder.seq (HoareUnder.of_hoare (operands (by omega))) (HoareUnder.seq hcall ?_)
  apply HoareUnder.of_hoare
  rintro evm
    ⟨caller, msg, child, hcallee, hle, hst, hss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv, hmdep,
      -, hat⟩
  have hleft : 15 ≤ gas - 24 -
      (messageCallGas fork 0 (65535 : U256).toNat (gas - 24) 0 (if cold then 2600 else 100)).cost +
        child.gas := by
    have htw : fork ≥ .tangerineWhistle := Nat.le_trans (by decide) hfork
    cases cold <;> simp only [accessCost, ite_true, Bool.false_eq_true, ite_false] at hgas ⊢ <;>
      rw [messageCallGas_of_le htw (by omega)] <;> simp only [maxMessageCallGas] <;> omega
  obtain ⟨stopped, hreach, halted, hq⟩ := finish (fork := fork) (message := message)
    (word := flag child) hleft evm hat
  exact ⟨stopped, hreach, halted, caller, msg, child, hcallee, hle, hst, hmg, hmt, hmtg, hmca,
    hmcode, hmv, hmd, hmdep, hq⟩

/-- The loop of the interpreter runs the code to its specification, or the run aborts.

It holds for every runner of messages that meets the assumption.

The run aborts only when the runner fails on the message, with an error that aborts the run.

The bound on the gas of messages is any bound that holds the gas of the frame. -/
theorem runFrame_spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {cold : Bool}
    {calleeCode : ByteArray}
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 24 + accessCost cold + 960 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} (meets : Meets callee runChild)
    {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Returned (state := state) (message := message) callee calleeCode cold gas stopped) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e ∧
      e.aborts = true :=
  (spec hfork hglam hcode hdel hdepth hcold hgas).runFrame meets start within

/-- With the runner of messages of the interpreter, the code returns 1 or 0, or the run aborts.

That runner runs the message of the call, and meets the assumption that always holds.

The word is 1 when the frame of the callee ends with no error. -/
theorem runFrame_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    {calleeCode : ByteArray}
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 24 + accessCost cold + 960 ≤ gas) {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound
        (fun caller message _ => match message.target with
          | some _ => processMessage fork message caller.state caller.substate.child
          | none => processCreateMessage fork message caller.state caller.substate.child)
        evm within = .ok stopped ∧
      Returned (state := state) (message := message) (fun _ _ _ => True) calleeCode cold gas
        stopped) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound
        (fun caller message _ => match message.target with
          | some _ => processMessage fork message caller.state caller.substate.child
          | none => processCreateMessage fork message caller.state caller.substate.child)
        evm within = .error e ∧ e.aborts = true :=
  runFrame_spec hfork hglam hcode hdel hdepth hcold hgas (meets_process fork bound) start within

/-- When the address holds no code and is no precompile, the contract returns the word 1.

That holds under the assumption that a call to no code ends with no error. -/
theorem spec_noCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok .empty)
    (hpre : Precompiles.isPrecompile fork
      (toAddressMasked (target message.data)).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 24 + accessCost cold + 960 ≤ gas) :
    SpecUnder fork NoCodeSucceeds (At CODE message 0 [] .empty gas state substate)
      fun evm => Returned (state := state) (message := message) NoCodeSucceeds .empty cold gas evm ∧
        evm.output = wordBytes 1 := by
  have hdel : Fork.pectra ≤ fork → delegatedAddress ByteArray.empty = none := fun _ => by
    simp [delegatedAddress, isValidDelegation, DELEGATION_SIZE]
  apply (spec hfork hglam hcode hdel hdepth hcold hgas).consequence (fun _ hp => hp)
  intro evm hr
  refine ⟨hr, ?_⟩
  obtain ⟨_, msg, child, hcallee, -, -, -, -, htarget, hca, hmcode, -, -, -, hhalt⟩ := hr
  have hnone : child.error = none :=
    hcallee hmcode (by simp [htarget]) (by simp [precompileAddress, hca, hpre])
  have hflag : flag child = 1 := by simp [flag, hnone]
  rw [hhalt.2.2.1, hflag]

/-- With the runner of messages of the interpreter, a call to no code makes the code return 1.

The address holds no code and is no precompile, and the run may still abort. -/
theorem runFrame_process_noCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {cold : Bool}
    (hcode : state.getCode (state.getAccount (toAddressMasked (target message.data))).codeHash =
      .ok .empty)
    (hpre : Precompiles.isPrecompile fork
      (toAddressMasked (target message.data)).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 24 + accessCost cold + 960 ≤ gas) {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound
        (fun caller message _ => match message.target with
          | some _ => processMessage fork message caller.state caller.substate.child
          | none => processCreateMessage fork message caller.state caller.substate.child)
        evm within = .ok stopped ∧ stopped.output = wordBytes 1) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound
        (fun caller message _ => match message.target with
          | some _ => processMessage fork message caller.state caller.substate.child
          | none => processCreateMessage fork message caller.state caller.substate.child)
        evm within = .error e ∧ e.aborts = true := by
  rcases (spec_noCode hfork hglam hcode hpre hdepth hcold hgas).runFrame
      (meets_process_noCode fork bound) start within with ⟨stopped, hrun, -, hout⟩ | aborted
  · exact .inl ⟨stopped, hrun, hout⟩
  · exact .inr aborted

end EthLib.Execution.Evm.Logic.CallFlag
