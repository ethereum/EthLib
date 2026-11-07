module

public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallFlag
public import EthLib.Execution.Proofs.Evm.Logic.Examples.SumLoop

/-!
# Proofs: a contract that sends a word to a callee and reads back what it returns

This example proves a call with call data and return data, through the runner of the interpreter.

The callee returns the first word of its call data.

- At 0, `60 00 35` reads the word of call data at offset 0.
- At 3, `60 00 52` writes it at offset 0 of memory.
- At 6, `60 20 60 00 f3` returns those 32 bytes.

The caller sends the first word of its own call data to the address in its second word.

- At 0, `60 00 35 60 00 52` writes the word of call data at offset 0 at offset 0 of memory.
- At 6, `60 40 60 20` pushes an output range of 64 bytes at 32.
- At 10, `60 20 60 00 60 00` pushes an input range of 32 bytes at 0, and the value 0.
- At 16, `60 20 35` reads the address, the word of call data at offset 32.
- At 19, `61 ff ff f1` asks to pass on 65535 gas and calls.
- At 23, `60 40 60 20 f3` returns the 64 bytes of memory from offset 32.

The output range holds 64 bytes, and the callee returns 32.

So CALL writes the 32 bytes of the callee at 32, and the next 32 bytes stay zero.

The caller then returns the word it sent, then 32 zero bytes.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.CallEcho

open EthLib.Base (Fork U256 toAddressMasked byteAt eq_of_byteAt)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the callee, which returns the first word of its call data. -/
def ECHO : ByteArray := ⟨#[0x60, 0x00, 0x35, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The bytecode of the caller. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x35, 0x60, 0x00, 0x52, 0x60, 0x40, 0x60, 0x20, 0x60,
  0x20, 0x60, 0x00, 0x60, 0x00, 0x60, 0x20, 0x35, 0x61, 0xff, 0xff, 0xf1, 0x60, 0x40, 0x60, 0x20,
  0xf3]⟩

/-- The first word of a call data. -/
def word (data : ByteArray) : U256 := loadWord data 0 32

/-- The address that the caller calls: the second word of its call data. -/
def target (data : ByteArray) : U256 := loadWord data 32 32

/-- A read of a whole word of memory from offset 0 gives that word. -/
theorem memoryReadBytes_wordBytes (x : U256) :
    memoryReadBytes (wordBytes x) 0 32 = wordBytes x := by
  have h := memoryReadBytes_whole (memory := wordBytes x)
  rwa [size_wordBytes] at h

/-- The code of the callee returns the first word of its call data, for 21 gas. -/
theorem echo {message : Message fork} {state : TransactionState} {substate : Substate}
    {gas : Nat} (hgas : 21 ≤ gas) :
    Spec fork (At ECHO message 0 [] .empty gas state substate)
      (Halted false (wordBytes (word message.data)) (gas - 21) state substate) := by
  have h1 := push1 (code := ECHO) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := calldataload (fork := fork) (code := ECHO) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 2) (start := 0) (rest := [])
    (gas := gas - 3) (by decide) rfl (by omega)
  have h3 := push1 (code := ECHO) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 3) (stack := [word message.data]) (memory := .empty)
    (gas := gas - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h4 := Logic.mstore (fork := fork) (code := ECHO) (message := message) (pc := 5)
    (start := 0) (value := word message.data) (rest := []) (memory := .empty)
    (gas := gas - 3 - 3 - 3) (state := state) (substate := substate) (by decide) rfl
    (by simp only [hext]; omega)
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [hext, h0, CallFlag.memoryWrite_word] at h4
  have h5 := push1 (code := ECHO) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 6) (stack := []) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3)) (byte := 0x20) (by decide) rfl rfl (by omega) (by decide)
  have h6 := push1 (code := ECHO) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 8) (stack := [32]) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3) (byte := 0x00) (by decide) rfl rfl (by omega)
    (by decide)
  have hext' : extendMemory (wordBytes (word message.data)).size [((0 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have h7 := Logic.«return» (fork := fork) (code := ECHO) (message := message) (pc := 10)
    (start := 0) (size := 32) (rest := []) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3) (state := state) (substate := substate)
    (by decide) rfl (by rw [hext']; exact Nat.zero_le _)
  rw [hext'] at h7
  have hread : memoryReadBytes (memoryExtend (wordBytes (word message.data)) 0) (0 : U256).toNat
      (32 : U256).toNat = wordBytes (word message.data) := by
    rw [memoryExtend_zero]
    exact memoryReadBytes_wordBytes _
  have hg : gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 0 = gas - 21 := by omega
  exact Spec.seq (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6)
    (h7.consequence (fun _ hp => hp) fun _ hq => by rw [hread, hg] at hq; exact hq)

/-- The assumption that a call to the code of the callee returns the first word of its data. -/
abbrev Callee : Evm fork Nat → Message fork → Evm fork Nat → Prop :=
  RunsAs ECHO (fun message _ _ => 21 ≤ message.gas) fun message state substate =>
    Halted false (wordBytes (word message.data)) (message.gas - 21) (startState fork message state)
      substate

/-- The runner of the interpreter meets the assumption, for every bound. -/
theorem meets (bound : Nat) : Meets (Callee (fork := fork)) (processRunner fork bound) :=
  meets_of_spec (fun _ _ _ _ hg => echo hg) bound

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The caller writes the first word of its call data to memory and pushes the operands of CALL.

That takes 39 gas. -/
theorem operands {gas : Nat} (hgas : 39 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 22 [65535, target message.data, 0, 0, 32, 32, 64]
        (wordBytes (word message.data)) (gas - 39) state substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 2) (start := 0) (rest := [])
    (gas := gas - 3) (by decide) rfl (by omega)
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 3) (stack := [word message.data]) (memory := .empty)
    (gas := gas - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h4 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 5)
    (start := 0) (value := word message.data) (rest := []) (memory := .empty)
    (gas := gas - 3 - 3 - 3) (state := state) (substate := substate) (by decide) rfl
    (by simp only [hext]; omega)
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [hext, h0, CallFlag.memoryWrite_word] at h4
  have h5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 6) (stack := []) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3)) (byte := 0x40) (by decide) rfl rfl (by omega) (by decide)
  have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 8) (stack := [64]) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3) (byte := 0x20) (by decide) rfl rfl (by omega)
    (by decide)
  have h7 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 10) (stack := [32, 64]) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3) (byte := 0x20) (by decide) rfl rfl (by omega)
    (by decide)
  have h8 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 12) (stack := [32, 32, 64])
    (memory := wordBytes (word message.data)) (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h9 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 14) (stack := [0, 32, 32, 64])
    (memory := wordBytes (word message.data)) (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h10 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 16) (stack := [0, 0, 32, 32, 64])
    (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 3 - 3) (byte := 0x20) (by decide) rfl rfl
    (by omega) (by decide)
  have h11 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes (word message.data)) (pc := 18) (start := 32)
    (rest := [0, 0, 32, 32, 64]) (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 3 - 3 - 3)
    (by decide) rfl (by omega)
  have h12 := Logic.push (fork := fork) (code := CODE) (message := message) (pc := 19)
    (stack := [loadWord message.data 32 32, 0, 0, 32, 32, 64])
    (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 3 - 3 - 3 - 3) (state := state)
    (substate := substate) (n := 2) (word := 65535) (by decide) (by decide) rfl rfl (by decide)
    (by omega) (by simp [STACK_LIMIT])
  have hg : gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 = gas - 39 := by omega
  have h := (((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq
    h10).seq h11).seq h12)
  rw [hg] at h
  exact h

/-- After CALL, the caller returns the 64 bytes of its memory from offset 32, for 6 gas. -/
theorem finish {flag : U256} {memory : ByteArray} (hsize : memory.size = 96) {gas : Nat}
    {state : TransactionState} {substate : Substate} (hgas : 6 ≤ gas) :
    Spec fork (At CODE message 23 [flag] memory gas state substate)
      (Halted false (memoryReadBytes memory 32 64) (gas - 6) state substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 23) (stack := [flag]) (memory := memory) (gas := gas)
    (byte := 0x40) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have h2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 25) (stack := [64, flag]) (memory := memory) (gas := gas - 3)
    (byte := 0x20) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have hext : extendMemory memory.size [((32 : U256), (64 : U256))] = ⟨0, 0⟩ := by
    rw [hsize]
    decide
  have h3 := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 27)
    (start := 32) (size := 64) (rest := [flag]) (memory := memory) (gas := gas - 3 - 3)
    (state := state) (substate := substate) (by decide) rfl (by rw [hext]; exact Nat.zero_le _)
  rw [hext] at h3
  have hread : memoryReadBytes (memoryExtend memory 0) (32 : U256).toNat (64 : U256).toNat =
      memoryReadBytes memory 32 64 := by
    rw [memoryExtend_zero]
    rfl
  have hg : gas - 3 - 3 - 0 = gas - 6 := by omega
  exact Spec.seq (h1.seq h2)
    (h3.consequence (fun _ hp => hp) fun _ hq => by rw [hread, hg] at hq; exact hq)

/-- The 64 bytes that the caller returns: the word it sent, then 32 zero bytes.

The callee wrote 32 bytes into an output range of 64, and the rest stays zero. -/
theorem memoryReadBytes_echoed (x : U256) :
    memoryReadBytes (memoryWrite (memoryExtend (wordBytes x) 64) 32 (wordBytes x)) 32 64 =
      memoryExtend (wordBytes x) 32 := by
  have hx := size_wordBytes x
  have hext : (memoryExtend (wordBytes x) 64).size = 96 := by
    rw [size_memoryExtend, hx]
  have hfit : 32 + (wordBytes x).size ≤ (memoryExtend (wordBytes x) 64).size := by omega
  have hw : (memoryWrite (memoryExtend (wordBytes x) 64) 32 (wordBytes x)).size = 96 := by
    rw [size_memoryWrite hfit, hext]
  have hread : 32 + 64 ≤ (memoryWrite (memoryExtend (wordBytes x) 64) 32 (wordBytes x)).size := by
    omega
  apply eq_of_byteAt
  · rw [size_memoryReadBytes hread, size_memoryExtend, hx]
  · intro i
    rw [byteAt_memoryReadBytes hread, byteAt_memoryExtend, byteAt_memoryWrite hfit, hx]
    by_cases hi : i < 32
    · have h1 : i < 64 := by omega
      have h2 : 32 ≤ 32 + i ∧ 32 + i < 32 + 32 := by omega
      rw [ite_eq_left h1, ite_eq_left h2, Nat.add_sub_cancel_left]
    · have hz : byteAt (wordBytes x) i = 0 := Base.byteAt_of_size_le (by omega)
      rw [hz]
      by_cases h1 : i < 64
      · have h2 : ¬(32 ≤ 32 + i ∧ 32 + i < 32 + 32) := by omega
        rw [ite_eq_left h1, ite_eq_right h2, byteAt_memoryExtend, Base.byteAt_of_size_le (by omega)]
      · rw [ite_eq_right h1]

/-- The caller returns the word it sent, then 32 zero bytes, with the runner of the interpreter.

The address in the second word of its call data holds the code of the callee and is no precompile.

The depth leaves room for one more frame, and the frame holds the gas of the call.

Or the run aborts, when a runner fails with an error that aborts the run. -/
theorem runFrame_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    (hcode : state.getCode
      (state.getAccount (toAddressMasked (target message.data))).codeHash = .ok ECHO)
    (hprecompile : Precompiles.isPrecompile fork
      (toAddressMasked (target message.data)).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 45 + CallFlag.accessCost cold + 384 ≤ gas) {bound : Nat}
    {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧
      stopped.running = false ∧ stopped.error = none ∧
      stopped.output = memoryExtend (wordBytes (word message.data)) 32) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true := by
  have hacc : CallFlag.accessCost cold = if cold then 2600 else 100 := rfl
  have hext : extendMemory (wordBytes (word message.data)).size
      [((0 : U256), (32 : U256)), ((32 : U256), (64 : U256))] = ⟨6, 64⟩ := by
    rw [size_wordBytes]
    decide
  have hcall := callWith (fork := fork) (code := CODE) (message := message) (pc := 22)
    (memory := wordBytes (word message.data)) (gas := gas - 39) (state := state)
    (substate := substate) (callee := Callee) (asked := 65535) (to := target message.data)
    (inputStart := 0) (inputSize := 32) (outputStart := 32) (outputSize := 64) (rest := [])
    hfork hglam (by decide) rfl hcode (fun _ => by decide) hdepth hcold
    (by rw [hext]; cases cold <;> simp only [CallFlag.accessCost, ite_true, Bool.false_eq_true,
      ite_false] at hgas ⊢ <;> omega)
  rw [hext] at hcall
  -- The rest of the run, from each frame that CALL gives.
  have htail : Hoare fork
      (fun evm => ∃ caller msg child, Callee caller msg child ∧ child.gas ≤ msg.gas ∧
        caller.state =
          (state.recordAccountRead (toAddressMasked (target message.data))).recordAccountRead
            message.currentTarget ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert
            (toAddressMasked (target message.data)) } ∧
        msg.gas = callGas 65535 (gas - 39) ((if cold then 2600 else 100) + 6) ∧
        msg.caller = message.currentTarget ∧
        msg.currentTarget = toAddressMasked (target message.data) ∧
        msg.target = some (toAddressMasked (target message.data)) ∧
        msg.codeAddress = some (toAddressMasked (target message.data)) ∧ msg.code = ECHO ∧
        msg.data = memoryReadBytes (memoryExtend (wordBytes (word message.data)) 64)
          (0 : U256).toNat (32 : U256).toNat ∧
        msg.value = 0 ∧ msg.depth = message.depth + 1 ∧
        At CODE message (22 + 1) ((if child.error.isNone then 1 else 0) :: [])
          (memoryWrite (memoryExtend (wordBytes (word message.data)) 64) (32 : U256).toNat
            (child.output.extract 0 (min (64 : U256).toNat child.output.size)))
          (gas - 39 - (callGas 65535 (gas - 39) ((if cold then 2600 else 100) + 6) +
            ((if cold then 2600 else 100) + 6)) + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          evm)
      (fun evm => evm.running = false ∧ evm.error = none ∧
        evm.output = memoryExtend (wordBytes (word message.data)) 32) := by
    rintro evm ⟨caller, msg, child, hcallee, -, -, -, hmg, -, -, hmtg, hmca, hmcode, hmd, hmv, -,
      hat⟩
    have hpre : precompileAddress fork msg = none := by
      simp [precompileAddress, hmca, hprecompile]
    have hsub : 21 ≤ msg.gas ∧ 6 ≤ gas - 39 - (callGas 65535 (gas - 39)
        ((if cold then 2600 else 100) + 6) + ((if cold then 2600 else 100) + 6)) := by
      rw [hmg]
      unfold callGas maxMessageCallGas
      rw [show (65535 : U256).toNat = 65535 from rfl]
      cases cold <;> simp only [CallFlag.accessCost, ite_true, Bool.false_eq_true, ite_false]
        at hgas ⊢ <;> omega
    obtain ⟨ended, hret, hchild⟩ := hcallee hmcode (by simp [hmtg]) (by simp [hmv]) hpre hsub.1
    have hdata : msg.data = memoryReadBytes (wordBytes (word message.data)) 0 32 := by
      rw [hmd]
      have h : memoryReadBytes (memoryExtend (wordBytes (word message.data)) 64) 0 32 =
          memoryReadBytes (wordBytes (word message.data)) 0 32 := by
        apply eq_of_byteAt
        · rw [size_memoryReadBytes (by rw [size_memoryExtend, size_wordBytes]; omega),
            size_memoryReadBytes (by simp [size_wordBytes])]
        · intro i
          rw [byteAt_memoryReadBytes (by rw [size_memoryExtend, size_wordBytes]; omega),
            byteAt_memoryReadBytes (by simp [size_wordBytes]), byteAt_memoryExtend]
      exact h
    have hnone : child.error = none := by
      rw [hchild, rollbackOnError_of_error_eq_none hret.2.1]
      exact hret.2.1
    have hout : child.output = wordBytes (word message.data) := by
      rw [hchild, rollbackOnError_of_error_eq_none hret.2.1, hret.2.2.1, hdata, word,
        SumLoop.loadWord_wordBytes]
    rw [hout, size_wordBytes, show (64 : U256).toNat = 64 from rfl,
      show (32 : U256).toNat = 32 from rfl] at hat
    have hext' : (wordBytes (word message.data)).extract 0 (min 64 32) =
        wordBytes (word message.data) := by
      rw [show min 64 32 = 32 from rfl]
      have h := ByteArray.extract_zero_size (b := wordBytes (word message.data))
      rwa [size_wordBytes] at h
    rw [hext'] at hat
    have hsize : (memoryWrite (memoryExtend (wordBytes (word message.data)) 64) 32
        (wordBytes (word message.data))).size = 96 := by
      rw [size_memoryWrite (by simp [size_memoryExtend, size_wordBytes]), size_memoryExtend,
        size_wordBytes]
    obtain ⟨stopped, hreach, halted, hq⟩ := finish (fork := fork) (message := message)
      (flag := if child.error.isNone then 1 else 0) hsize
      (Nat.le_trans hsub.2 (Nat.le_add_right _ child.gas)) evm hat
    refine ⟨stopped, hreach, halted, hq.2.1, ?_⟩
    rw [hq.2.2.1, memoryReadBytes_echoed]
  have h := SpecUnder.seq (HoareUnder.of_hoare (operands (by omega)))
    (HoareUnder.seq hcall (HoareUnder.of_hoare htail))
  rcases h.runFrame (meets bound) start within with ⟨stopped, ran, herr, hout⟩ | aborted
  · exact .inl ⟨stopped, ran, running_runFrame ran, herr, hout⟩
  · exact .inr aborted

end EthLib.Execution.Evm.Logic.CallEcho
