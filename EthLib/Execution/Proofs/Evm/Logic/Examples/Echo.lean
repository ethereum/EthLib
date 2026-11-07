module

public import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# Proofs: a contract that returns its call data

This example proves code whose memory depends on its input, with frames that know ranges of memory.

The bytecode `0x366000600037366000f3` copies the call data to memory and returns it.

- At 0, `36` pushes the size of the call data.
- At 1, `60 00 60 00` pushes the offset 0 in the call data and the start 0 in memory.
- At 5, `37` is CALLDATACOPY.
- At 6, `36` pushes the size of the call data again.
- At 7, `60 00` pushes the start 0.
- At 9, `f3` is RETURN.

The proof never states the whole memory, only its size and the range that holds the call data.

The call data holds some bytes, fewer than `2 ^ 256`.

The code costs 16 gas, 3 gas a word of call data, and the price of memory that holds the call data.

It then halts normally, returns its call data, and keeps its state and substate.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Echo

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode: copy the call data to memory, then return it. -/
def CODE : ByteArray := ⟨#[0x36, 0x60, 0x00, 0x60, 0x00, 0x37, 0x36, 0x60, 0x00, 0xf3]⟩

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- A read of a whole buffer from its start gives the buffer. -/
theorem bufferRead_whole (data : ByteArray) :
    (⟨(bufferRead data 0 data.size).toArray⟩ : ByteArray) = data := by
  rw [bufferRead_zero_size]

/-- Memory that grows from nothing to hold the call data costs the price of that many bytes. -/
theorem extendMemory_data {n : U256} :
    (extendMemory 0 [((0 : U256), n)]).cost = memoryGasCost n.toNat := by
  by_cases hz : n = 0
  · subst hz
    rw [extendMemory_of_length_eq_zero]
    rfl
  · have hpos : n.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
    have h0 : (0 : U256).toNat = 0 := rfl
    rw [extendMemory_of_lt (by decide) hz (by rw [h0]; omega)]
    dsimp only
    rw [h0, Nat.zero_add, memoryGasCost_ceil32, show memoryGasCost 0 = 0 from rfl, Nat.sub_zero]

/-- The specification: the code returns its call data.

The call data holds some bytes, fewer than `2 ^ 256`.

The frame has at least 16 gas, 3 gas a word of call data, and the price of memory that holds it. -/
theorem spec (hsome : 0 < message.data.size) (hfit : message.data.size < 2 ^ 256) {gas : Nat}
    (hgas : 16 + 3 * wordCount message.data.size + memoryGasCost message.data.size ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false message.data
        (gas - (16 + 3 * wordCount message.data.size + memoryGasCost message.data.size))
        state substate) := by
  have hn : (BitVec.ofNat 256 message.data.size).toNat = message.data.size := by
    simp [Nat.mod_eq_of_lt hfit]
  have hz : BitVec.ofNat 256 message.data.size ≠ 0 := fun h => by
    have := congrArg BitVec.toNat h
    rw [hn] at this
    exact absurd this (by rw [show (0 : U256).toNat = 0 from rfl]; omega)
  have hcost := extendMemory_data (n := BitVec.ofNat 256 message.data.size)
  rw [hn] at hcost
  have h1 := Known.of_at (size := 0) (facts := []) fun memory =>
    calldatasize (fork := fork) (code := CODE) (message := message) (pc := 0) (stack := [])
      (memory := memory) (gas := gas) (state := state) (substate := substate) (by decide) rfl
      (by omega) (by decide)
  have h2 := Known.of_at (size := 0) (facts := []) fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 1) (stack := [BitVec.ofNat 256 message.data.size])
      (memory := memory) (gas := gas - 2) (byte := 0x00) (by decide) rfl rfl (by omega)
      (by simp [STACK_LIMIT])
  have h3 := Known.of_at (size := 0) (facts := []) fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 3) (stack := [0, BitVec.ofNat 256 message.data.size])
      (memory := memory) (gas := gas - 2 - 3) (byte := 0x00) (by decide) rfl rfl (by omega)
      (by simp [STACK_LIMIT])
  have h4 := calldatacopy_known (fork := fork) (code := CODE) (message := message) (pc := 5)
    (size := 0) (facts := []) (gas := gas - 2 - 3 - 3) (state := state) (substate := substate)
    (start := 0) (offset := 0) (length := BitVec.ofNat 256 message.data.size) (rest := [])
    (by decide) rfl hz (by rw [hcost, hn]; omega)
  rw [hcost, hn, show (0 : U256).toNat = 0 from rfl, bufferRead_whole, List.filter_nil] at h4
  have h5 := Known.of_at
    (size := 0 + (extendMemory 0 [((0 : U256), BitVec.ofNat 256 message.data.size)]).expandBy)
    (facts := [(0, message.data)]) fun memory =>
    calldatasize (fork := fork) (code := CODE) (message := message) (pc := 6) (stack := [])
      (memory := memory)
      (gas := gas - 2 - 3 - 3 - (3 + 3 * wordCount message.data.size +
        memoryGasCost message.data.size))
      (state := state) (substate := substate) (by decide) rfl (by omega) (by decide)
  have h6 := Known.of_at
    (size := 0 + (extendMemory 0 [((0 : U256), BitVec.ofNat 256 message.data.size)]).expandBy)
    (facts := [(0, message.data)]) fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 7) (stack := [BitVec.ofNat 256 message.data.size])
      (memory := memory)
      (gas := gas - 2 - 3 - 3 - (3 + 3 * wordCount message.data.size +
        memoryGasCost message.data.size) - 2)
      (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have h7 := return_known (fork := fork) (code := CODE) (message := message) (pc := 9)
    (start := 0) (length := BitVec.ofNat 256 message.data.size) (out := message.data) (rest := [])
    (gas := gas - 2 - 3 - 3 - (3 + 3 * wordCount message.data.size +
        memoryGasCost message.data.size) - 2 - 3)
    (size := 0 + (extendMemory 0 [((0 : U256), BitVec.ofNat 256 message.data.size)]).expandBy)
    (facts := [(0, message.data)])
    (state := state) (substate := substate) (by decide) rfl (List.mem_singleton.mpr rfl) hn.symm
  have hg : gas - 2 - 3 - 3 - (3 + 3 * wordCount message.data.size +
      memoryGasCost message.data.size) - 2 - 3 =
      gas - (16 + 3 * wordCount message.data.size + memoryGasCost message.data.size) := by
    omega
  have h := Spec.seq (P := At CODE message 0 [] .empty gas state substate)
    (fun evm hat => (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6) evm (known_of_at_empty hat)) h7
  rw [hg] at h
  exact h

/-- The loop of the interpreter runs the code to its specification.

It holds for every bound on the gas of messages and every runner of messages.

The code sends no message. -/
theorem runFrame_spec (hsome : 0 < message.data.size) (hfit : message.data.size < 2 ^ 256)
    {gas : Nat}
    (hgas : 16 + 3 * wordCount message.data.size + memoryGasCost message.data.size ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false message.data
        (gas - (16 + 3 * wordCount message.data.size + memoryGasCost message.data.size))
        state substate stopped :=
  (spec hsome hfit hgas).runFrame start within

end EthLib.Execution.Evm.Logic.Echo
