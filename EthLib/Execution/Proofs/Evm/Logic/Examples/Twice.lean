module

public import EthLib.Execution.Proofs.Evm.Logic.Subroutine
public import EthLib.Execution.Proofs.Evm.Logic.Stack

/-!
# Proofs: a contract that calls one subroutine twice

This example proves a subroutine once and uses that proof at two places that call it.

The subroutine at 24 doubles the word on top of its return address.

- At 24, `5b` is JUMPDEST.
- At 25, `80 01` doubles the word.
- At 27, `90 56` puts the return address on top and jumps back to it.

The contract quadruples the word of call data at offset 0, and returns it.

- At 0, `60 08 60 00 35` pushes the return address 8, then the word of call data.
- At 5, `60 18 56` calls the subroutine at 24.
- At 8, `5b 60 0f 90` takes the double, and puts the return address 15 under it.
- At 12, `60 18 56` calls the subroutine again.
- At 15, `5b` is JUMPDEST.
- At 16, `60 00 52` writes the word at offset 0 of memory.
- At 19, `60 20 60 00 f3` returns those 32 bytes.

The subroutine costs 18 gas: a JUMPDEST of 1, three opcodes of 3 and a JUMP of 8.

Each call adds a push of 3 and a JUMP of 8, and the contract costs 90 gas in all.

The contract returns 4 times the word, modulo `2 ^ 256`, and keeps its state and substate.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Twice

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode: a contract that calls its subroutine at 24 twice. -/
def CODE : ByteArray := ⟨#[0x60, 0x08, 0x60, 0x00, 0x35, 0x60, 0x18, 0x56, 0x5b, 0x60, 0x0f,
  0x90, 0x60, 0x18, 0x56, 0x5b, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3, 0x5b, 0x80, 0x01,
  0x90, 0x56]⟩

/-- The word that the contract quadruples: the word of call data at offset 0. -/
def input (data : ByteArray) : U256 := loadWord data 0 32

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}
  {memory : ByteArray}

/-- The subroutine doubles the word on top of its return address, for 18 gas.

It needs room for one more word on the stack. -/
theorem double (x : U256) :
    Subroutine (fork := fork) CODE message 24 [x] [x + x] 1 18 memory memory state state
      substate substate := by
  intro ret rest gas valid room hgas
  have h1 := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 24)
    (stack := [x] ++ ret :: rest) (memory := memory) (gas := gas) (state := state)
    (substate := substate) (by decide) rfl (by omega)
  have h2 := dup1 (fork := fork) (code := CODE) (message := message) (pc := 25)
    (memory := memory) (gas := gas - 1) (state := state) (substate := substate) (x := x)
    (rest := ret :: rest) (by decide) rfl (by omega)
    (by simp [STACK_LIMIT] at room ⊢; omega)
  have h3 := binary (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := memory) (pc := 26) (x := x) (y := x) (rest := ret :: rest)
    (gas := gas - 1 - 3) (by decide) rfl
    (ofByte_of_decode (op := .add) rfl (Fork.frontier_le _)) instruction_add
    (by simp only [OPCODE_ADD, VERY_LOW]; omega)
  have h4 := swap (fork := fork) (code := CODE) (message := message) (pc := 27) 0
    (memory := memory) (gas := gas - 1 - 3 - OPCODE_ADD) (state := state) (substate := substate)
    (top := add x x) (x := ret) (rest := ret :: rest) (by decide) rfl rfl
    (by simp only [OPCODE_ADD, VERY_LOW]; omega)
  have h5 := jump (fork := fork) (code := CODE) (message := message) (pc := 28)
    (memory := memory) (gas := gas - 1 - 3 - OPCODE_ADD - 3) (state := state)
    (substate := substate) (destination := ret) (rest := add x x :: rest) (by decide) rfl
    (by simp only [OPCODE_ADD, VERY_LOW]; omega) valid
  have hg : gas - 1 - 3 - OPCODE_ADD - 3 - 8 = gas - 18 := by
    simp only [OPCODE_ADD, VERY_LOW]
    omega
  rw [hg] at h5
  exact (((h1.seq h2).seq h3).seq h4).seq h5

/-- The word that the contract returns, 4 times its input, modulo `2 ^ 256`. -/
theorem add_add (x : U256) : x + x + (x + x) = 4 * x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  rw [show (4 : U256).toNat = 4 from rfl]
  omega

/-- A call of the subroutine from a PUSH1 of its address at `pc`, then JUMP.

The return address `ret` is a JUMPDEST of the code, and the stack under it leaves room. -/
theorem callDouble {pc : Nat} {ret x : U256} {gas : Nat} (hlt : pc + 2 < CODE.size)
    (hpush : CODE[pc]'(by omega) = 0x60) (hword : pushData CODE pc 1 = 24)
    (hjump : CODE[pc + 2] = 0x56)
    (valid : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hgas : 29 ≤ gas) :
    Hoare fork (At CODE message pc [x, ret] memory gas state substate)
      (At CODE message ret.toNat [x + x] memory (gas - 29) state substate) := by
  exact callSubroutine (fork := fork) (n := 1) (entry := 24) (ret := ret) (args := [x])
    (results := [x + x]) (rest := []) (room := 1) (cost := 18) (double x) (by decide)
    (by omega) (by rw [hpush]; decide) (by decide)
    hword hlt hjump
    (by decide) valid (by simp [STACK_LIMIT]) (by simp [STACK_LIMIT]) hgas

/-- The specification: the contract returns 4 times the word of call data at offset 0.

It needs at least 90 gas, keeps 90 gas less, and keeps its state and substate. -/
theorem spec {gas : Nat} (hgas : 90 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (4 * input message.data)) (gas - 90) state substate) := by
  have p1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas)
    (byte := 0x08) (by decide) rfl rfl (by omega) (by decide)
  have p2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 2) (stack := [8]) (memory := .empty) (gas := gas - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have p3 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 4) (start := 0) (rest := [8])
    (gas := gas - 3 - 3) (by decide) rfl (by omega)
  have c1 := callDouble (fork := fork) (message := message) (memory := .empty) (state := state)
    (substate := substate) (pc := 5) (ret := 8) (x := input message.data)
    (gas := gas - 3 - 3 - 3) (by decide) rfl (by decide) rfl (by decide) (by omega)
  have j1 := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 8)
    (stack := [input message.data + input message.data]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 29) (state := state) (substate := substate) (by decide) rfl
    (by omega)
  have p4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 9) (stack := [input message.data + input message.data])
    (memory := .empty) (gas := gas - 3 - 3 - 3 - 29 - 1) (byte := 0x0f) (by decide) rfl rfl
    (by omega) (by simp [STACK_LIMIT])
  have s1 := swap (fork := fork) (code := CODE) (message := message) (pc := 11) 0
    (memory := .empty) (gas := gas - 3 - 3 - 3 - 29 - 1 - 3) (state := state)
    (substate := substate) (top := 15) (x := input message.data + input message.data)
    (rest := [input message.data + input message.data]) (by decide) rfl rfl (by omega)
  have c2 := callDouble (fork := fork) (message := message) (memory := .empty) (state := state)
    (substate := substate) (pc := 12) (ret := 15)
    (x := input message.data + input message.data) (gas := gas - 3 - 3 - 3 - 29 - 1 - 3 - 3)
    (by decide) rfl (by decide) rfl (by decide) (by omega)
  rw [add_add] at c2
  have j2 := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 15)
    (stack := [input message.data + input message.data +
      (input message.data + input message.data)]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 29 - 1 - 3 - 3 - 29) (state := state) (substate := substate)
    (by decide) rfl (by omega)
  rw [add_add] at j2
  have p5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 16) (stack := [4 * input message.data]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 29 - 1 - 3 - 3 - 29 - 1) (byte := 0x00) (by decide) rfl rfl
    (by omega) (by simp [STACK_LIMIT])
  -- Memory grows from no word to one word, for 3 gas.
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have m1 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 18)
    (start := 0) (value := 4 * input message.data) (rest := []) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 29 - 1 - 3 - 3 - 29 - 1 - 3) (state := state)
    (substate := substate) (by decide) rfl (by rw [hext]; dsimp only; omega)
  have hwrite : memoryWrite (memoryExtend .empty (extendMemory ByteArray.empty.size
      [((0 : U256), (32 : U256))]).expandBy) (0 : U256).toNat
      (wordBytes (4 * input message.data)) = wordBytes (4 * input message.data) := by
    rw [hext]
    exact memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])
  rw [hwrite, hext] at m1
  have p6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 19) (stack := [])
    (memory := wordBytes (4 * input message.data))
    (gas := gas - 3 - 3 - 3 - 29 - 1 - 3 - 3 - 29 - 1 - 3 - (3 + 3)) (byte := 0x20)
    (by decide) rfl rfl (by omega) (by decide)
  have p7 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 21) (stack := [32])
    (memory := wordBytes (4 * input message.data))
    (gas := gas - 3 - 3 - 3 - 29 - 1 - 3 - 3 - 29 - 1 - 3 - (3 + 3) - 3) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  -- Memory already holds the word, so RETURN grows nothing.
  have hext' : extendMemory (wordBytes (4 * input message.data)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have r := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 23)
    (start := 0) (size := 32) (rest := []) (memory := wordBytes (4 * input message.data))
    (gas := gas - 3 - 3 - 3 - 29 - 1 - 3 - 3 - 29 - 1 - 3 - (3 + 3) - 3 - 3) (state := state)
    (substate := substate) (by decide) rfl (by rw [hext']; exact Nat.zero_le _)
  have hread : memoryReadBytes (memoryExtend (wordBytes (4 * input message.data)) 0)
      (0 : U256).toNat (32 : U256).toNat = wordBytes (4 * input message.data) := by
    rw [memoryExtend_zero]
    have := memoryReadBytes_whole (memory := wordBytes (4 * input message.data))
    rwa [size_wordBytes] at this
  rw [hext'] at r
  have hg : gas - 3 - 3 - 3 - 29 - 1 - 3 - 3 - 29 - 1 - 3 - (3 + 3) - 3 - 3 - 0 = gas - 90 := by
    omega
  exact Spec.seq ((((((((((((p1.seq p2).seq p3).seq c1).seq j1).seq p4).seq s1).seq c2).seq
    j2).seq p5).seq m1).seq p6).seq p7) (r.consequence (fun _ hp => hp) fun _ hq => by
      rw [hread, hg] at hq
      exact hq)

/-- The loop of the interpreter runs the contract to its specification.

It holds for every bound on the gas of messages and every runner of messages.

The contract sends no message. -/
theorem runFrame_spec {gas : Nat} (hgas : 90 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
        Halted false (wordBytes (4 * input message.data)) (gas - 90) state substate stopped :=
  (spec hgas).runFrame start within

end EthLib.Execution.Evm.Logic.Twice
