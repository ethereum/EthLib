module

public import EthLib.Execution.Proofs.Evm.Logic.Subroutine
public import EthLib.Execution.Proofs.Evm.Logic.Stack

/-!
# Proofs: a contract with a recursive subroutine

This example proves a subroutine that calls itself, by induction on its argument.

The subroutine at 17 sums the numbers from 1 to `k`, for the word `k` on top of its return address.

- At 17, `5b 80 15 60 25 57` jumps to 37 when `k` is 0.
- At 23, `60 01 81 03` computes `k - 1`.
- At 27, `60 21 90` puts the return address 33 under it.
- At 30, `60 11 56` calls the subroutine on `k - 1`.
- At 33, `5b 01 90 56` adds `k` to the sum, and jumps back.
- At 37, `5b 90 56` jumps back with the word 0.

Each call on a word that is not 0 keeps two more words on the stack.

So the word `k` needs room for `2 k + 2` words.

The subroutine costs `32 + 61 k` gas.

The contract calls the subroutine on the word of call data at offset 0, and returns the sum.

- At 0, `60 08 60 00 35` pushes the return address 8, then the word of call data.
- At 5, `60 11 56` calls the subroutine.
- At 8, `5b 60 00 52` writes the sum at offset 0 of memory.
- At 12, `60 20 60 00 f3` returns those 32 bytes.

The word must be at most 510, so that the recursion fits in the 1024 words of the stack.

The contract then returns `k (k + 1) / 2` for `68 + 61 k` gas, and keeps its state and substate.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.SumTo

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode: a contract and its recursive subroutine at 17. -/
def CODE : ByteArray := ⟨#[0x60, 0x08, 0x60, 0x00, 0x35, 0x60, 0x11, 0x56, 0x5b, 0x60, 0x00,
  0x52, 0x60, 0x20, 0x60, 0x00, 0xf3, 0x5b, 0x80, 0x15, 0x60, 0x25, 0x57, 0x60, 0x01, 0x81, 0x03,
  0x60, 0x21, 0x90, 0x60, 0x11, 0x56, 0x5b, 0x01, 0x90, 0x56, 0x5b, 0x90, 0x56]⟩

/-- The sum of the numbers from 1 to `k`, as a word. -/
def triangle (k : Nat) : U256 := BitVec.ofNat 256 (k * (k + 1) / 2)

/-- The sum up to `k + 1` is the sum up to `k`, plus `k + 1`. -/
theorem triangle_succ (k : Nat) :
    triangle (k + 1) = triangle k + BitVec.ofNat 256 (k + 1) := by
  rw [triangle, triangle, ← BitVec.ofNat_add]
  congr 1
  have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
  rw [h]
  omega

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}
  {memory : ByteArray}

/-- The subroutine sums the numbers from 1 to `k`, for `32 + 61 k` gas.

It needs room for `2 k + 2` more words on the stack. -/
theorem sum (k : Nat) :
    Subroutine (fork := fork) CODE message 17 [BitVec.ofNat 256 k] [triangle k] (2 * k + 2)
      (32 + 61 * k) memory memory state state substate substate := by
  induction k with
  | zero =>
    intro ret rest gas valid room hgas
    simp only [List.length_singleton, STACK_LIMIT] at room
    have h1 := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 17)
      (stack := [BitVec.ofNat 256 0] ++ ret :: rest) (memory := memory) (gas := gas)
      (state := state) (substate := substate) (by decide) rfl (by omega)
    have h2 := dup1 (fork := fork) (code := CODE) (message := message) (pc := 18)
      (memory := memory) (gas := gas - 1) (state := state) (substate := substate)
      (x := BitVec.ofNat 256 0) (rest := ret :: rest) (by decide) rfl (by omega)
      (by simp [STACK_LIMIT]; omega)
    have h3 := unary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 19) (x := BitVec.ofNat 256 0)
      (rest := BitVec.ofNat 256 0 :: ret :: rest) (gas := gas - 1 - 3) (by decide) rfl
      (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
    have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 20)
      (stack := isZero (BitVec.ofNat 256 0) :: BitVec.ofNat 256 0 :: ret :: rest)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO) (byte := 0x25) (by decide) rfl
      rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT]; omega)
    have h5 := jumpi_taken (fork := fork) (code := CODE) (message := message) (pc := 22)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3) (state := state)
      (substate := substate) (destination := BitVec.ofNat 256 (UInt8.toNat 0x25))
      (condition := isZero (BitVec.ofNat 256 0)) (rest := BitVec.ofNat 256 0 :: ret :: rest)
      (by decide) rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by decide) (by decide)
    have h6 := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 37)
      (stack := BitVec.ofNat 256 0 :: ret :: rest) (memory := memory)
      (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10) (state := state) (substate := substate)
      (by decide) rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
    have h7 := swap (fork := fork) (code := CODE) (message := message) (pc := 38) 0
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1) (state := state)
      (substate := substate) (top := BitVec.ofNat 256 0) (x := ret) (rest := ret :: rest)
      (by decide) rfl rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
    have h8 := jump (fork := fork) (code := CODE) (message := message) (pc := 39)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3) (state := state)
      (substate := substate) (destination := ret) (rest := BitVec.ofNat 256 0 :: rest)
      (by decide) rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) valid
    have hg : gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3 - 8 = gas - (32 + 61 * 0) := by
      simp only [OPCODE_ISZERO, VERY_LOW]
      omega
    rw [hg] at h8
    exact ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  | succ k ih =>
    intro ret rest gas valid room hgas
    simp only [List.length_singleton, STACK_LIMIT] at room
    have hk : k + 1 < 2 ^ 256 := by omega
    have hne : BitVec.ofNat 256 (k + 1) ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
      exact absurd this (by rw [show (0 : U256).toNat = 0 from rfl]; omega)
    have hz : isZero (BitVec.ofNat 256 (k + 1)) = 0 := by
      unfold isZero
      exact ite_eq_right hne
    have hsub : sub (BitVec.ofNat 256 (k + 1)) 1 = BitVec.ofNat 256 k := by
      apply BitVec.eq_of_toNat_eq
      simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
        Nat.mod_eq_of_lt (show k < 2 ^ 256 by omega)]
      rw [show (1 : U256).toNat = 1 from rfl]
      omega
    have h1 := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 17)
      (stack := [BitVec.ofNat 256 (k + 1)] ++ ret :: rest) (memory := memory) (gas := gas)
      (state := state) (substate := substate) (by decide) rfl (by omega)
    have h2 := dup1 (fork := fork) (code := CODE) (message := message) (pc := 18)
      (memory := memory) (gas := gas - 1) (state := state) (substate := substate)
      (x := BitVec.ofNat 256 (k + 1)) (rest := ret :: rest) (by decide) rfl (by omega)
      (by simp [STACK_LIMIT]; omega)
    have h3 := unary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 19) (x := BitVec.ofNat 256 (k + 1))
      (rest := BitVec.ofNat 256 (k + 1) :: ret :: rest) (gas := gas - 1 - 3) (by decide) rfl
      (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
    rw [hz] at h3
    have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 20)
      (stack := 0 :: BitVec.ofNat 256 (k + 1) :: ret :: rest)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO) (byte := 0x25) (by decide) rfl
      rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT]; omega)
    have h5 := jumpi_zero (fork := fork) (code := CODE) (message := message) (pc := 22)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3) (state := state)
      (substate := substate) (destination := BitVec.ofNat 256 (UInt8.toNat 0x25))
      (rest := BitVec.ofNat 256 (k + 1) :: ret :: rest)
      (by decide) rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
    have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 23) (stack := BitVec.ofNat 256 (k + 1) :: ret :: rest)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10) (byte := 0x01)
      (by decide) rfl rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
      (by simp [STACK_LIMIT]; omega)
    have h7 := dup (fork := fork) (code := CODE) (message := message) (pc := 25) 1
      (stack := BitVec.ofNat 256 (UInt8.toNat 0x01) :: BitVec.ofNat 256 (k + 1) :: ret :: rest)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3) (state := state)
      (substate := substate) (x := BitVec.ofNat 256 (k + 1)) (by decide) rfl rfl
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT]; omega)
    have h8 := binary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 26) (x := BitVec.ofNat 256 (k + 1))
      (y := BitVec.ofNat 256 (UInt8.toNat 0x01)) (rest := BitVec.ofNat 256 (k + 1) :: ret :: rest)
      (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3) (by decide) rfl
      (ofByte_of_decode (op := .sub) rfl (Fork.frontier_le _)) instruction_sub
      (by simp only [OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega)
    rw [show BitVec.ofNat 256 (UInt8.toNat 0x01) = (1 : U256) from rfl, hsub] at h8
    have h9 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 27)
      (stack := BitVec.ofNat 256 k :: BitVec.ofNat 256 (k + 1) :: ret :: rest)
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB)
      (byte := 0x21) (by decide) rfl rfl
      (by simp only [OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT]; omega)
    have h10 := swap (fork := fork) (code := CODE) (message := message) (pc := 29) 0
      (memory := memory) (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB - 3)
      (state := state) (substate := substate) (top := BitVec.ofNat 256 (UInt8.toNat 0x21))
      (x := BitVec.ofNat 256 k) (rest := BitVec.ofNat 256 k :: BitVec.ofNat 256 (k + 1) :: ret ::
        rest) (by decide) rfl rfl (by simp only [OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega)
    have h11 := callSubroutine (fork := fork) (code := CODE) (message := message) (pc := 30)
      (n := 1) (entry := 17) (ret := BitVec.ofNat 256 (UInt8.toNat 0x21))
      (args := [BitVec.ofNat 256 k]) (results := [triangle k])
      (rest := BitVec.ofNat 256 (k + 1) :: ret :: rest) (room := 2 * k + 2)
      (cost := 32 + 61 * k)
      (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB - 3 - 3) ih (by decide)
      (by decide) rfl (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      (by simp [STACK_LIMIT]; omega) (by simp [STACK_LIMIT]; omega)
      (by simp only [OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega)
    have h12 := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 33)
      (stack := [triangle k] ++ BitVec.ofNat 256 (k + 1) :: ret :: rest) (memory := memory)
      (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB - 3 - 3 -
        (11 + (32 + 61 * k))) (state := state) (substate := substate) (by decide) rfl
      (by simp only [OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega)
    have h13 := binary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 34) (x := triangle k)
      (y := BitVec.ofNat 256 (k + 1)) (rest := ret :: rest)
      (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB - 3 - 3 -
        (11 + (32 + 61 * k)) - 1) (by decide) rfl
      (ofByte_of_decode (op := .add) rfl (Fork.frontier_le _)) instruction_add
      (by simp only [OPCODE_ADD, OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega)
    rw [show add (triangle k) (BitVec.ofNat 256 (k + 1)) = triangle (k + 1) from
      (triangle_succ k).symm] at h13
    have h14 := swap (fork := fork) (code := CODE) (message := message) (pc := 35) 0
      (memory := memory)
      (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB - 3 - 3 -
        (11 + (32 + 61 * k)) - 1 - OPCODE_ADD)
      (state := state) (substate := substate) (top := triangle (k + 1)) (x := ret)
      (rest := ret :: rest) (by decide) rfl rfl
      (by simp only [OPCODE_ADD, OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega)
    have h15 := jump (fork := fork) (code := CODE) (message := message) (pc := 36)
      (memory := memory)
      (gas := gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB - 3 - 3 -
        (11 + (32 + 61 * k)) - 1 - OPCODE_ADD - 3)
      (state := state) (substate := substate) (destination := ret)
      (rest := triangle (k + 1) :: rest) (by decide) rfl
      (by simp only [OPCODE_ADD, OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]; omega) valid
    have hg : gas - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB - 3 - 3 -
        (11 + (32 + 61 * k)) - 1 - OPCODE_ADD - 3 - 8 = gas - (32 + 61 * (k + 1)) := by
      simp only [OPCODE_ADD, OPCODE_SUB, OPCODE_ISZERO, VERY_LOW]
      omega
    rw [hg] at h15
    exact (((((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq
      h10).seq h11).seq h12).seq h13).seq h14).seq h15

/-- The word that the contract sums up to: the word of call data at offset 0. -/
def input (data : ByteArray) : U256 := loadWord data 0 32

/-- The specification: the contract returns the sum of the numbers from 1 to its input.

The input is at most 510, so that the recursion fits on the stack.

It needs at least `68 + 61 k` gas for the input `k`, and keeps the rest.

It keeps its state and substate. -/
theorem spec (hsmall : (input message.data).toNat ≤ 510) {gas : Nat}
    (hgas : 68 + 61 * (input message.data).toNat ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (triangle (input message.data).toNat))
        (gas - (68 + 61 * (input message.data).toNat)) state substate) := by
  have hword : BitVec.ofNat 256 (input message.data).toNat = input message.data :=
    (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  have p1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas)
    (byte := 0x08) (by decide) rfl rfl (by omega) (by decide)
  have p2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 2) (stack := [8]) (memory := .empty) (gas := gas - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have p3 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 4) (start := 0) (rest := [8])
    (gas := gas - 3 - 3) (by decide) rfl (by omega)
  have hsum := sum (fork := fork) (message := message) (memory := .empty) (state := state)
    (substate := substate) (input message.data).toNat
  rw [hword] at hsum
  have c := callSubroutine (fork := fork) (code := CODE) (message := message) (pc := 5)
    (n := 1) (entry := 17) (ret := 8) (args := [input message.data])
    (results := [triangle (input message.data).toNat]) (rest := [])
    (room := 2 * (input message.data).toNat + 2) (cost := 32 + 61 * (input message.data).toNat)
    (gas := gas - 3 - 3 - 3) hsum (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (by simp [STACK_LIMIT]; omega)
    (by simp [STACK_LIMIT]) (by omega)
  have j := jumpdest (fork := fork) (code := CODE) (message := message) (pc := 8)
    (stack := [triangle (input message.data).toNat]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - (11 + (32 + 61 * (input message.data).toNat))) (state := state)
    (substate := substate) (by decide) rfl (by omega)
  have p4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 9) (stack := [triangle (input message.data).toNat])
    (memory := .empty) (gas := gas - 3 - 3 - 3 - (11 + (32 + 61 * (input message.data).toNat)) - 1)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  -- Memory grows from no word to one word, for 3 gas.
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have m := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 11)
    (start := 0) (value := triangle (input message.data).toNat) (rest := []) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - (11 + (32 + 61 * (input message.data).toNat)) - 1 - 3)
    (state := state) (substate := substate) (by decide) rfl (by rw [hext]; dsimp only; omega)
  have hwrite : memoryWrite (memoryExtend .empty (extendMemory ByteArray.empty.size
      [((0 : U256), (32 : U256))]).expandBy) (0 : U256).toNat
      (wordBytes (triangle (input message.data).toNat)) =
      wordBytes (triangle (input message.data).toNat) := by
    rw [hext]
    exact memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])
  rw [hwrite, hext] at m
  have p5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 12) (stack := [])
    (memory := wordBytes (triangle (input message.data).toNat))
    (gas := gas - 3 - 3 - 3 - (11 + (32 + 61 * (input message.data).toNat)) - 1 - 3 - (3 + 3))
    (byte := 0x20) (by decide) rfl rfl (by omega) (by decide)
  have p6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 14) (stack := [32])
    (memory := wordBytes (triangle (input message.data).toNat))
    (gas := gas - 3 - 3 - 3 - (11 + (32 + 61 * (input message.data).toNat)) - 1 - 3 - (3 + 3) -
      3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  -- Memory already holds the word, so RETURN grows nothing.
  have hext' : extendMemory (wordBytes (triangle (input message.data).toNat)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have r := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 16)
    (start := 0) (size := 32) (rest := [])
    (memory := wordBytes (triangle (input message.data).toNat))
    (gas := gas - 3 - 3 - 3 - (11 + (32 + 61 * (input message.data).toNat)) - 1 - 3 - (3 + 3) -
      3 - 3) (state := state) (substate := substate) (by decide) rfl
    (by rw [hext']; exact Nat.zero_le _)
  have hread : memoryReadBytes (memoryExtend (wordBytes (triangle (input message.data).toNat)) 0)
      (0 : U256).toNat (32 : U256).toNat = wordBytes (triangle (input message.data).toNat) := by
    rw [memoryExtend_zero]
    have := memoryReadBytes_whole (memory := wordBytes (triangle (input message.data).toNat))
    rwa [size_wordBytes] at this
  rw [hext'] at r
  have hg : gas - 3 - 3 - 3 - (11 + (32 + 61 * (input message.data).toNat)) - 1 - 3 - (3 + 3) -
      3 - 3 - 0 = gas - (68 + 61 * (input message.data).toNat) := by
    omega
  exact Spec.seq ((((((((p1.seq p2).seq p3).seq c).seq j).seq p4).seq m).seq p5).seq p6)
    (r.consequence (fun _ hp => hp) fun _ hq => by
      rw [hread, hg] at hq
      exact hq)

/-- The loop of the interpreter runs the contract to its specification.

It holds for every bound on the gas of messages and every runner of messages.

The contract sends no message. -/
theorem runFrame_spec (hsmall : (input message.data).toNat ≤ 510) {gas : Nat}
    (hgas : 68 + 61 * (input message.data).toNat ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (wordBytes (triangle (input message.data).toNat))
        (gas - (68 + 61 * (input message.data).toNat)) state substate stopped :=
  (spec hsmall hgas).runFrame start within

end EthLib.Execution.Evm.Logic.SumTo
