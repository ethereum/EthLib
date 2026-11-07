module

public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Logic.Memory
public import EthLib.Execution.Proofs.Evm.Logic.Loop

/-!
# Proofs: a contract with a loop

This example shows that the logic proves a contract that loops as many times as its call data says.

The contract reads the word `n` of call data at offset 0, and sums the numbers from `n` down to 1.

It keeps the counter on the stack and the sum in the word at offset 0 of memory.

It returns the sum, a word: `n (n + 1) / 2` modulo `2^256`, since the additions of the EVM wrap.

- At 0, `60 00 60 00 52` writes the word 0 at offset 0 of memory.
- At 5, `60 00 35` reads the counter, the word of call data at offset 0.
- At 8, `5b` marks the head of the loop.
- At 9, `80 15 60 3b 57` jumps to 59 when the counter is 0.
- At 14, `80 60 00 51 01 60 00 52` adds the counter to the sum in memory.
- At 22, `7f ff .. ff 01` adds `2^256 - 1` to the counter, which takes 1 from it.
- At 56, `60 08 56` jumps back to the head of the loop.
- At 59, `5b 60 20 60 00 f3` returns the 32 bytes of memory from offset 0, the sum.

The counter is a word, so `n` is below `2^256`, and the loop runs `n` times.

Each run of the loop costs 55 gas, and the rest of the code 45 gas, so the call costs `45 + 55 n`.

The rules are those of one counter of gas, the meter of every fork before Glamsterdam.

The proof runs the loop by induction on the counter, from its value at the head of the loop.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.SumLoop

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x60, 0x00, 0x52, 0x60, 0x00, 0x35, 0x5b, 0x80, 0x15, 0x60,
  0x3b, 0x57, 0x80, 0x60, 0x00, 0x51, 0x01, 0x60, 0x00, 0x52, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01, 0x60, 0x08, 0x56, 0x5b,
  0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The number of runs of the loop: the word of call data at offset 0. -/
def count (data : ByteArray) : Nat := (loadWord data 0 32).toNat

/-- The sum of the numbers from 1 to `m`. -/
def triangle (m : Nat) : Nat := m * (m + 1) / 2

/-- The sum at the head of the loop, when the counter is `k`: the numbers from `k + 1` to `n`. -/
def partialSum (n k : Nat) : U256 := BitVec.ofNat 256 (triangle n - triangle k)

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- The frame at the head of the loop, when the counter is `k`, from a call with some gas. -/
def Head (message : Message fork) (state : State.TransactionState) (substate : Substate)
    (gas k : Nat) (evm : Evm fork Nat) : Prop :=
  k ≤ count message.data ∧
    At CODE message 8 [BitVec.ofNat 256 k] (wordBytes (partialSum (count message.data) k))
      (gas - 18 - 55 * (count message.data - k)) state substate evm

/-- The word of a memory that holds one word is that word. -/
theorem loadWord_wordBytes (word : U256) :
    loadWord (memoryReadBytes (wordBytes word) 0 32) 0 32 = word := by
  have h := loadWord_memoryWrite_wordBytes (memory := wordBytes word) (start := 0) word
    (by simp [size_wordBytes])
  rwa [memoryWrite_whole rfl] at h

/-! ## Before the loop -/

/-- The code writes 0 to memory and reads the counter, then reaches the head of the loop. -/
theorem start {gas : Nat} (hgas : 18 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (Head message state substate gas (count message.data)) := by
  have h1 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate)
    (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00) (by decide) rfl rfl
    (by omega) (by decide)
  have h2 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate)
    (pc := 2) (stack := [0]) (memory := .empty) (gas := gas - 3) (byte := 0x00) (by decide) rfl rfl
    (by omega) (by decide)
  -- Memory grows from no word to one word, for 3 gas.
  have hg1 : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h3 := mstore (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 4) (start := 0) (value := 0) (rest := [])
    (gas := gas - 3 - 3) (by decide) rfl (by rw [hg1]; simp only; omega)
  rw [hg1] at h3
  dsimp only at h3
  have hm : memoryWrite (memoryExtend ByteArray.empty 32) (0 : U256).toNat (wordBytes 0) =
      wordBytes 0 := memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])
  rw [hm] at h3
  have h4 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate)
    (pc := 5) (stack := []) (memory := wordBytes 0) (gas := gas - 3 - 3 - (3 + 3)) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h5 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes 0) (pc := 7) (start := 0) (rest := [])
    (gas := gas - 3 - 3 - (3 + 3) - 3) (by decide) rfl (by omega)
  have h := (((h1.seq h2).seq h3).seq h4).seq h5
  refine h.consequence (fun _ x => x) fun evm hr => ⟨Nat.le_refl _, ?_⟩
  have hs : BitVec.ofNat 256 (count message.data) = loadWord message.data 0 32 := by
    simp [count]
  have hp : partialSum (count message.data) (count message.data) = 0 := by
    simp [partialSum]
  rw [hs, hp, Nat.sub_self, Nat.mul_zero, Nat.sub_zero]
  have hg : gas - 3 - 3 - (3 + 3) - 3 - 3 = gas - 18 := by omega
  rw [hg] at hr
  exact hr

/-! ## The sums -/

/-- The sum up to `k + 1` is the sum up to `k`, and `k + 1`. -/
theorem triangle_succ (k : Nat) : triangle (k + 1) = triangle k + (k + 1) := by
  unfold triangle
  have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by
    rw [Nat.mul_comm k, Nat.mul_comm 2, ← Nat.mul_add]
  rw [h, Nat.add_mul_div_left _ _ (by decide)]

/-- The sums grow with their bound. -/
theorem triangle_le {a b : Nat} (h : a ≤ b) : triangle a ≤ triangle b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

/-- The counter is below `2^256`, since it is a word. -/
theorem count_lt (data : ByteArray) : count data < 2 ^ 256 := (loadWord data 0 32).isLt

/-- The sum at the head grows by the counter. -/
theorem partialSum_add {n k : Nat} (h : k + 1 ≤ n) :
    partialSum n (k + 1) + BitVec.ofNat 256 (k + 1) = partialSum n k := by
  unfold partialSum
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  have := triangle_le h
  rw [triangle_succ] at this ⊢
  omega

/-- Adding `2^256 - 1` to a nonzero counter takes 1 from it. -/
theorem allOnes_add {k : Nat} (h : k + 1 < 2 ^ 256) :
    BitVec.ofNat 256 (2 ^ 256 - 1) + BitVec.ofNat 256 (k + 1) = BitVec.ofNat 256 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ 256 - 1 < 2 ^ 256 by decide), Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (show k < 2 ^ 256 by omega)]
  omega

/-! ## The loop -/

/-- One run of the loop takes the counter from `k + 1` to `k` and adds `k + 1` to the sum.

It costs 55 gas. -/
theorem body {gas : Nat} (hgas : 45 + 55 * count message.data ≤ gas) (k : Nat) :
    Hoare fork (Head message state substate gas (k + 1)) (Head message state substate gas k) := by
  intro evm ⟨hk, hrun⟩
  have hlt : k + 1 < 2 ^ 256 := Nat.lt_of_le_of_lt hk (count_lt _)
  -- The names of the parts of the frame at the head.
  generalize hn : count message.data = n at hk hrun hgas
  generalize hG : gas - 18 - 55 * (n - (k + 1)) = G at hrun
  have hG55 : 55 ≤ G := by omega
  generalize hW : wordBytes (partialSum n (k + 1)) = W at hrun
  have hWs : W.size = 32 := by rw [← hW, size_wordBytes]
  have hz : extendMemory W.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hWs]; decide
  have h1 := jumpdest (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 8) (stack := [BitVec.ofNat 256 (k + 1)])
    (gas := G) (by decide) rfl (by omega)
  have h2 := dup1 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 9) (x := BitVec.ofNat 256 (k + 1)) (rest := [])
    (gas := G - 1) (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  have h3 := unary (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 10) (x := BitVec.ofNat 256 (k + 1))
    (rest := [BitVec.ofNat 256 (k + 1)]) (gas := G - 1 - 3) (by decide) rfl
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega)
  have hiz : isZero (BitVec.ofNat 256 (k + 1)) = 0 := by
    have hne : BitVec.ofNat 256 (k + 1) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h'
      simp at h'
    unfold isZero
    rw [ite_eq_right hne]
  rw [hiz] at h3
  have h4 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 11) (stack := [0, BitVec.ofNat 256 (k + 1)]) (memory := W)
    (gas := G - 1 - 3 - OPCODE_ISZERO) (byte := 0x3b) (by decide) rfl rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have h5 := jumpi_zero (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 13) (destination := 0x3b)
    (rest := [BitVec.ofNat 256 (k + 1)]) (gas := G - 1 - 3 - OPCODE_ISZERO - 3) (by decide) rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega)
  have h6 := dup1 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 14) (x := BitVec.ofNat 256 (k + 1)) (rest := [])
    (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10) (by decide) rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have h7 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate)
    (pc := 15) (stack := [BitVec.ofNat 256 (k + 1), BitVec.ofNat 256 (k + 1)]) (memory := W)
    (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3) (byte := 0x00) (by decide) rfl rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have h8 := mload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 17) (start := 0)
    (rest := [BitVec.ofNat 256 (k + 1), BitVec.ofNat 256 (k + 1)])
    (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3) (by decide) rfl
    (by rw [hz]; simp [OPCODE_ISZERO, VERY_LOW]; omega)
  rw [hz, memoryExtend_zero] at h8
  dsimp only at h8
  have hacc : loadWord (memoryReadBytes W (0 : U256).toNat 32) 0 32 = partialSum n (k + 1) := by
    rw [← hW]
    exact loadWord_wordBytes _
  rw [hacc] at h8
  have h9 := binary (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 18) (x := partialSum n (k + 1))
    (y := BitVec.ofNat 256 (k + 1)) (rest := [BitVec.ofNat 256 (k + 1)])
    (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - (3 + 0)) (by decide) rfl
    (ofByte_of_decode (op := .add) rfl (Fork.frontier_le _)) instruction_add
    (by simp [OPCODE_ADD, OPCODE_ISZERO, VERY_LOW]; omega)
  rw [show add (partialSum n (k + 1)) (BitVec.ofNat 256 (k + 1)) = partialSum n k from
    partialSum_add (by omega)] at h9
  -- The rest of the run, with the gas spent so far written as one number.
  have hG9 : G - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - (3 + 0) - OPCODE_ADD = G - 32 := by
    simp only [OPCODE_ADD, OPCODE_ISZERO, VERY_LOW]
    omega
  rw [hG9] at h9
  have h10 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate)
    (pc := 19) (stack := [partialSum n k, BitVec.ofNat 256 (k + 1)]) (memory := W)
    (gas := G - 32) (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have h11 := mstore (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 21) (start := 0) (value := partialSum n k)
    (rest := [BitVec.ofNat 256 (k + 1)]) (gas := G - 32 - 3) (by decide) rfl
    (by rw [hz]; simp only; omega)
  rw [hz, memoryExtend_zero] at h11
  dsimp only at h11
  rw [show BitVec.toNat (0 : U256) = 0 from rfl,
    memoryWrite_whole (by rw [hWs, size_wordBytes])] at h11
  have h12 := Logic.push (fork := fork) (code := CODE) (message := message) (pc := 22)
    (stack := [BitVec.ofNat 256 (k + 1)]) (memory := wordBytes (partialSum n k))
    (gas := G - 32 - 3 - (3 + 0)) (state := state) (substate := substate) (n := 32)
    (word := BitVec.ofNat 256 (2 ^ 256 - 1)) (by decide) (by decide) rfl rfl (by decide)
    (by omega) (by simp [STACK_LIMIT])
  have h13 := binary (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes (partialSum n k)) (pc := 22 + (1 + 32))
    (x := BitVec.ofNat 256 (2 ^ 256 - 1)) (y := BitVec.ofNat 256 (k + 1)) (rest := [])
    (gas := G - 32 - 3 - (3 + 0) - 3) (by decide) rfl
    (ofByte_of_decode (op := .add) rfl (Fork.frontier_le _)) instruction_add
    (by simp [OPCODE_ADD, VERY_LOW]; omega)
  rw [show add (BitVec.ofNat 256 (2 ^ 256 - 1)) (BitVec.ofNat 256 (k + 1)) = BitVec.ofNat 256 k
    from allOnes_add hlt] at h13
  have h14 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate)
    (pc := 56) (stack := [BitVec.ofNat 256 k]) (memory := wordBytes (partialSum n k))
    (gas := G - 32 - 3 - (3 + 0) - 3 - OPCODE_ADD) (byte := 0x08) (by decide) rfl rfl
    (by simp [OPCODE_ADD, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have h15 := jump (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes (partialSum n k)) (pc := 58)
    (destination := 8) (rest := [BitVec.ofNat 256 k])
    (gas := G - 32 - 3 - (3 + 0) - 3 - OPCODE_ADD - 3) (by decide) rfl
    (by simp [OPCODE_ADD, VERY_LOW]; omega) (by decide)
  have h := (((((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq
    h9).seq h10).seq h11).seq h12).seq h13).seq h14).seq h15
  obtain ⟨after, hreach, hpost⟩ := h evm hrun
  refine ⟨after, hreach, by omega, ?_⟩
  rw [hn]
  have hg : G - 32 - 3 - (3 + 0) - 3 - OPCODE_ADD - 3 - 8 = gas - 18 - 55 * (n - k) := by
    simp only [OPCODE_ADD, VERY_LOW]
    omega
  rw [← hg]
  exact hpost

/-- The sum that the call returns: `n (n + 1) / 2` modulo `2^256`, as a word. -/
def total (data : ByteArray) : U256 := BitVec.ofNat 256 (triangle (count data))

/-- When the counter is 0, the code jumps out of the loop and returns the sum, for 27 gas. -/
theorem exit {gas : Nat} (hgas : 45 + 55 * count message.data ≤ gas) :
    Spec fork (Head message state substate gas 0)
      (Halted false (wordBytes (total message.data)) (gas - 45 - 55 * count message.data) state
        substate) := by
  rintro evm ⟨-, hrun⟩
  generalize hn : count message.data = n at hrun hgas
  rw [Nat.sub_zero] at hrun
  generalize hG : gas - 18 - 55 * n = G at hrun
  have hG27 : 27 ≤ G := by omega
  have hp : partialSum n 0 = BitVec.ofNat 256 (triangle n) := by
    simp [partialSum, triangle]
  rw [hp] at hrun
  generalize hW : wordBytes (BitVec.ofNat 256 (triangle n)) = W at hrun
  have hWs : W.size = 32 := by rw [← hW, size_wordBytes]
  have hz : extendMemory W.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hWs]; decide
  have h1 := jumpdest (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 8) (stack := [BitVec.ofNat 256 0])
    (gas := G) (by decide) rfl (by omega)
  have h2 := dup1 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 9) (x := BitVec.ofNat 256 0) (rest := [])
    (gas := G - 1) (by decide) rfl (by omega) (by decide)
  have h3 := unary (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 10) (x := BitVec.ofNat 256 0)
    (rest := [BitVec.ofNat 256 0]) (gas := G - 1 - 3) (by decide) rfl
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega)
  rw [show isZero (BitVec.ofNat 256 0) = 1 from rfl] at h3
  have h4 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 11) (stack := [1, BitVec.ofNat 256 0]) (memory := W)
    (gas := G - 1 - 3 - OPCODE_ISZERO) (byte := 0x3b) (by decide) rfl rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega) (by decide)
  have h5 := jumpi_taken (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 13) (destination := 0x3b) (condition := 1)
    (rest := [BitVec.ofNat 256 0]) (gas := G - 1 - 3 - OPCODE_ISZERO - 3) (by decide) rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega) (by decide) (by decide)
  have h6 := jumpdest (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 59) (stack := [BitVec.ofNat 256 0])
    (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10) (by decide) rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega)
  have h7 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 60) (stack := [BitVec.ofNat 256 0]) (memory := W)
    (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1) (byte := 0x20) (by decide) rfl rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega) (by decide)
  have h8 := Logic.push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 62) (stack := [32, BitVec.ofNat 256 0]) (memory := W)
    (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3) (byte := 0x00) (by decide) rfl rfl
    (by simp [OPCODE_ISZERO, VERY_LOW]; omega) (by decide)
  have h9 := Logic.«return» (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := W) (pc := 64) (start := 0) (size := 32)
    (rest := [BitVec.ofNat 256 0]) (gas := G - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3 - 3)
    (by decide) rfl (by rw [hz]; exact Nat.zero_le _)
  rw [hz, memoryExtend_zero] at h9
  dsimp only at h9
  have hout : memoryReadBytes W (0 : U256).toNat (32 : U256).toNat = W := by
    have := memoryReadBytes_whole (memory := W)
    rw [hWs] at this
    exact this
  rw [hout] at h9
  have h := (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9
  obtain ⟨after, hreach, hstop, hr, he, ho, hg, hs, hss⟩ := h evm hrun
  refine ⟨after, hreach, hstop, hr, he, by rw [ho, ← hW, total, hn], ?_, hs, hss⟩
  rw [hg]
  simp only [OPCODE_ISZERO, VERY_LOW]
  omega

/-! ## The specification -/

/-- The sum is `n (n + 1) / 2` modulo `2^256`, for the counter `n`. -/
theorem toNat_total (data : ByteArray) :
    (total data).toNat = count data * (count data + 1) / 2 % 2 ^ 256 := by
  simp [total, triangle]

/-- A call with at least `45 + 55 n` gas, for the counter `n`, returns the sum from 1 to `n`.

It halts normally with `45 + 55 n` gas less, and keeps its state and substate. -/
theorem spec {gas : Nat} (hgas : 45 + 55 * count message.data ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (total message.data)) (gas - 45 - 55 * count message.data) state
        substate) :=
  (start (by omega)).seq (Hoare.loop (body hgas) (exit hgas) (count message.data))

/-- The loop of the interpreter runs the call to the sum.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_spec {gas : Nat} (hgas : 45 + 55 * count message.data ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (wordBytes (total message.data))
        (gas - 45 - 55 * count message.data) state substate stopped :=
  (spec hgas).runFrame start within

end EthLib.Execution.Evm.Logic.SumLoop
