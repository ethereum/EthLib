module

public import EthLib.Execution.Proofs.Evm.Logic.Subroutine
public import EthLib.Execution.Proofs.Evm.Logic.Stack
public import EthLib.Execution.Proofs.Evm.Logic.Loop

/-!
# Proofs: a contract that writes an array of words to memory with a loop

This example proves a loop over frames that know ranges of memory, with its gas in its invariant.

The contract reads the word `n` of call data at offset 0, and writes `n` words to memory.

The word at offset `32 i` is `i`, for each `i` below `n`.

It writes them from the last one down, so memory grows only at the first write.

It then returns the `32 n` bytes of memory from offset 0.

- At 0, `60 00 35` reads the counter, the word of call data at offset 0.
- At 3, `5b 80 15 60 13 57` marks the head of the loop, and jumps to 19 when the counter is 0.
- At 9, `60 01 90 03` takes 1 from the counter.
- At 13, `60 03 81` pushes the return address 3 and a copy of the counter.
- At 16, `60 1d 56` calls the subroutine at 29, which returns to the head of the loop.
- At 19, `5b 60 00 35 60 20 02` computes `32 n` from the word of call data.
- At 26, `60 00 f3` returns the `32 n` bytes of memory from offset 0.
- At 29, `5b 80 60 20 02 52 56` writes the word `i` at offset `32 i`, and jumps back.

The word `n` must be below `2^251`, so that `32 n` is below `2^256`.

Each run of the loop costs 69 gas, and the growth of memory at the first run.

The rest of the code costs 44 gas.

So the call costs `44 + 69 n`, and the price of `32 n` bytes of memory.

It halts normally, returns the `n` words, and keeps its state and substate.

The subroutine has one proof over frames that know ranges of memory, for every size of memory.

The rules are those of one counter of gas, the meter of every fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Indices

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode: the loop from 0 to 28, and the subroutine that writes a word at 29. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x35, 0x5b, 0x80, 0x15, 0x60, 0x13, 0x57, 0x60, 0x01,
  0x90, 0x03, 0x60, 0x03, 0x81, 0x60, 0x1d, 0x56, 0x5b, 0x60, 0x00, 0x35, 0x60, 0x20, 0x02, 0x60,
  0x00, 0xf3, 0x5b, 0x80, 0x60, 0x20, 0x02, 0x52, 0x56]⟩

/-- The number of words: the word of call data at offset 0. -/
def count (data : ByteArray) : Nat := (loadWord data 0 32).toNat

/-- The `m` words from `k`: the words `k`, `k + 1`, up to `k + m - 1`, in order. -/
def cells : Nat → Nat → ByteArray
  | _, 0 => .empty
  | k, m + 1 => wordBytes (BitVec.ofNat 256 k) ++ cells (k + 1) m

/-- The `m` words from `k` take `32 m` bytes. -/
theorem size_cells (k m : Nat) : (cells k m).size = 32 * m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih => rw [cells, ByteArray.size_append, size_wordBytes, ih]; omega

/-- The size of memory at the head of the loop, with `k` of the `n` runs left.

Memory is empty before the first run, and holds `n` words after it. -/
def sizeAt (n k : Nat) : Nat := if k = n then 0 else 32 * n

/-- The facts at the head of the loop, with `k` of the `n` runs left.

After the first run, memory holds the words from `k` to `n - 1` from offset `32 k`. -/
def factsAt (n k : Nat) : List (Nat × ByteArray) :=
  if k = n then [] else [(32 * k, cells k (n - k))]

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- The frame at the head of the loop, with `k` runs left and `gas` gas. -/
def Head (message : Message fork) (state : State.TransactionState) (substate : Substate)
    (k gas : Nat) (evm : Evm fork Nat) : Prop :=
  k ≤ count message.data ∧
    Known CODE message 3 [BitVec.ofNat 256 k] (sizeAt (count message.data) k)
      (factsAt (count message.data) k) gas state substate evm

/-! ## The subroutine -/

/-- The subroutine at 29 writes the word `w` at offset `32 w`, with `w` modulo `2^256`.

It keeps the facts apart from the word, and costs 23 gas and the growth of memory. -/
theorem store (w : U256) (size : Nat) (facts : List (Nat × ByteArray)) :
    KnownSubroutine CODE message 29 [w] [] 2 (23 + (extendMemory size [(32 * w, 32)]).cost)
      size (size + (extendMemory size [(32 * w, 32)]).expandBy) facts
      (((32 * w).toNat, wordBytes w) :: facts.filter (Apart (32 * w).toNat 32)) state state
      substate substate := by
  intro ret rest gas valid room hgas
  simp only [List.length_cons, List.length_nil, STACK_LIMIT] at room
  have h1 := Known.of_at (size := size) (facts := facts) fun memory =>
    jumpdest (fork := fork) (code := CODE) (message := message) (pc := 29)
      (stack := [w] ++ ret :: rest) (memory := memory) (gas := gas) (state := state)
      (substate := substate) (by decide) rfl (by omega)
  have h2 := Known.of_at (size := size) (facts := facts) fun memory =>
    dup1 (fork := fork) (code := CODE) (message := message) (pc := 30) (memory := memory)
      (gas := gas - 1) (state := state) (substate := substate) (x := w) (rest := ret :: rest)
      (by decide) rfl (by omega) (by simp [STACK_LIMIT]; omega)
  have h3 := Known.of_at (size := size) (facts := facts) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 31)
      (stack := w :: w :: ret :: rest) (memory := memory) (gas := gas - 1 - 3) (state := state)
      (substate := substate) (byte := 0x20) (by decide) rfl rfl (by omega)
      (by simp [STACK_LIMIT]; omega)
  have h4 := Known.of_at (size := size) (facts := facts) fun memory =>
    binary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 33) (x := 32) (y := w)
      (rest := w :: ret :: rest) (gas := gas - 1 - 3 - 3) (by decide) rfl
      (ofByte_of_decode (op := .mul) rfl (Fork.frontier_le _)) (instruction_of_stackOnlyStep rfl)
      (by simp only [OPCODE_MUL, LOW]; omega)
  have h5 := mstore_known (fork := fork) (code := CODE) (message := message) (pc := 34)
    (size := size) (facts := facts) (gas := gas - 1 - 3 - 3 - OPCODE_MUL) (state := state)
    (substate := substate) (start := 32 * w) (value := w) (rest := ret :: rest) (by decide) rfl
    (by simp only [OPCODE_MUL, LOW]; omega)
  have h6 := Known.of_at (size := size + (extendMemory size [(32 * w, 32)]).expandBy)
    (facts := ((32 * w).toNat, wordBytes w) :: facts.filter (Apart (32 * w).toNat 32))
    fun memory =>
    jump (fork := fork) (code := CODE) (message := message) (pc := 35) (memory := memory)
      (gas := gas - 1 - 3 - 3 - OPCODE_MUL - (3 + (extendMemory size [(32 * w, 32)]).cost))
      (state := state) (substate := substate) (destination := ret) (rest := rest) (by decide)
      rfl (by simp only [OPCODE_MUL, LOW]; omega) valid
  have hg : gas - 1 - 3 - 3 - OPCODE_MUL - (3 + (extendMemory size [(32 * w, 32)]).cost) - 8 =
      gas - (23 + (extendMemory size [(32 * w, 32)]).cost) := by
    simp only [OPCODE_MUL, LOW]
    omega
  rw [hg] at h6
  exact ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6

/-! ## The loop -/

/-- The gas of the run of a loop with `k + 1` of the `n` runs left, which grows memory once.

It is `price`, and the price of `32 n` bytes of memory at the first run. -/
def runCost (price n k : Nat) : Nat := price + if k + 1 = n then memoryGasCost (32 * n) else 0

/-- The runs of such a loop cost `price` each, and the price of `32 n` bytes of memory. -/
theorem loopCost_runCost (price n : Nat) :
    Triple.loopCost (runCost price n) n = price * n + memoryGasCost (32 * n) := by
  have low : ∀ k < n, Triple.loopCost (runCost price n) k = price * k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Triple.loopCost, ih (by omega), runCost, ite_eq_right (by omega), Nat.mul_succ]
      omega
  cases n with
  | zero => rfl
  | succ m =>
    rw [Triple.loopCost, low m (by omega), runCost, ite_eq_left rfl, Nat.mul_succ price m]
    omega

/-- The count is below `2^256`, since it is a word. -/
theorem count_lt (data : ByteArray) : count data < 2 ^ 256 := (loadWord data 0 32).isLt

/-- Taking 1 from a counter that is not 0 gives the counter below it. -/
theorem sub_one {k : Nat} (h : k + 1 < 2 ^ 256) :
    sub (BitVec.ofNat 256 (k + 1)) 1 = BitVec.ofNat 256 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show k < 2 ^ 256 by omega)]
  rw [show (1 : U256).toNat = 1 from rfl]
  omega

/-- A word of a counter `k` with `32 k` below `2^256` gives the offset `32 k`. -/
theorem toNat_offset {k : Nat} (h : 32 * k < 2 ^ 256) :
    (32 * BitVec.ofNat 256 k : U256).toNat = 32 * k := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (32 : U256).toNat = 32 from rfl,
    Nat.mod_eq_of_lt (show k < 2 ^ 256 by omega), Nat.mod_eq_of_lt h]

/-- The test for zero of a counter that is not 0 gives 0. -/
theorem isZero_succ {k : Nat} (h : k + 1 < 2 ^ 256) : isZero (BitVec.ofNat 256 (k + 1)) = 0 := by
  have hne : BitVec.ofNat 256 (k + 1) ≠ 0 := by
    intro h'
    have h'' := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at h''
    simp at h''
  unfold isZero
  rw [ite_eq_right hne]

/-- The growth of memory for the write at offset `32 k`, with `k + 1` of the `n` runs left.

Memory grows to `32 n` bytes at the first run, for the price of those bytes, and not after. -/
theorem extendMemory_sizeAt {n k : Nat} (hk : k < n) (hn : n < 2 ^ 251) :
    extendMemory (sizeAt n (k + 1)) [(32 * BitVec.ofNat 256 k, 32)] =
      ⟨if k + 1 = n then memoryGasCost (32 * n) else 0, if k + 1 = n then 32 * n else 0⟩ := by
  have hoff : (32 * BitVec.ofNat 256 k : U256).toNat = 32 * k := toNat_offset (by omega)
  have h32 : (32 : U256).toNat = 32 := rfl
  unfold sizeAt
  split
  · rename_i heq
    rw [extendMemory_of_lt (by decide) (by decide) (by rw [hoff, h32]; omega), hoff, h32,
      ceil32_of_mod (by omega), show 32 * k + 32 = 32 * n by omega,
      show memoryGasCost 0 = 0 from rfl]
    rfl
  · exact extendMemory_of_le (by rw [hoff, h32]; omega)

/-- The write of the word `k` at offset `32 k`, with `k + 1` of the `n` runs left, gives the head.

The frame then has the size of memory and the facts of the head with `k` runs left. -/
theorem known_write {code : ByteArray} {pc : Nat} {stack : List U256} {gas : Nat}
    {evm : Evm fork Nat} {n k : Nat} (hk : k < n) (hn : n < 2 ^ 251)
    (h : Known code message pc stack (sizeAt n (k + 1) + if k + 1 = n then 32 * n else 0)
      (((32 * BitVec.ofNat 256 k : U256).toNat, wordBytes (BitVec.ofNat 256 k)) ::
        (factsAt n (k + 1)).filter (Apart (32 * BitVec.ofNat 256 k : U256).toNat 32))
      gas state substate evm) :
    Known code message pc stack (sizeAt n k) (factsAt n k) gas state substate evm := by
  obtain ⟨hat, hsize, -, hall⟩ := h
  have hoff : (32 * BitVec.ofNat 256 k : U256).toNat = 32 * k := toNat_offset (by omega)
  refine ⟨hat, ?_, ?_, ?_⟩
  · rw [hsize]
    unfold sizeAt
    by_cases h : k + 1 = n <;> simp [h] <;> omega
  · unfold sizeAt
    split <;> omega
  · have hw : Holds evm.memory (32 * k) (wordBytes (BitVec.ofNat 256 k)) := by
      have := hall _ (List.mem_cons_self ..)
      rwa [hoff] at this
    have hrest : Holds evm.memory (32 * k + 32) (cells (k + 1) (n - (k + 1))) := by
      by_cases h : k + 1 = n
      · rw [show n - (k + 1) = 0 by omega]
        exact holds_empty (by have := hw.1; rw [size_wordBytes] at this; exact this)
      · have := hall (32 * (k + 1), cells (k + 1) (n - (k + 1))) (List.mem_cons_of_mem _
          (List.mem_filter.mpr ⟨by simp [factsAt, h],
            by simp only [Apart, hoff, Bool.or_eq_true, decide_eq_true_eq]; omega⟩))
        rwa [show 32 * (k + 1) = 32 * k + 32 by omega] at this
    have hcells :
        cells k (n - k) = wordBytes (BitVec.ofNat 256 k) ++ cells (k + 1) (n - (k + 1)) := by
      rw [show n - k = n - (k + 1) + 1 by omega]
      rfl
    intro fact hfact
    simp only [factsAt, ite_eq_right (show ¬k = n by omega), List.mem_singleton] at hfact
    subst hfact
    rw [hcells]
    exact hw.append (by rw [size_wordBytes]; exact hrest)

/-- One run of the loop writes the word `k` at offset `32 k` and takes the counter to `k`.

The count `n` is below `2^251`.

The run costs 69 gas, and the price of `32 n` bytes of memory if it is the first. -/
theorem body (hn : count message.data < 2 ^ 251) (k g : Nat)
    (hgas : runCost 69 (count message.data) k ≤ g) :
    Hoare fork (Head message state substate (k + 1) g)
      (Head message state substate k (g - runCost 69 (count message.data) k)) := by
  unfold Head
  rintro evm ⟨hk, hknown⟩
  generalize hN : count message.data = n at hk hknown hgas hn ⊢
  have hlt : k + 1 < 2 ^ 256 := by omega
  have hc : 69 ≤ g := by unfold runCost at hgas; omega
  have h1 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    jumpdest (fork := fork) (code := CODE) (message := message) (pc := 3)
      (stack := [BitVec.ofNat 256 (k + 1)]) (memory := memory) (gas := g) (state := state)
      (substate := substate) (by decide) rfl (by omega)
  have h2 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    dup1 (fork := fork) (code := CODE) (message := message) (pc := 4) (memory := memory)
      (gas := g - 1) (state := state) (substate := substate) (x := BitVec.ofNat 256 (k + 1))
      (rest := []) (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  have h3 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    unary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 5) (x := BitVec.ofNat 256 (k + 1))
      (rest := [BitVec.ofNat 256 (k + 1)]) (gas := g - 1 - 3) (by decide) rfl
      (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
  rw [isZero_succ hlt] at h3
  have h4 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 6)
      (stack := [0, BitVec.ofNat 256 (k + 1)]) (memory := memory)
      (gas := g - 1 - 3 - OPCODE_ISZERO) (state := state) (substate := substate) (byte := 0x13)
      (by decide) rfl rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have h5 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    jumpi_zero (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 8) (destination := 0x13)
      (rest := [BitVec.ofNat 256 (k + 1)]) (gas := g - 1 - 3 - OPCODE_ISZERO - 3) (by decide) rfl
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
  have h6 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 9)
      (stack := [BitVec.ofNat 256 (k + 1)]) (memory := memory)
      (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10) (state := state) (substate := substate)
      (byte := 0x01) (by decide) rfl rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
      (by simp [STACK_LIMIT])
  have h7 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    swap (fork := fork) (code := CODE) (message := message) (pc := 11) 0 (memory := memory)
      (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3) (state := state) (substate := substate)
      (top := 1) (x := BitVec.ofNat 256 (k + 1)) (rest := [BitVec.ofNat 256 (k + 1)])
      (by decide) rfl rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
  have h8 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    binary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 12) (x := BitVec.ofNat 256 (k + 1))
      (y := 1) (rest := []) (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3) (by decide) rfl
      (ofByte_of_decode (op := .sub) rfl (Fork.frontier_le _)) instruction_sub
      (by simp only [OPCODE_ISZERO, OPCODE_SUB, VERY_LOW]; omega)
  rw [sub_one hlt] at h8
  have hg8 : g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 3 - 3 - OPCODE_SUB = g - 29 := by
    simp only [OPCODE_ISZERO, OPCODE_SUB, VERY_LOW]
    omega
  rw [hg8] at h8
  have h9 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 13)
      (stack := [BitVec.ofNat 256 k]) (memory := memory) (gas := g - 29) (state := state)
      (substate := substate) (byte := 0x03) (by decide) rfl rfl (by omega)
      (by simp [STACK_LIMIT])
  have h10 := Known.of_at (size := sizeAt n (k + 1)) (facts := factsAt n (k + 1)) fun memory =>
    dup (fork := fork) (code := CODE) (message := message) (pc := 15) 1
      (stack := [3, BitVec.ofNat 256 k]) (memory := memory) (gas := g - 29 - 3)
      (state := state) (substate := substate) (x := BitVec.ofNat 256 k) (by decide) (by decide)
      rfl (by omega) (by simp [STACK_LIMIT])
  have h11 := callKnownSubroutine (fork := fork) (code := CODE) (message := message) (pc := 16)
    (n := 1) (entry := 29) (ret := 3) (args := [BitVec.ofNat 256 k]) (results := [])
    (rest := [BitVec.ofNat 256 k]) (room := 2) (gas := g - 29 - 3 - 3) (state := state)
    (substate := substate)
    (store (BitVec.ofNat 256 k) (sizeAt n (k + 1)) (factsAt n (k + 1)))
    (by decide) (by decide) rfl (by decide) rfl (by decide) rfl (by decide) (by decide)
    (by simp [STACK_LIMIT])
    (by simp [STACK_LIMIT]) (by
      rw [extendMemory_sizeAt (by omega) hn]
      unfold runCost at hgas
      dsimp only
      omega)
  obtain ⟨after, hreach, hK⟩ :=
    (((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq
      h11 evm hknown
  rw [extendMemory_sizeAt (by omega) hn] at hK
  dsimp only at hK
  have hg : g - 29 - 3 - 3 - (11 + (23 + if k + 1 = n then memoryGasCost (32 * n) else 0)) =
      g - runCost 69 n k := by
    unfold runCost
    omega
  rw [hg] at hK
  exact ⟨after, hreach, by omega, known_write (by omega) hn hK⟩

/-- With no run left, memory holds the `n` words from offset 0. -/
theorem known_zero {code : ByteArray} {pc : Nat} {stack : List U256} {n g : Nat}
    {evm : Evm fork Nat}
    (h : Known code message pc stack (sizeAt n 0) (factsAt n 0) g state substate evm) :
    Known code message pc stack (sizeAt n 0) [(0, cells 0 n)] g state substate evm := by
  obtain ⟨hat, hsize, hmod, hall⟩ := h
  refine ⟨hat, hsize, hmod, ?_⟩
  intro fact hfact
  rw [List.mem_singleton] at hfact
  subst hfact
  by_cases h0 : n = 0
  · rw [h0]
    exact holds_empty (Nat.zero_le _)
  · have := hall (32 * 0, cells 0 (n - 0)) (by simp [factsAt, Ne.symm h0])
    simpa using this

/-- At the head with no run left, memory holds the `n` words from offset 0. -/
theorem head_zero {g : Nat} {evm : Evm fork Nat} (h : Head message state substate 0 g evm) :
    Known CODE message 3 [BitVec.ofNat 256 0] (sizeAt (count message.data) 0)
      [(0, cells 0 (count message.data))] g state substate evm :=
  known_zero h.2

/-- When the counter is 0, the code jumps out of the loop and returns the `n` words, for 38 gas. -/
theorem exit (hn : count message.data < 2 ^ 251) (g : Nat) (hgas : 38 ≤ g) :
    Spec fork (Head message state substate 0 g)
      (Halted false (cells 0 (count message.data)) (g - 38) state substate) := by
  intro evm hhead
  have hK := head_zero hhead
  generalize hS : sizeAt (count message.data) 0 = S at hK
  have e1 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    jumpdest (fork := fork) (code := CODE) (message := message) (pc := 3)
      (stack := [BitVec.ofNat 256 0]) (memory := memory) (gas := g) (state := state)
      (substate := substate) (by decide) rfl (by omega)
  have e2 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    dup1 (fork := fork) (code := CODE) (message := message) (pc := 4) (memory := memory)
      (gas := g - 1) (state := state) (substate := substate) (x := BitVec.ofNat 256 0)
      (rest := []) (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  have e3 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    unary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 5) (x := BitVec.ofNat 256 0)
      (rest := [BitVec.ofNat 256 0]) (gas := g - 1 - 3) (by decide) rfl
      (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
  rw [show isZero (BitVec.ofNat 256 0) = 1 from rfl] at e3
  have e4 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 6)
      (stack := [1, BitVec.ofNat 256 0]) (memory := memory) (gas := g - 1 - 3 - OPCODE_ISZERO)
      (state := state) (substate := substate) (byte := 0x13) (by decide) rfl rfl
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have e5 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    jumpi_taken (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 8) (destination := 0x13) (condition := 1)
      (rest := [BitVec.ofNat 256 0]) (gas := g - 1 - 3 - OPCODE_ISZERO - 3) (by decide) rfl
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by decide) (by decide)
  have e6 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    jumpdest (fork := fork) (code := CODE) (message := message) (pc := 19)
      (stack := [BitVec.ofNat 256 0]) (memory := memory)
      (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10) (state := state) (substate := substate)
      (by decide) rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
  have e7 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 20)
      (stack := [BitVec.ofNat 256 0]) (memory := memory)
      (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1) (state := state) (substate := substate)
      (byte := 0x00) (by decide) rfl rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
      (by simp [STACK_LIMIT])
  have e8 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    calldataload (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 22) (start := 0)
      (rest := [BitVec.ofNat 256 0]) (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3)
      (by decide) rfl (by simp only [OPCODE_ISZERO, VERY_LOW]; omega)
  have e9 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 23)
      (stack := [loadWord message.data (0 : U256).toNat 32, BitVec.ofNat 256 0])
      (memory := memory) (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3 - 3)
      (state := state) (substate := substate) (byte := 0x20) (by decide) rfl rfl
      (by simp only [OPCODE_ISZERO, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have e10 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    binary (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 25) (x := 32)
      (y := loadWord message.data (0 : U256).toNat 32) (rest := [BitVec.ofNat 256 0])
      (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3 - 3 - 3) (by decide) rfl
      (ofByte_of_decode (op := .mul) rfl (Fork.frontier_le _)) (instruction_of_stackOnlyStep rfl)
      (by simp only [OPCODE_ISZERO, OPCODE_MUL, VERY_LOW, LOW]; omega)
  have e11 := Known.of_at (size := S) (facts := [(0, cells 0 (count message.data))]) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 26)
      (stack := [mul 32 (loadWord message.data (0 : U256).toNat 32), BitVec.ofNat 256 0])
      (memory := memory) (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3 - 3 - 3 - OPCODE_MUL)
      (state := state) (substate := substate) (byte := 0x00) (by decide) rfl rfl
      (by simp only [OPCODE_ISZERO, OPCODE_MUL, VERY_LOW, LOW]; omega) (by simp [STACK_LIMIT])
  have hlen : (cells 0 (count message.data)).size =
      (mul 32 (loadWord message.data (0 : U256).toNat 32)).toNat := by
    rw [size_cells]
    have hc : (loadWord message.data (0 : U256).toNat 32).toNat = count message.data := rfl
    simp only [mul, BitVec.toNat_mul, hc, show (32 : U256).toNat = 32 from rfl]
    rw [Nat.mod_eq_of_lt (by omega)]
  have e12 := return_known (fork := fork) (code := CODE) (message := message) (pc := 28)
    (size := S) (facts := [(0, cells 0 (count message.data))])
    (gas := g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3 - 3 - 3 - OPCODE_MUL - 3)
    (state := state) (substate := substate) (start := 0)
    (length := mul 32 (loadWord message.data (0 : U256).toNat 32))
    (out := cells 0 (count message.data)) (rest := [BitVec.ofNat 256 0]) (by decide) rfl
    (List.mem_singleton_self _) hlen
  have hg : g - 1 - 3 - OPCODE_ISZERO - 3 - 10 - 1 - 3 - 3 - 3 - OPCODE_MUL - 3 = g - 38 := by
    simp only [OPCODE_ISZERO, OPCODE_MUL, VERY_LOW, LOW]
    omega
  rw [hg] at e12
  exact Spec.seq ((((((((((e1.seq e2).seq e3).seq e4).seq e5).seq e6).seq e7).seq e8).seq
    e9).seq e10).seq e11) e12 evm hK

/-! ## The specification -/

/-- The code reads the count and reaches the head of the loop with every run left, for 6 gas. -/
theorem start {gas : Nat} (hgas : 6 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (Head message state substate (count message.data) (gas - 6)) := by
  have s1 := Known.of_at (size := 0) (facts := []) fun memory =>
    push1 (fork := fork) (code := CODE) (message := message) (pc := 0) (stack := [])
      (memory := memory) (gas := gas) (state := state) (substate := substate) (byte := 0x00)
      (by decide) rfl rfl (by omega) (by decide)
  have s2 := Known.of_at (size := 0) (facts := []) fun memory =>
    calldataload (fork := fork) (code := CODE) (message := message) (state := state)
      (substate := substate) (memory := memory) (pc := 2) (start := 0) (rest := [])
      (gas := gas - 3) (by decide) rfl (by omega)
  intro evm hat
  obtain ⟨after, hreach, hK⟩ := (s1.seq s2) evm (known_of_at_empty hat)
  refine ⟨after, hreach, Nat.le_refl _, ?_⟩
  have hs : loadWord message.data (0 : U256).toNat 32 = BitVec.ofNat 256 (count message.data) := by
    simp [count]
  rw [hs, show gas - 3 - 3 = gas - 6 by omega] at hK
  simpa [sizeAt, factsAt] using hK

/-- The price of the call for `n` words.

It is 44, then 69 a word, and the price of `32 n` bytes of memory. -/
def price (n : Nat) : Nat := 44 + 69 * n + memoryGasCost (32 * n)

/-- A call with the count `n` below `2^251` and enough gas returns the words 0 to `n - 1`.

Each word takes 32 bytes, in order from offset 0.

It halts normally with that price less gas, and keeps its state and substate. -/
theorem spec (hn : count message.data < 2 ^ 251) {gas : Nat}
    (hgas : price (count message.data) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (cells 0 (count message.data)) (gas - price (count message.data)) state
        substate) := by
  unfold price at hgas ⊢
  have hloop := Triple.loop_gas (S := Step fork) (I := Head message state substate)
    (Q := fun g evm => evm.running = false ∧
      Halted false (cells 0 (count message.data)) g state substate evm)
    (cost := runCost 69 (count message.data)) (exitCost := 38) (fun k g hg => body hn k g hg)
    (fun g hg => exit hn g hg) (count message.data) (gas - 6)
    (by rw [loopCost_runCost]; omega)
  rw [loopCost_runCost, show gas - 6 - (69 * count message.data +
    memoryGasCost (32 * count message.data) + 38) = gas - (44 + 69 * count message.data +
    memoryGasCost (32 * count message.data)) by omega] at hloop
  exact Spec.seq (start (by omega)) hloop

/-- The loop of the interpreter runs the call to its specification.

It holds for every bound on the gas of messages and every runner of messages.

The code sends no message. -/
theorem runFrame_spec (hn : count message.data < 2 ^ 251) {gas : Nat}
    (hgas : price (count message.data) ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (cells 0 (count message.data))
        (gas - price (count message.data)) state substate stopped :=
  (spec hn hgas).runFrame start within

end EthLib.Execution.Evm.Logic.Indices
