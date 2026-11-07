module

public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: a contract that reads the slot that its call data names

This example shows that the logic proves a contract that branches on its call data.

The contract also hashes memory and reads storage.

The bytecode compares the top four bytes of the first word of its call data with `0x12345678`.

On a match, it copies the words of call data at the offsets 4 and 36 to memory.

It hashes those 64 bytes with Keccak-256, and returns the word of storage of the current account at
that hash.

Otherwise it reverts, with no output.

- At 0, `60 00 35` reads the word of call data at offset 0.
- At 3, `60 e0 1c` shifts it right by 224 bits, which leaves its top four bytes.
- At 6, `63 12 34 56 78 14` compares them with `0x12345678`.
- At 12, `60 13 57` jumps to 19 on a match.
- At 15, `60 00 80 fd` reverts with no output.
- At 19, `5b` marks the destination of the jump.
- At 20, `60 04 35 60 00 52` writes the word of call data at offset 4 at offset 0 of memory.
- At 26, `60 24 35 60 20 52` writes the word of call data at offset 36 at offset 32 of memory.
- At 32, `60 40 60 00 20` hashes the 64 bytes of memory from offset 0.
- At 37, `54` reads the slot of storage at that hash.
- At 38, `60 00 52 60 20 60 00 f3` writes the word at offset 0 of memory and returns it.

A word of call data reads as CALLDATALOAD reads it: the 32 bytes from its offset.

Bytes past the end of the call data read as zero.

The run costs 122 gas besides SLOAD, and 37 gas on the path that reverts.

SLOAD costs 2100 for a slot that the transaction has not accessed, and 100 for one it has.

The rules are those of one counter of gas, the meter of every fork before Glamsterdam, from Berlin.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.SlotOfCalldata

open EthLib.Base (Fork U256 byteAt byteAt_append eq_of_byteAt)
open GasCosts

variable {fork : Fork}

/-! ## Memory -/

/-- Growth by no byte leaves memory as it is. -/
theorem memoryExtend_zero (memory : ByteArray) : memoryExtend memory 0 = memory := by
  apply eq_of_byteAt (by simp [size_memoryExtend])
  intro i
  exact byteAt_memoryExtend memory 0 i

/-- A write of a whole memory from offset 0 gives the written bytes. -/
theorem memoryWrite_whole {memory value : ByteArray} (h : memory.size = value.size) :
    memoryWrite memory 0 value = value := by
  have hs : (memoryWrite memory 0 value).size = value.size := by
    rw [size_memoryWrite (by omega)]
    omega
  apply eq_of_byteAt hs
  intro i
  rw [byteAt_memoryWrite (by omega)]
  split
  · simp
  · rename_i hi
    rw [Base.byteAt_of_size_le (by omega), Base.byteAt_of_size_le (by omega)]

/-- A write past the end of a memory, into bytes that it grew by, appends the written bytes. -/
theorem memoryWrite_extend_end {memory value : ByteArray} :
    memoryWrite (memoryExtend memory value.size) memory.size value = memory ++ value := by
  have hs : (memoryWrite (memoryExtend memory value.size) memory.size value).size =
      (memory ++ value).size := by
    rw [size_memoryWrite (by simp [size_memoryExtend])]
    simp [size_memoryExtend]
  apply eq_of_byteAt hs
  intro i
  rw [byteAt_memoryWrite (by simp [size_memoryExtend]), byteAt_append]
  split
  · rename_i hi
    rw [ite_eq_right (by omega)]
  · rename_i hi
    by_cases hlt : i < memory.size
    · rw [ite_eq_left hlt, byteAt_memoryExtend]
    · rw [ite_eq_right hlt]
      rw [Base.byteAt_of_size_le (by simp [size_memoryExtend]; omega),
        Base.byteAt_of_size_le (by omega)]

/-- A read of a whole memory from offset 0 gives the memory. -/
theorem memoryReadBytes_whole {memory : ByteArray} :
    memoryReadBytes memory 0 memory.size = memory := by
  apply eq_of_byteAt (by rw [size_memoryReadBytes (by omega)])
  intro i
  rw [byteAt_memoryReadBytes (by omega)]
  split
  · simp
  · rename_i hi
    rw [Base.byteAt_of_size_le (by omega)]

/-! ## The code -/

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x35, 0x60, 0xe0, 0x1c, 0x63, 0x12, 0x34, 0x56, 0x78, 0x14,
  0x60, 0x13, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x60, 0x04, 0x35, 0x60, 0x00, 0x52, 0x60, 0x24,
  0x35, 0x60, 0x20, 0x52, 0x60, 0x40, 0x60, 0x00, 0x20, 0x54, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60,
  0x00, 0xf3]⟩

/-- The word that the code compares with the top four bytes of its call data. -/
def TAG : U256 := 0x12345678

/-- The top four bytes of the first word of call data, as a word. -/
def prefixOf (data : ByteArray) : U256 := bitwiseShr 0xe0 (loadWord data 0 32)

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- PUSH1 of the code, at a program counter, of a byte. -/
theorem push1 {pc : Nat} {stack : List U256} {memory : ByteArray} {gas : Nat} (byte : UInt8)
    (hlt : pc < CODE.size) (hop : CODE[pc] = 0x60) (hnext : pc + 1 < CODE.size)
    (hbyte : CODE[pc + 1] = byte) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (Running CODE message pc stack memory gas state substate)
      (Running CODE message (pc + 2) (BitVec.ofNat 256 byte.toNat :: stack) memory (gas - 3)
        state substate) := by
  have h := Logic.push (fork := fork) (code := CODE) (message := message) (pc := pc)
    (stack := stack) (memory := memory) (gas := gas) (state := state) (substate := substate)
    (n := 1) (word := BitVec.ofNat 256 byte.toNat) (by decide) hlt (by rw [hop]; decide) rfl
    (by simp [pushData, bufferRead, Base.byteAt, hnext, hbyte, Base.bytesToNat]) hgas hstack
  exact h

/-- The part of the run that every call takes: the comparison of the prefix with the tag. -/
theorem compare (hfork : .berlin ≤ fork) {gas : Nat} (hgas : 21 ≤ gas) :
    Hoare fork (Running CODE message 0 [] .empty gas state substate)
      (Running CODE message 14 [0x13, equal TAG (prefixOf message.data)] .empty (gas - 21) state
        substate) := by
  have h1 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 0) (stack := []) (memory := .empty) (gas := gas) 0x00 (by decide) rfl (by decide) rfl
    (by omega) (by decide)
  have h2 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 2) (start := 0) (rest := [])
    (gas := gas - 3) (by decide) rfl (by omega)
  have h3 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 3) (stack := [loadWord message.data 0 32]) (memory := .empty) (gas := gas - 3 - 3) 0xe0
    (by decide) rfl (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  have h4 := binary (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 5) (x := 0xe0)
    (y := loadWord message.data 0 32) (rest := []) (gas := gas - 3 - 3 - 3)
    (by decide) rfl (ofByte_of_decode_le (op := .shr) rfl (Nat.le_trans (by decide) hfork))
    instruction_shr
    (by simp [OPCODE_SHR, VERY_LOW]; omega)
  have h5 := Logic.push (fork := fork) (code := CODE) (message := message) (pc := 6)
    (stack := [prefixOf message.data]) (memory := .empty) (gas := gas - 3 - 3 - 3 - 3)
    (state := state) (substate := substate) (n := 4) (word := TAG) (by decide) (by decide)
    rfl rfl (by decide) (by omega) (by simp [STACK_LIMIT])
  have h6 := binary (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 11) (x := TAG) (y := prefixOf message.data)
    (rest := []) (gas := gas - 3 - 3 - 3 - 3 - 3)
    (by decide) rfl (ofByte_of_decode_le (op := .eq) rfl (Fork.frontier_le _)) instruction_eq
    (by simp [OPCODE_EQ, VERY_LOW]; omega)
  have h7 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 12) (stack := [equal TAG (prefixOf message.data)]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3 - 3 - 3) 0x13 (by decide) rfl (by decide) rfl (by omega)
    (by simp [STACK_LIMIT])
  have hg : gas - 3 - 3 - 3 - 3 - 3 - 3 - 3 = gas - 21 := by omega
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7)
  rw [hg] at h
  simpa [OPCODE_SHR, OPCODE_EQ, VERY_LOW, prefixOf] using h

/-- A triple whose postcondition holds of another memory, equal to the one it names. -/
theorem Hoare.memory_eq {P : Evm fork Nat → Prop} {code : ByteArray} {pc : Nat}
    {stack : List U256} {m m' : ByteArray} {gas : Nat} {st : State.TransactionState}
    {ss : Substate} (h : Hoare fork P (Running code message pc stack m gas st ss)) (hm : m = m') :
    Hoare fork P (Running code message pc stack m' gas st ss) := hm ▸ h

/-- A triple whose postcondition holds of another gas, equal to the one it names. -/
theorem Hoare.gas_eq {P : Evm fork Nat → Prop} {code : ByteArray} {pc : Nat}
    {stack : List U256} {m : ByteArray} {gas gas' : Nat} {st : State.TransactionState}
    {ss : Substate} (h : Hoare fork P (Running code message pc stack m gas st ss))
    (hg : gas = gas') : Hoare fork P (Running code message pc stack m gas' st ss) := hg ▸ h

/-! ## The path that reverts -/

/-- A call whose prefix is not the tag reverts with no output, for 37 gas. -/
theorem mismatch (hfork : .berlin ≤ fork) {gas : Nat} (hgas : 37 ≤ gas) :
    Spec fork (Running CODE message 14 [0x13, 0] .empty (gas - 21) state substate)
      (Halted true .empty (gas - 37) state substate) := by
  -- A range of size 0 does not grow memory.
  have hz : extendMemory ByteArray.empty.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by decide
  have h1 := jumpi_zero (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 14) (destination := 0x13) (rest := [])
    (gas := gas - 21) (by decide) rfl (by omega)
  have h2 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 15) (stack := []) (memory := .empty) (gas := gas - 21 - 10) 0x00 (by decide) rfl
    (by decide) rfl (by omega) (by decide)
  have h3 := dup1 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 17) (x := 0) (rest := [])
    (gas := gas - 21 - 10 - 3) (by decide) rfl (by omega) (by decide)
  have h4 := Logic.revert (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 18) (start := 0) (size := 0) (rest := [])
    (gas := gas - 21 - 10 - 3 - 3) (Nat.le_trans (by decide) hfork) (by decide) rfl
    (by rw [hz]; exact Nat.zero_le _)
  have h := ((h1.seq h2).seq h3).seq h4
  refine Spec.consequence h (fun _ x => x) fun evm ⟨hr, he, ho, hg, hs, hss⟩ =>
    ⟨hr, he, by simpa [hz, memoryReadBytes] using ho, by
      have hc : (extendMemory ByteArray.empty.size [(0, 0)]).cost = 0 := by decide
      rw [hc] at hg
      omega, hs, hss⟩

/-! ## The path that reads storage -/

/-- The 64 bytes that the code hashes: the words of call data at the offsets 4 and 36. -/
def hashed (data : ByteArray) : ByteArray :=
  wordBytes (loadWord data 4 32) ++ wordBytes (loadWord data 36 32)

/-- The key of the slot that the code reads: the Keccak-256 hash of those 64 bytes. -/
def key (data : ByteArray) : U256 := keccak (hashed data)

/-- After the jump, the code writes the two words of call data to memory, for 32 gas. -/
theorem copy {gas : Nat} (hgas : 30 ≤ gas) :
    Hoare fork (Running CODE message 20 [] .empty gas state substate)
      (Running CODE message 32 [] (hashed message.data) (gas - 30) state substate) := by
  have h1 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 20) (stack := []) (memory := .empty) (gas := gas) 0x04 (by decide) rfl (by decide) rfl
    (by omega) (by decide)
  have h2 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 22) (start := 4) (rest := [])
    (gas := gas - 3) (by decide) rfl (by omega)
  have h3 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 23) (stack := [loadWord message.data 4 32]) (memory := .empty) (gas := gas - 3 - 3)
    0x00 (by decide) rfl (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  -- Memory grows from no word to one word, for 3 gas.
  have hg1 : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h4 := mstore (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 25) (start := 0)
    (value := loadWord message.data 4 32) (rest := []) (gas := gas - 3 - 3 - 3) (by decide) rfl
    (by rw [hg1]; simp only; omega)
  have hm1 : memoryWrite (memoryExtend ByteArray.empty
      (extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))]).expandBy)
      (0 : U256).toNat (wordBytes (loadWord message.data 4 32)) =
      wordBytes (loadWord message.data 4 32) := by
    rw [hg1]
    exact memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])
  have h4' := Hoare.memory_eq h4 hm1
  rw [hg1] at h4'
  dsimp only at h4'
  have h5 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 26) (stack := []) (memory := wordBytes (loadWord message.data 4 32))
    (gas := gas - 3 - 3 - 3 - (3 + 3))
    0x24 (by decide) rfl (by decide) rfl (by omega) (by decide)
  have h6 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes (loadWord message.data 4 32)) (pc := 28)
    (start := 36) (rest := [])
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3)
    (by decide) rfl (by omega)
  have h7 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 29) (stack := [loadWord message.data 36 32])
    (memory := wordBytes (loadWord message.data 4 32))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3)
    0x20 (by decide) rfl (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  -- Memory grows from one word to two words, for 3 more gas.
  have hg2 : extendMemory (wordBytes (loadWord message.data 4 32)).size
      [((32 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_wordBytes]
    decide
  have h8 := mstore (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes (loadWord message.data 4 32)) (pc := 31)
    (start := 32) (value := loadWord message.data 36 32) (rest := [])
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3)
    (by decide) rfl (by rw [hg2]; simp only; omega)
  have hm2 : memoryWrite (memoryExtend (wordBytes (loadWord message.data 4 32))
      (extendMemory (wordBytes (loadWord message.data 4 32)).size
        [((32 : U256), (32 : U256))]).expandBy)
      (32 : U256).toNat (wordBytes (loadWord message.data 36 32)) = hashed message.data := by
    rw [hg2]
    have h := memoryWrite_extend_end (memory := wordBytes (loadWord message.data 4 32))
      (value := wordBytes (loadWord message.data 36 32))
    rw [size_wordBytes, size_wordBytes] at h
    exact h
  have h8' := Hoare.memory_eq h8 hm2
  have h := Hoare.gas_eq (((((((h1.seq h2).seq h3).seq h4').seq h5).seq h6).seq h7).seq h8')
    (by rw [hg2])
  exact h

/-- The size of the hashed bytes: two words. -/
theorem size_hashed (data : ByteArray) : (hashed data).size = 64 := by
  simp [hashed, size_wordBytes]

/-- The word of storage that the code returns, at the key that the call data names. -/
def slotWord (state : State.TransactionState) (message : Message fork) : U256 :=
  state.getStorage message.currentTarget (U256.toBeBytes (key message.data))

/-- The state once SLOAD records the read of the slot. -/
def readState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  state.recordStorageRead message.currentTarget (U256.toBeBytes (key message.data))

/-- The substate once SLOAD records the access of the slot. -/
def readSubstate (substate : Substate) (message : Message fork) : Substate :=
  { substate with
    accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
      ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
        (U256.toBeBytes (key message.data)))) }

/-- The rest of the run: hash the 64 bytes, read the slot at the hash, and return its word. -/
theorem lookup (hfork : .berlin ≤ fork) {cold : Bool}
    (hcold : decide (U256.toBeBytes (key message.data) ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    {gas : Nat} (hgas : 60 + (if cold then 2100 else 100) ≤ gas) :
    Spec fork (Running CODE message 32 [] (hashed message.data) gas state substate)
      (Halted false (wordBytes (slotWord state message))
        (gas - 60 - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message)) := by
  have hs := size_hashed message.data
  have h1 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 32) (stack := []) (memory := hashed message.data) (gas := gas) 0x40 (by decide) rfl
    (by decide) rfl (by omega) (by decide)
  have h2 := push1 (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 34) (stack := [64]) (memory := hashed message.data) (gas := gas - 3) 0x00 (by decide)
    rfl (by decide) rfl (by omega) (by decide)
  have hw : wordCount (64 : U256).toNat = 2 := by decide
  -- The 64 bytes are in memory already, so hashing them grows nothing.
  have hk : extendMemory (hashed message.data).size [((0 : U256), (64 : U256))] = ⟨0, 0⟩ := by
    rw [hs]
    decide
  have h3 := keccak256 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := hashed message.data) (pc := 36) (start := 0) (size := 64)
    (rest := []) (gas := gas - 3 - 3) (by decide) rfl (by rw [hk, hw]; simp only; omega)
  have hread : memoryReadBytes (memoryExtend (hashed message.data)
      (extendMemory (hashed message.data).size [((0 : U256), (64 : U256))]).expandBy)
      (0 : U256).toNat (64 : U256).toNat = hashed message.data := by
    rw [hk, memoryExtend_zero]
    have := memoryReadBytes_whole (memory := hashed message.data)
    rw [hs] at this
    exact this
  have hext : memoryExtend (hashed message.data)
      (extendMemory (hashed message.data).size [((0 : U256), (64 : U256))]).expandBy =
      hashed message.data := by
    rw [hk, memoryExtend_zero]
  rw [hread, hext, hw, hk] at h3
  have h3' : Hoare fork (Running CODE message 36 [0, 64] (hashed message.data) (gas - 3 - 3) state
      substate) (Running CODE message 37 [key message.data] (hashed message.data)
        (gas - 3 - 3 - (30 + 6 * 2 + 0)) state substate) := h3
  have h12 : Hoare fork (Running CODE message 32 [] (hashed message.data) gas state substate)
      (Running CODE message 36 [0, 64] (hashed message.data) (gas - 3 - 3) state substate) :=
    h1.seq h2
  have h4 := sload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := hashed message.data) (pc := 37) (key := key message.data)
    (rest := []) (cold := cold) (gas := gas - 3 - 3 - (30 + 6 * 2 + 0)) hfork (by decide) rfl
    hcold (by omega)
  -- From here the frame holds the state and the substate that record the read.
  have h5 := push1 (fork := fork) (message := message) (state := readState state message)
    (substate := readSubstate substate message) (pc := 38) (stack := [slotWord state message])
    (memory := hashed message.data)
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - if cold then 2100 else 100) 0x00 (by decide) rfl
    (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  have hm : extendMemory (hashed message.data).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs]
    decide
  have h6 := mstore (fork := fork) (code := CODE) (message := message)
    (state := readState state message) (substate := readSubstate substate message)
    (memory := hashed message.data) (pc := 40) (start := 0) (value := slotWord state message)
    (rest := []) (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3)
    (by decide) rfl (by rw [hm]; simp only; omega)
  rw [hm, memoryExtend_zero] at h6
  have hs3 : (memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))).size = 64 := by
    rw [size_memoryWrite (by simp [hs, size_wordBytes]), hs]
  have h7 := push1 (fork := fork) (message := message) (state := readState state message)
    (substate := readSubstate substate message) (pc := 41) (stack := [])
    (memory := memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message)))
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0)) 0x20
    (by decide) rfl (by decide) rfl (by omega) (by decide)
  have h8 := push1 (fork := fork) (message := message) (state := readState state message)
    (substate := readSubstate substate message) (pc := 43) (stack := [32])
    (memory := memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message)))
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0) - 3) 0x00
    (by decide) rfl (by decide) rfl (by omega) (by decide)
  have hr : extendMemory (memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs3]
    decide
  have h9 := Logic.«return» (fork := fork) (code := CODE) (message := message)
    (state := readState state message) (substate := readSubstate substate message)
    (memory := memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))) (pc := 45) (start := 0) (size := 32) (rest := [])
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0) - 3 - 3)
    (by decide) rfl (by rw [hr]; exact Nat.zero_le _)
  rw [hr, memoryExtend_zero] at h9
  have hout : memoryReadBytes (memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))) (0 : U256).toNat (32 : U256).toNat =
      wordBytes (slotWord state message) := by
    have := memoryReadBytes_memoryWrite (memory := hashed message.data) (start := 0)
      (value := wordBytes (slotWord state message)) (by simp [hs, size_wordBytes])
    rw [size_wordBytes] at this
    exact this
  rw [hout] at h9
  have h4' : Hoare fork (Running CODE message 37 [key message.data] (hashed message.data)
        (gas - 3 - 3 - (30 + 6 * 2 + 0)) state substate)
      (Running CODE message 38 [slotWord state message] (hashed message.data)
        (gas - 3 - 3 - (30 + 6 * 2 + 0) - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message)) := h4
  have h := ((((((h12.seq h3').seq h4').seq h5).seq h6).seq h7).seq h8).seq h9
  have hfinal : gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0) - 3 -
      3 - 0 = gas - 60 - (if cold then 2100 else 100) := by
    split <;> omega
  exact Spec.consequence h (fun _ x => x) fun _ ⟨hr, he, ho, hg, hst, hss⟩ =>
    ⟨hr, he, ho, hg.trans hfinal, hst, hss⟩

/-! ## The specification -/

/-- A call whose prefix is the tag returns the word of storage at the key that its call data
names.

It pays 122 gas and SLOAD, which costs 2100 for a cold slot and 100 for a warm one.

It records the read and the access of the slot. -/
theorem spec_match (hfork : .berlin ≤ fork) (hprefix : prefixOf message.data = TAG) {cold : Bool}
    (hcold : decide (U256.toBeBytes (key message.data) ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    {gas : Nat} (hgas : 122 + (if cold then 2100 else 100) ≤ gas) :
    Spec fork (Running CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (slotWord state message))
        (gas - 122 - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message)) := by
  have hc := compare (fork := fork) (message := message) (state := state) (substate := substate)
    hfork (gas := gas) (by omega)
  have heq : equal TAG (prefixOf message.data) = 1 := by simp [equal, hprefix]
  rw [heq] at hc
  have hj := jumpi_taken (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 14) (destination := 0x13) (condition := 1)
    (rest := []) (gas := gas - 21) (by decide) rfl (by omega) (by decide) (by decide)
  have hd := jumpdest (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 19) (stack := []) (gas := gas - 21 - 10)
    (by decide) rfl (by omega)
  have hcp := copy (fork := fork) (message := message) (state := state) (substate := substate)
    (gas := gas - 21 - 10 - 1) (by omega)
  have hl := lookup (fork := fork) (message := message) (state := state) (substate := substate)
    hfork hcold (gas := gas - 21 - 10 - 1 - 30) (by split <;> split at hgas <;> omega)
  have hfinal : gas - 21 - 10 - 1 - 30 - 60 - (if cold then 2100 else 100) =
      gas - 122 - (if cold then 2100 else 100) := by
    split <;> omega
  rw [hfinal] at hl
  exact (((hc.seq hj).seq hd).seq hcp).seq hl

/-- A call whose prefix is not the tag reverts with no output, for 37 gas.

It reads no storage, so it keeps its state and substate. -/
theorem spec_mismatch (hfork : .berlin ≤ fork) (hprefix : prefixOf message.data ≠ TAG)
    {gas : Nat} (hgas : 37 ≤ gas) :
    Spec fork (Running CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 37) state substate) := by
  have hc := compare (fork := fork) (message := message) (state := state) (substate := substate)
    hfork (gas := gas) (by omega)
  have heq : equal TAG (prefixOf message.data) = 0 := by simp [equal, Ne.symm hprefix]
  rw [heq] at hc
  exact hc.seq (mismatch hfork hgas)

/-- The loop of the interpreter runs a matching call to the word of storage it names.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_match (hfork : .berlin ≤ fork) (hprefix : prefixOf message.data = TAG)
    {cold : Bool} (hcold : decide (U256.toBeBytes (key message.data) ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    {gas : Nat} (hgas : 122 + (if cold then 2100 else 100) ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : Running CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (wordBytes (slotWord state message))
        (gas - 122 - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message) stopped :=
  (spec_match hfork hprefix hcold hgas).runFrame start within

/-- The loop of the interpreter runs a call that does not match to a revert with no output. -/
theorem runFrame_mismatch (hfork : .berlin ≤ fork) (hprefix : prefixOf message.data ≠ TAG)
    {gas : Nat} (hgas : 37 ≤ gas) {bound : Nat} {runChild : MessageRunner fork Nat bound}
    {evm : Evm fork Nat} (start : Running CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted true .empty (gas - 37) state substate stopped :=
  (spec_mismatch hfork hprefix hgas).runFrame start within

end EthLib.Execution.Evm.Logic.SlotOfCalldata
