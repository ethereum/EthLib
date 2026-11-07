module

public import EthLib.Execution.Proofs.Evm.Logic.Branch

/-!
# Proofs: a contract that branches on the first word of its call data with a table of keys

This example proves a contract whose code holds a table of two keys.

- At 0, `60 00 35` reads the word `x` of call data at offset 0.
- At 3, `80 63 11 11 11 11 14 61 00 1d 57` jumps to 29 when `x` is `0x11111111`.
- At 14, `80 63 22 22 22 22 14 61 00 28 57` jumps to 40 when `x` is `0x22222222`.
- At 25, `60 00 80 fd` reverts with no output.
- At 29, `5b 60 01 60 00 52 60 20 60 00 f3` returns the word 1.
- At 40, `5b 60 02 60 00 52 60 20 60 00 f3` returns the word 2.

Each entry of the table takes 11 bytes: a key of 4 bytes and a destination of 2.

The first key costs 47 gas, the second 69, and a word that is neither key 56.

The paths that return hold at every fork with the one-counter meter.

The path that reverts holds from Byzantium, by EIP-140.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.KeyBranch

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x35,
  0x80, 0x63, 0x11, 0x11, 0x11, 0x11, 0x14, 0x61, 0x00, 0x1d, 0x57,
  0x80, 0x63, 0x22, 0x22, 0x22, 0x22, 0x14, 0x61, 0x00, 0x28, 0x57,
  0x60, 0x00, 0x80, 0xfd,
  0x5b, 0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3,
  0x5b, 0x60, 0x02, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The first key. -/
def KEY1 : U256 := 0x11111111

/-- The second key. -/
def KEY2 : U256 := 0x22222222

/-- The entries of the table: each key with the destination of its jump. -/
def ENTRIES : List (U256 × U256) := [(KEY1, 29), (KEY2, 40)]

/-- The word of call data at offset 0, on which the code branches. -/
abbrev word (message : Message fork) : U256 := loadWord message.data 0 32

/-- The code holds the table from offset 3, with keys of 4 bytes and destinations of 2. -/
theorem table : Table CODE 4 2 3 ENTRIES :=
  ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, by decide, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, by decide,
    ⟨by decide, rfl⟩, by decide, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, by decide,
    ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, by decide, ⟨by decide, rfl⟩, by decide, trivial⟩

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- The code reads the word and runs the table, for 6 gas and 22 for each entry it tests. -/
theorem lookup {gas : Nat} (hgas : 6 + 22 * tested (word message) ENTRIES ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message (branch (word message) 3 (entrySize 4 2) ENTRIES) [word message] .empty
        (gas - 6 - 22 * tested (word message) ENTRIES) state substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 2) (start := 0) (rest := [])
    (gas := gas - 3) (by decide) rfl (by omega)
  have h3 := branchTable (fork := fork) (code := CODE) (message := message) (memory := .empty)
    (state := state) (substate := substate) (x := word message) (rest := []) (pc := 3)
    (gas := gas - 3 - 3) (by decide) (by decide) (by decide) table (by omega)
  exact Hoare.gas_eq ((h1.seq h2).seq h3) (by omega)

/-- The block at `pc` returns the word of its byte, for 19 gas. -/
theorem answer {pc : Nat} {byte : UInt8} {x : U256} {gas : Nat} (hgas : 19 ≤ gas)
    (b0 : ByteAt CODE pc 0x5b) (b1 : ByteAt CODE (pc + 1) 0x60) (b2 : ByteAt CODE (pc + 2) byte)
    (b3 : ByteAt CODE (pc + 3) 0x60) (b4 : ByteAt CODE (pc + 4) 0x00)
    (b5 : ByteAt CODE (pc + 5) 0x52) (b6 : ByteAt CODE (pc + 6) 0x60)
    (b7 : ByteAt CODE (pc + 7) 0x20) (b8 : ByteAt CODE (pc + 8) 0x60)
    (b9 : ByteAt CODE (pc + 9) 0x00) (b10 : ByteAt CODE (pc + 10) 0xf3) :
    Spec fork (At CODE message pc [x] .empty gas state substate)
      (Halted false (wordBytes (BitVec.ofNat 256 byte.toNat)) (gas - 19) state substate) := by
  obtain ⟨l0, h0⟩ := b0
  obtain ⟨l2, h2⟩ := b2
  obtain ⟨_, h1⟩ := b1
  obtain ⟨l4, h4⟩ := b4
  obtain ⟨_, h3⟩ := b3
  obtain ⟨_, h5⟩ := b5
  obtain ⟨l7, h7⟩ := b7
  obtain ⟨_, h6⟩ := b6
  obtain ⟨l9, h9⟩ := b9
  obtain ⟨_, h8⟩ := b8
  obtain ⟨l10, h10⟩ := b10
  have s1 := jumpdest (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := pc) (stack := [x]) (gas := gas) l0 h0
    (by omega)
  have s2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := pc + 1) (stack := [x]) (memory := .empty) (gas := gas - 1)
    (byte := byte) l2 h1 h2 (by omega) (by simp [STACK_LIMIT])
  have s3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := pc + 1 + 2) (stack := [BitVec.ofNat 256 byte.toNat, x])
    (memory := .empty) (gas := gas - 1 - 3) (byte := 0x00) l4 h3 h4 (by omega)
    (by simp [STACK_LIMIT])
  have hext : extendMemory ByteArray.empty.size
      [((BitVec.ofNat 256 (0 : UInt8).toNat : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have s4 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := pc + 1 + 2 + 2)
    (start := BitVec.ofNat 256 (0 : UInt8).toNat) (value := BitVec.ofNat 256 byte.toNat)
    (rest := [x]) (memory := .empty) (gas := gas - 1 - 3 - 3) (state := state)
    (substate := substate) (by omega) h5 (by simp only [hext]; omega)
  have h0' : (BitVec.ofNat 256 (0 : UInt8).toNat : U256).toNat = 0 := rfl
  have hw : memoryWrite (memoryExtend .empty 32) 0 (wordBytes (BitVec.ofNat 256 byte.toNat)) =
      wordBytes (BitVec.ofNat 256 byte.toNat) :=
    memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])
  rw [hext, h0', hw] at s4
  have s5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := pc + 1 + 2 + 2 + 1) (stack := [x])
    (memory := wordBytes (BitVec.ofNat 256 byte.toNat)) (gas := gas - 1 - 3 - 3 - (3 + 3))
    (byte := 0x20) l7 h6 h7 (by omega) (by simp [STACK_LIMIT])
  have s6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := pc + 1 + 2 + 2 + 1 + 2) (stack := [32, x])
    (memory := wordBytes (BitVec.ofNat 256 byte.toNat)) (gas := gas - 1 - 3 - 3 - (3 + 3) - 3)
    (byte := 0x00) l9 h8 h9 (by omega) (by simp [STACK_LIMIT])
  have hext' : extendMemory (wordBytes (BitVec.ofNat 256 byte.toNat)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have s7 := Logic.«return» (fork := fork) (code := CODE) (message := message)
    (pc := pc + 1 + 2 + 2 + 1 + 2 + 2) (start := 0) (size := 32) (rest := [x])
    (memory := wordBytes (BitVec.ofNat 256 byte.toNat))
    (gas := gas - 1 - 3 - 3 - (3 + 3) - 3 - 3) (state := state) (substate := substate) l10
    (by simpa using h10) (by rw [hext']; exact Nat.zero_le _)
  rw [hext', memoryExtend_zero] at s7
  have hread : memoryReadBytes (wordBytes (BitVec.ofNat 256 byte.toNat)) (0 : U256).toNat
      (32 : U256).toNat = wordBytes (BitVec.ofNat 256 byte.toNat) := by
    have h := memoryReadBytes_whole (memory := wordBytes (BitVec.ofNat 256 byte.toNat))
    rwa [size_wordBytes] at h
  have hg : gas - 1 - 3 - 3 - (3 + 3) - 3 - 3 - 0 = gas - 19 := by omega
  exact Spec.seq (((((s1.seq s2).seq s3).seq s4).seq s5).seq s6)
    (s7.consequence (fun _ hp => hp) fun _ hq => by rw [hread, hg] at hq; exact hq)

/-- A call whose word is the first key returns the word 1, for 47 gas. -/
theorem spec_key1 (hx : word message = KEY1) {gas : Nat} (hgas : 47 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 1) (gas - 47) state substate) := by
  have ht : tested (word message) ENTRIES = 1 := by simp [tested, ENTRIES, hx]
  have hb : branch (word message) 3 (entrySize 4 2) ENTRIES = 29 := by
    simp [branch, ENTRIES, hx]
  have h1 := lookup (fork := fork) (message := message) (state := state) (substate := substate)
    (gas := gas) (by rw [ht]; omega)
  rw [ht, hb] at h1
  have h2 := answer (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 29) (byte := 0x01) (x := word message) (gas := gas - 6 - 22 * 1) (by omega)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩
  have hg : gas - 6 - 22 * 1 - 19 = gas - 47 := by omega
  rw [hg] at h2
  exact Spec.seq h1 h2

/-- A call whose word is the second key returns the word 2, for 69 gas. -/
theorem spec_key2 (hx : word message = KEY2) {gas : Nat} (hgas : 69 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 2) (gas - 69) state substate) := by
  have hne : KEY1 ≠ KEY2 := by decide
  have ht : tested (word message) ENTRIES = 2 := by simp [tested, ENTRIES, hx, hne]
  have hb : branch (word message) 3 (entrySize 4 2) ENTRIES = 40 := by
    simp [branch, ENTRIES, hx, hne]
  have h1 := lookup (fork := fork) (message := message) (state := state) (substate := substate)
    (gas := gas) (by rw [ht]; omega)
  rw [ht, hb] at h1
  have h2 := answer (fork := fork) (message := message) (state := state) (substate := substate)
    (pc := 40) (byte := 0x02) (x := word message) (gas := gas - 6 - 22 * 2) (by omega)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩
  have hg : gas - 6 - 22 * 2 - 19 = gas - 69 := by omega
  rw [hg] at h2
  exact Spec.seq h1 h2

/-- From Byzantium, a call whose word is neither key reverts with no output, for 56 gas. -/
theorem spec_miss (hfork : .byzantium ≤ fork) (h1 : word message ≠ KEY1)
    (h2 : word message ≠ KEY2) {gas : Nat} (hgas : 56 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 56) state substate) := by
  have hall : ∀ e ∈ ENTRIES, e.1 ≠ word message := by
    intro e he
    simp only [ENTRIES, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Ne.symm h1
    · exact Ne.symm h2
  have ht : tested (word message) ENTRIES = 2 := tested_of_forall_ne hall
  have hb : branch (word message) 3 (entrySize 4 2) ENTRIES = 25 := by
    rw [branch_of_forall_ne hall]
    rfl
  have hl := lookup (fork := fork) (message := message) (state := state) (substate := substate)
    (gas := gas) (by rw [ht]; omega)
  rw [ht, hb] at hl
  have hz : extendMemory ByteArray.empty.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by decide
  have s1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 25) (stack := [word message]) (memory := .empty)
    (gas := gas - 6 - 22 * 2) (byte := 0x00) (by decide) rfl rfl (by omega)
    (by simp [STACK_LIMIT])
  have s2 := dup1 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 27) (x := 0) (rest := [word message])
    (gas := gas - 6 - 22 * 2 - 3) (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  have s3 := Logic.revert (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 28) (start := 0) (size := 0)
    (rest := [word message]) (gas := gas - 6 - 22 * 2 - 3 - 3) hfork (by decide) rfl
    (by rw [hz]; exact Nat.zero_le _)
  refine Spec.seq ((hl.seq s1).seq s2) (s3.consequence (fun _ hp => hp) ?_)
  rintro _ ⟨hr, he, ho, hg, hs, hss⟩
  refine ⟨hr, he, by simpa [hz, memoryReadBytes] using ho, ?_, hs, hss⟩
  have hc : (extendMemory ByteArray.empty.size [(0, 0)]).cost = 0 := by decide
  rw [hc] at hg
  rw [hg]
  omega

/-- The loop of the interpreter runs a call whose word is the first key to the word 1.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_key1 (hx : word message = KEY1) {gas : Nat} (hgas : 47 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (wordBytes 1) (gas - 47) state substate stopped :=
  (spec_key1 hx hgas).runFrame start within

/-- The loop of the interpreter runs a call whose word is the second key to the word 2.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_key2 (hx : word message = KEY2) {gas : Nat} (hgas : 69 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (wordBytes 2) (gas - 69) state substate stopped :=
  (spec_key2 hx hgas).runFrame start within

/-- From Byzantium, the loop of the interpreter runs a call whose word is neither key to a revert.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_miss (hfork : .byzantium ≤ fork) (h1 : word message ≠ KEY1)
    (h2 : word message ≠ KEY2) {gas : Nat} (hgas : 56 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted true .empty (gas - 56) state substate stopped :=
  (spec_miss hfork h1 h2 hgas).runFrame start within

end EthLib.Execution.Evm.Logic.KeyBranch
