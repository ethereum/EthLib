module

public import EthLib.Execution.Proofs.Evm.Logic.Steps
public import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# Proofs: a contract that reads the slot that its call data names

This example shows that the logic proves a contract that branches on its call data.

The contract also hashes memory and reads storage.

The bytecode compares the top four bytes of the first word of its call data with `0x12345678`.

On a match, it copies the words of call data at the offsets 4 and 36 to memory.

It hashes those 64 bytes with Keccak-256, and returns the word of storage at that hash.

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
- At 37, `54` reads the slot of storage of the current account at that hash.
- At 38, `60 00 52 60 20 60 00 f3` writes the word at offset 0 of memory and returns it.

A word of call data reads as CALLDATALOAD reads it: the 32 bytes from its offset.

Bytes past the end of the call data read as zero.

The run costs 122 gas besides SLOAD, and 37 gas on the path that reverts.

SLOAD costs 2100 for a slot that the transaction has not accessed, and 100 for one it has.

The rules are those of one counter of gas, the meter of every fork before Glamsterdam, from Berlin.

The code is stored as one number, so a fact about its bytes is evaluated on that number.

A tactic runs the opcodes of the stack and the jumps.

The proofs apply the rules for memory, storage and the halts by hand.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.SlotOfCalldata

open EthLib.Base (Fork U256 byteAt byteAt_append eq_of_byteAt)
open GasCosts

variable {fork : Fork}

/-! ## The code -/

/-- The bytecode as one number, whose highest byte is the first byte of the code. -/
def CODE_NAT : Nat :=
  0x60003560e01c631234567814601357600080fd5b60043560005260243560205260406000205460005260206000f3

/-- The bytecode of the contract: the 46 bytes of its number.

No proof unfolds it: proofs rewrite it by its equation, and evaluate its bytes on the number. -/
@[irreducible] def CODE : ByteArray := NatCode.ofNat CODE_NAT 46

/-- The equation of the code, which proofs rewrite by. -/
theorem CODE_eq : CODE = NatCode.ofNat CODE_NAT 46 := by
  unfold CODE
  rfl

/-- Proves a fact about the bytes of the code, by evaluation on its number. -/
local macro "code_fact" : tactic => `(tactic| evm_code [CODE_eq, CODE_NAT])

/-- The word that the code compares with the top four bytes of its call data. -/
def TAG : U256 := 0x12345678

/-- The top four bytes of the first word of call data, as a word. -/
def prefixOf (data : ByteArray) : U256 := bitwiseShr 0xe0 (loadWord data 0 32)

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- The part of the run that every call takes: the comparison of the prefix with the tag. -/
theorem compare (hfork : .berlin ≤ fork) {gas : Nat} (hgas : 21 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 14 [0x13, equal TAG (prefixOf message.data)] .empty (gas - 21) state
        substate) := by
  iterate 7 evm_step [CODE_eq, CODE_NAT]
  exact Triple.of_imp fun _ h => h

/-! ## The path that reverts -/

/-- A call whose prefix is not the tag reverts with no output, for 37 gas. -/
theorem mismatch (hfork : .berlin ≤ fork) {gas : Nat} (hgas : 37 ≤ gas) :
    Spec fork (At CODE message 14 [0x13, 0] .empty (gas - 21) state substate)
      (Halted true .empty (gas - 37) state substate) := by
  -- A range of size 0 does not grow memory.
  have hz : extendMemory ByteArray.empty.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by decide
  iterate 3 evm_step [CODE_eq, CODE_NAT]
  have h := Logic.revert (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 18) (start := 0) (size := 0) (rest := [])
    (gas := gas - 37) (Nat.le_trans (by decide) hfork) (by code_fact)
    (by code_fact) (by rw [hz]; exact Nat.zero_le _)
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
    Hoare fork (At CODE message 20 [] .empty gas state substate)
      (At CODE message 32 [] (hashed message.data) (gas - 30) state substate) := by
  iterate 3 evm_step [CODE_eq, CODE_NAT]
  -- Memory grows from no word to one word, for 3 gas, and a pushed word reads as `n#256`.
  have hg1 : extendMemory ByteArray.empty.size [(0#256, (32 : U256))] = ⟨3, 32⟩ := by decide
  have hm1 : memoryWrite (memoryExtend ByteArray.empty
      (extendMemory ByteArray.empty.size [(0#256, (32 : U256))]).expandBy)
      (0 : U256).toNat (wordBytes (loadWord message.data 4 32)) =
      wordBytes (loadWord message.data 4 32) := by
    rw [hg1]
    exact memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])
  refine Triple.seq (Hoare.gas_eq (Hoare.memory_eq (mstore (by code_fact)
    (by code_fact) (by rw [hg1]; simp only; omega)) hm1)
    (show _ = gas - 15 by rw [hg1]; simp only; omega)) ?_
  iterate 3 evm_step [CODE_eq, CODE_NAT]
  -- Memory grows from one word to two words, for 3 more gas.
  have hg2 : extendMemory (wordBytes (loadWord message.data 4 32)).size
      [(32#256, (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_wordBytes]
    decide
  have hm2 : memoryWrite (memoryExtend (wordBytes (loadWord message.data 4 32))
      (extendMemory (wordBytes (loadWord message.data 4 32)).size
        [(32#256, (32 : U256))]).expandBy)
      (32 : U256).toNat (wordBytes (loadWord message.data 36 32)) = hashed message.data := by
    rw [hg2]
    have h := memoryWrite_extend_end (memory := wordBytes (loadWord message.data 4 32))
      (value := wordBytes (loadWord message.data 36 32))
    rw [size_wordBytes, size_wordBytes] at h
    exact h
  refine Triple.seq (Hoare.gas_eq (Hoare.memory_eq (mstore (by code_fact)
    (by code_fact) (by rw [hg2]; simp only; omega)) hm2)
    (show _ = gas - 30 by rw [hg2]; simp only; omega)) ?_
  exact Triple.of_imp fun _ h => h

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
    Spec fork (At CODE message 32 [] (hashed message.data) gas state substate)
      (Halted false (wordBytes (slotWord state message))
        (gas - 60 - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message)) := by
  have hs := size_hashed message.data
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 32) (stack := []) (memory := hashed message.data) (gas := gas)
    (byte := 0x40) (by code_fact) (by code_fact) (by code_fact) (by omega) (by decide)
  have h2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 34) (stack := [64]) (memory := hashed message.data)
    (gas := gas - 3) (byte := 0x00) (by code_fact) (by code_fact) (by code_fact) (by omega)
    (by decide)
  have hw : keccak256Cost (64 : U256) = 30 + 6 * 2 := by decide
  -- The 64 bytes are in memory already, so hashing them grows nothing.
  have hk : extendMemory (hashed message.data).size [((0 : U256), (64 : U256))] = ⟨0, 0⟩ := by
    rw [hs]
    decide
  have h3 := keccak256 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := hashed message.data) (pc := 36) (start := 0) (size := 64)
    (rest := []) (gas := gas - 3 - 3) (by code_fact) (by code_fact)
    (by rw [hk, hw]; simp only; omega)
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
  have h3' : Hoare fork (At CODE message 36 [0, 64] (hashed message.data) (gas - 3 - 3) state
      substate) (At CODE message 37 [key message.data] (hashed message.data)
        (gas - 3 - 3 - (30 + 6 * 2 + 0)) state substate) := h3
  have h12 : Hoare fork (At CODE message 32 [] (hashed message.data) gas state substate)
      (At CODE message 36 [0, 64] (hashed message.data) (gas - 3 - 3) state substate) :=
    h1.seq h2
  have h4 := sload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := hashed message.data) (pc := 37) (key := key message.data)
    (rest := []) (cold := cold) (gas := gas - 3 - 3 - (30 + 6 * 2 + 0)) hfork (by code_fact)
    (by code_fact)
    hcold (by omega)
  -- From here the frame holds the state and the substate that record the read.
  have h5 := push1 (code := CODE) (fork := fork) (message := message)
    (state := readState state message) (substate := readSubstate substate message) (pc := 38)
    (stack := [slotWord state message]) (memory := hashed message.data)
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - if cold then 2100 else 100) (byte := 0x00)
    (by code_fact)
    (by code_fact) (by code_fact) (by omega) (by simp [STACK_LIMIT])
  have hm : extendMemory (hashed message.data).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs]
    decide
  have h6 := mstore (fork := fork) (code := CODE) (message := message)
    (state := readState state message) (substate := readSubstate substate message)
    (memory := hashed message.data) (pc := 40) (start := 0) (value := slotWord state message)
    (rest := []) (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3)
    (by code_fact) (by code_fact) (by rw [hm]; simp only; omega)
  rw [hm, memoryExtend_zero] at h6
  have hs3 : (memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))).size = 64 := by
    rw [size_memoryWrite (by simp [hs, size_wordBytes]), hs]
  have h7 := push1 (code := CODE) (fork := fork) (message := message)
    (state := readState state message) (substate := readSubstate substate message) (pc := 41)
    (stack := [])
    (memory := memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message)))
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0))
    (byte := 0x20) (by code_fact) (by code_fact) (by code_fact) (by omega) (by decide)
  have h8 := push1 (code := CODE) (fork := fork) (message := message)
    (state := readState state message) (substate := readSubstate substate message) (pc := 43)
    (stack := [32])
    (memory := memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message)))
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0) - 3)
    (byte := 0x00) (by code_fact) (by code_fact) (by code_fact) (by omega) (by decide)
  have hr : extendMemory (memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs3]
    decide
  have h9 := Logic.«return» (fork := fork) (code := CODE) (message := message)
    (state := readState state message) (substate := readSubstate substate message)
    (memory := memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))) (pc := 45) (start := 0) (size := 32) (rest := [])
    (gas := gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0) - 3 - 3)
    (by code_fact) (by code_fact) (by rw [hr]; exact Nat.zero_le _)
  rw [hr, memoryExtend_zero] at h9
  have hout : memoryReadBytes (memoryWrite (hashed message.data) (0 : U256).toNat
      (wordBytes (slotWord state message))) (0 : U256).toNat (32 : U256).toNat =
      wordBytes (slotWord state message) := by
    have := memoryReadBytes_memoryWrite (memory := hashed message.data) (start := 0)
      (value := wordBytes (slotWord state message)) (by simp [hs, size_wordBytes])
    rw [size_wordBytes] at this
    exact this
  rw [hout] at h9
  have h4' : Hoare fork (At CODE message 37 [key message.data] (hashed message.data)
        (gas - 3 - 3 - (30 + 6 * 2 + 0)) state substate)
      (At CODE message 38 [slotWord state message] (hashed message.data)
        (gas - 3 - 3 - (30 + 6 * 2 + 0) - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message)) := h4
  have h := ((((((h12.seq h3').seq h4').seq h5).seq h6).seq h7).seq h8).seq h9
  have hfinal : gas - 3 - 3 - (30 + 6 * 2 + 0) - (if cold then 2100 else 100) - 3 - (3 + 0) - 3 -
      3 - 0 = gas - 60 - (if cold then 2100 else 100) := by
    split <;> omega
  exact Spec.consequence h (fun _ x => x) fun _ ⟨hr, he, ho, hg, hst, hss⟩ =>
    ⟨hr, he, ho, hg.trans hfinal, hst, hss⟩

/-! ## The specification -/

/-- A call whose prefix is the tag returns the word of storage at the key its call data names.

It pays 122 gas and SLOAD, which costs 2100 for a cold slot and 100 for a warm one.

It records the read and the access of the slot. -/
theorem spec_match (hfork : .berlin ≤ fork) (hprefix : prefixOf message.data = TAG) {cold : Bool}
    (hcold : decide (U256.toBeBytes (key message.data) ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    {gas : Nat} (hgas : 122 + (if cold then 2100 else 100) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (slotWord state message))
        (gas - 122 - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message)) := by
  have hc := compare (fork := fork) (message := message) (state := state) (substate := substate)
    hfork (gas := gas) (by omega)
  have heq : equal TAG (prefixOf message.data) = 1 := by simp [equal, hprefix]
  rw [heq] at hc
  have hj := jumpi_taken (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 14) (destination := 0x13) (condition := 1)
    (rest := []) (gas := gas - 21) (by code_fact) (by code_fact) (by omega) (by decide)
    (by evm_dest [CODE_eq, CODE_NAT])
  have hd := jumpdest (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 19) (stack := []) (gas := gas - 21 - 10)
    (by code_fact) (by code_fact) (by omega)
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
    Spec fork (At CODE message 0 [] .empty gas state substate)
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
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (wordBytes (slotWord state message))
        (gas - 122 - if cold then 2100 else 100) (readState state message)
        (readSubstate substate message) stopped :=
  (spec_match hfork hprefix hcold hgas).runFrame start within

/-- The loop of the interpreter runs a call that does not match to a revert with no output. -/
theorem runFrame_mismatch (hfork : .berlin ≤ fork) (hprefix : prefixOf message.data ≠ TAG)
    {gas : Nat} (hgas : 37 ≤ gas) {bound : Nat} {runChild : MessageRunner fork Nat bound}
    {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted true .empty (gas - 37) state substate stopped :=
  (spec_mismatch hfork hprefix hgas).runFrame start within

end EthLib.Execution.Evm.Logic.SlotOfCalldata
