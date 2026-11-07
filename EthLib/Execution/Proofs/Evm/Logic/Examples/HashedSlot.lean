module

public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: a contract that writes a storage slot derived by hashing a key word and a base word

This example proves a contract that writes its storage at a slot it computes.

The key word is the address of the caller, and the base word is 0.

The slot is the Keccak-256 hash of the 64 bytes of the key word and then the base word.

- At 0, `60 00 35` reads the word `w` of call data at offset 0.
- At 3, `33` pushes the address of the caller as a word.
- At 4, `60 00 52` writes it at offset 0 of memory.
- At 7, `60 00 60 20 52` writes the base word at offset 32 of memory.
- At 12, `60 40 60 00 20` hashes the 64 bytes of memory from offset 0.
- At 17, `55` writes `w` to the slot at that hash.
- At 18, `60 00 80 f3` returns with no output.

The run costs 83 gas besides SSTORE.

The write pays the price of SSTORE from the original, current and new words, by EIP-2200.

The slot is cold when the transaction has not accessed it yet, by EIP-2929.

The write adds its refund to the refund counter, by EIP-2200, and from London by EIP-3529.

The frame must be one that may change the state, and the write must give a state.

The slot then holds `w`.

Nothing is stated of a read at a slot derived from another key word.

Such a read needs the two hashes to differ, and no theorem here states that.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.HashedSlot

open EthLib.Base (Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x35, 0x33, 0x60, 0x00, 0x52, 0x60, 0x00, 0x60, 0x20,
  0x52, 0x60, 0x40, 0x60, 0x00, 0x20, 0x55, 0x60, 0x00, 0x80, 0xf3]⟩

/-- The base word that the code hashes after the key word. -/
def BASE_WORD : U256 := 0

/-- The word of call data at offset 0, which the code writes. -/
abbrev word (message : Message fork) : U256 := loadWord message.data 0 32

/-- The 64 bytes that the code hashes: the address of the caller as a word, then the base word. -/
def hashed (message : Message fork) : ByteArray :=
  wordBytes message.caller.toU256 ++ wordBytes BASE_WORD

/-- The slot that the code writes: the Keccak-256 hash of those 64 bytes. -/
def slot (message : Message fork) : U256 := keccak (hashed message)

/-- The key of that slot in the storage of the current account. -/
abbrev KEY (message : Message fork) : Base.Bytes32 := U256.toBeBytes (slot message)

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The price of the write of the word to the slot. -/
abbrev writeCost (fork : Fork) (message : Message fork) (state : TransactionState) (cold : Bool) :
    Nat :=
  sstoreCost fork (state.getStorageOriginal message.currentTarget (KEY message))
    (state.getStorage message.currentTarget (KEY message)) (word message) cold

/-- The substate after the run: the slot is accessed, and the refund of the write is added. -/
abbrev endSubstate (fork : Fork) (message : Message fork) (state : TransactionState)
    (substate : Substate) : Substate :=
  { substate with
    accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
      ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert (KEY message))
    refundCounter := substate.refundCounter + sstoreRefund fork
      (state.getStorageOriginal message.currentTarget (KEY message))
      (state.getStorage message.currentTarget (KEY message)) (word message) }

/-- The size of the hashed bytes: two words. -/
theorem size_hashed (message : Message fork) : (hashed message).size = 64 := by
  simp [hashed, size_wordBytes]

/-- The code writes the key word and the base word to memory, and hashes them, for 77 gas. -/
theorem hash {gas : Nat} (hgas : 77 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 17 [slot message, word message] (hashed message) (gas - 77) state
        substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 2) (start := 0) (rest := [])
    (gas := gas - 3) (by decide) rfl (by omega)
  have h3 := caller (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 3) (stack := [word message])
    (gas := gas - 3 - 3) (by decide) rfl (by omega) (by simp [STACK_LIMIT])
  have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 4) (stack := [message.caller.toU256, word message])
    (memory := .empty) (gas := gas - 3 - 3 - 2) (byte := 0x00) (by decide) rfl rfl (by omega)
    (by simp [STACK_LIMIT])
  -- Memory grows from no word to one word, for 3 gas.
  have hg1 : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h5 := mstore (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 6) (start := 0)
    (value := message.caller.toU256) (rest := [word message]) (gas := gas - 3 - 3 - 2 - 3)
    (by decide) rfl (by rw [hg1]; simp only; omega)
  have hm1 : memoryWrite (memoryExtend ByteArray.empty
      (extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))]).expandBy)
      (0 : U256).toNat (wordBytes message.caller.toU256) = wordBytes message.caller.toU256 := by
    rw [hg1]
    exact memoryWrite_whole (by simp [size_memoryExtend, size_wordBytes])
  have h5' := Hoare.memory_eq h5 hm1
  rw [hg1] at h5'
  dsimp only at h5'
  have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 7) (stack := [word message])
    (memory := wordBytes message.caller.toU256) (gas := gas - 3 - 3 - 2 - 3 - (3 + 3))
    (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have h7 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 9) (stack := [BASE_WORD, word message])
    (memory := wordBytes message.caller.toU256) (gas := gas - 3 - 3 - 2 - 3 - (3 + 3) - 3)
    (byte := 0x20) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  -- Memory grows from one word to two words, for 3 more gas.
  have hg2 : extendMemory (wordBytes message.caller.toU256).size
      [((32 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_wordBytes]
    decide
  have h8 := mstore (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes message.caller.toU256) (pc := 11) (start := 32)
    (value := BASE_WORD) (rest := [word message]) (gas := gas - 3 - 3 - 2 - 3 - (3 + 3) - 3 - 3)
    (by decide) rfl (by rw [hg2]; simp only; omega)
  have hm2 : memoryWrite (memoryExtend (wordBytes message.caller.toU256)
      (extendMemory (wordBytes message.caller.toU256).size
        [((32 : U256), (32 : U256))]).expandBy)
      (32 : U256).toNat (wordBytes BASE_WORD) = hashed message := by
    rw [hg2]
    have h := memoryWrite_extend_end (memory := wordBytes message.caller.toU256)
      (value := wordBytes BASE_WORD)
    rw [size_wordBytes, size_wordBytes] at h
    exact h
  have h8' := Hoare.memory_eq h8 hm2
  rw [hg2] at h8'
  dsimp only at h8'
  have hs := size_hashed message
  have h9 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 12) (stack := [word message]) (memory := hashed message)
    (gas := gas - 3 - 3 - 2 - 3 - (3 + 3) - 3 - 3 - (3 + 3)) (byte := 0x40) (by decide) rfl rfl
    (by omega) (by simp [STACK_LIMIT])
  have h10 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 14) (stack := [64, word message]) (memory := hashed message)
    (gas := gas - 3 - 3 - 2 - 3 - (3 + 3) - 3 - 3 - (3 + 3) - 3) (byte := 0x00) (by decide) rfl
    rfl (by omega) (by simp [STACK_LIMIT])
  have hw : keccak256Cost (64 : U256) = 30 + 6 * 2 := by decide
  -- The 64 bytes are in memory already, so hashing them grows nothing.
  have hk : extendMemory (hashed message).size [((0 : U256), (64 : U256))] = ⟨0, 0⟩ := by
    rw [hs]
    decide
  have h11 := keccak256 (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := hashed message) (pc := 16) (start := 0) (size := 64)
    (rest := [word message]) (gas := gas - 3 - 3 - 2 - 3 - (3 + 3) - 3 - 3 - (3 + 3) - 3 - 3)
    (by decide) rfl (by rw [hk, hw]; simp only; omega)
  have hread : memoryReadBytes (memoryExtend (hashed message)
      (extendMemory (hashed message).size [((0 : U256), (64 : U256))]).expandBy)
      (0 : U256).toNat (64 : U256).toNat = hashed message := by
    rw [hk, memoryExtend_zero]
    have := memoryReadBytes_whole (memory := hashed message)
    rw [hs] at this
    exact this
  have hext : memoryExtend (hashed message)
      (extendMemory (hashed message).size [((0 : U256), (64 : U256))]).expandBy =
      hashed message := by
    rw [hk, memoryExtend_zero]
  rw [hread, hext, hw, hk] at h11
  have h := (((((((((h1.seq h2).seq h3).seq h4).seq h5').seq h6).seq h7).seq h8').seq h9).seq
    h10).seq h11
  exact Hoare.gas_eq h (by simp only; omega)

/-- The specification of the contract: it returns with no output in the state `state'`.

That is the state that the write of `w` to the slot it derives gives.

The frame may change the state, and holds more than the stipend of 2300 gas at the write.

It holds the gas of the whole run. -/
theorem spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    {state' : TransactionState} (hstatic : message.isStatic = false)
    (hcold : decide (KEY message ∉ substate.accessedStorageKeys.getD message.currentTarget ∅) =
      cold)
    (hset : (state.recordStorageRead message.currentTarget (KEY message)).setStorage
      message.currentTarget (KEY message) (word message) = .ok state')
    {gas : Nat} (hgas : 83 + writeCost fork message state cold ≤ gas)
    (hstipend : 77 + CALL_STIPEND < gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - 83 - writeCost fork message state cold) state'
        (endSubstate fork message state substate)) := by
  have hs := size_hashed message
  have h1 := hash (fork := fork) (message := message) (state := state) (substate := substate)
    (gas := gas) (by omega)
  have h2 := sstore (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := hashed message) (pc := 17) (key := slot message)
    (new := word message) (rest := []) (gas := gas - 77) (state' := state') hfork hglam
    (by decide) rfl hstatic hcold (by omega) (by show writeCost fork message state cold ≤ _; omega)
    hset
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state')
    (substate := endSubstate fork message state substate) (pc := 18) (stack := [])
    (memory := hashed message) (gas := gas - 77 - writeCost fork message state cold)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h4 := dup1 (fork := fork) (code := CODE) (message := message) (state := state')
    (substate := endSubstate fork message state substate) (memory := hashed message) (pc := 20)
    (x := 0) (rest := []) (gas := gas - 77 - writeCost fork message state cold - 3) (by decide)
    rfl (by omega) (by decide)
  -- A range of size 0 does not grow memory.
  have hz : extendMemory (hashed message).size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [hs]
    decide
  have h5 := Logic.«return» (fork := fork) (code := CODE) (message := message) (state := state')
    (substate := endSubstate fork message state substate) (memory := hashed message) (pc := 21)
    (start := 0) (size := 0) (rest := [])
    (gas := gas - 77 - writeCost fork message state cold - 3 - 3) (by decide) rfl
    (by rw [hz]; exact Nat.zero_le _)
  have h := (((h1.seq h2).seq h3).seq h4).seq h5
  refine Spec.consequence h (fun _ x => x) fun evm ⟨hr, he, ho, hg, hst, hss⟩ =>
    ⟨hr, he, by simpa [hz, memoryReadBytes] using ho, by
      have hc : (extendMemory (hashed message).size [(0, 0)]).cost = 0 := by rw [hz]
      rw [hc] at hg
      omega, hst, hss⟩

/-- The loop of the interpreter runs the code to its specification.

The slot derived from the caller and the base word then holds `w`.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    {state' : TransactionState} (hstatic : message.isStatic = false)
    (hcold : decide (KEY message ∉ substate.accessedStorageKeys.getD message.currentTarget ∅) =
      cold)
    (hset : (state.recordStorageRead message.currentTarget (KEY message)).setStorage
      message.currentTarget (KEY message) (word message) = .ok state')
    {gas : Nat} (hgas : 83 + writeCost fork message state cold ≤ gas)
    (hstipend : 77 + CALL_STIPEND < gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false .empty (gas - 83 - writeCost fork message state cold) state'
        (endSubstate fork message state substate) stopped ∧
      stopped.state.getStorage message.currentTarget (KEY message) = word message := by
  obtain ⟨stopped, ran, hq⟩ :=
    (spec hfork hglam hstatic hcold hset hgas hstipend).runFrame start within
  refine ⟨stopped, ran, hq, ?_⟩
  rw [hq.2.2.2.2.1]
  exact State.TransactionState.getStorage_setStorage_self hset

end EthLib.Execution.Evm.Logic.HashedSlot
