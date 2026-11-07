module

public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallFlag
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: a contract that adds 1 to a word of its storage

This example proves a contract that writes its storage.

- At 0, `60 00 54` reads the word `v` of the slot at key 0 of the current account.
- At 3, `60 01 01` adds 1 to it.
- At 6, `80` keeps a copy of the sum.
- At 7, `60 00 55` writes the sum to the slot at key 0.
- At 10, `60 00 52` writes the sum at offset 0 of memory.
- At 13, `60 20 60 00 f3` returns those 32 bytes.

The read of the slot makes it warm, so the write pays no cold surcharge, by EIP-2929.

The write pays the price of SSTORE from the original, current and new words, by EIP-2200.

It adds the refund of the write to the refund counter, by EIP-3529.

The frame must be one that may change the state, with the account of the current address.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Counter

open EthLib.Base (Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x54, 0x60, 0x01, 0x01, 0x80, 0x60, 0x00, 0x55, 0x60, 0x00,
  0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The key of the slot that the contract reads and writes: the word 0. -/
def KEY : Base.Bytes32 := U256.toBeBytes 0

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The price of the read of the slot: 2100 when cold and 100 when warm, by EIP-2929. -/
def readCost (cold : Bool) : Nat := if cold then 2100 else 100

/-- The word of the slot when the frame starts. -/
abbrev current (message : Message fork) (state : TransactionState) : U256 :=
  state.getStorage message.currentTarget KEY

/-- The price of the write of the sum to the slot, which is warm. -/
abbrev writeCost (fork : Fork) (message : Message fork) (state : TransactionState) : Nat :=
  sstoreCost fork (state.getStorageOriginal message.currentTarget KEY) (current message state)
    (current message state + 1) false

/-- The substate after the run: the slot is accessed, and the refund of the write is added. -/
abbrev endSubstate (fork : Fork) (message : Message fork) (state : TransactionState)
    (substate : Substate) : Substate :=
  { substate with
    accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
      ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert KEY)
    refundCounter := substate.refundCounter + sstoreRefund fork
      (state.getStorageOriginal message.currentTarget KEY) (current message state)
      (current message state + 1) }

/-- A second access to a slot of an address leaves the accessed slots as the first left them. -/
theorem accessed_insert_insert (keys : Std.ExtTreeMap Base.Address (Std.ExtTreeSet Base.Bytes32))
    (address : Base.Address) (key : Base.Bytes32) :
    (keys.insert address ((keys.getD address ∅).insert key)).insert address
        (((keys.insert address ((keys.getD address ∅).insert key)).getD address ∅).insert key) =
      keys.insert address ((keys.getD address ∅).insert key) := by
  have hset : ((keys.getD address ∅).insert key).insert key = (keys.getD address ∅).insert key := by
    apply Std.ExtTreeSet.ext_mem
    intro k
    simp only [Std.ExtTreeSet.mem_insert]
    constructor
    · rintro (h | h | h) <;> simp_all
    · rintro (h | h) <;> simp_all
  rw [Std.ExtTreeMap.getD_insert_self, hset]
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [Std.ExtTreeMap.getElem?_insert]
  split <;> rfl

/-- The specification of the contract: it writes `v + 1` to the slot and returns it.

The frame may change the state, and the write gives the state `state'`.

It holds more than the stipend of 2300 gas at the write, and the gas of the whole run. -/
theorem spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    {state' : TransactionState} (hstatic : message.isStatic = false)
    (hcold : decide (KEY ∉ substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hset : ((state.recordStorageRead message.currentTarget KEY).recordStorageRead
      message.currentTarget KEY).setStorage message.currentTarget KEY
      (current message state + 1) = .ok state')
    {gas : Nat} (hgas : 15 + readCost cold + writeCost fork message state + 15 ≤ gas)
    (hstipend : 15 + readCost cold + CALL_STIPEND < gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (current message state + 1))
        (gas - 30 - readCost cold - writeCost fork message state) state'
        (endSubstate fork message state substate)) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := sload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 2) (key := 0) (rest := []) (gas := gas - 3)
    hfork (by decide) rfl hcold (by show readCost cold ≤ gas - 3; omega)
  have h3 := push1 (code := CODE) (fork := fork) (message := message)
    (state := state.recordStorageRead message.currentTarget KEY)
    (substate := { substate with
      accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
        ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert KEY) })
    (pc := 3) (stack := [current message state]) (memory := .empty)
    (gas := gas - 3 - readCost cold) (byte := 0x01) (by decide) rfl rfl
    (by omega) (by simp [STACK_LIMIT])
  -- The state and the substate after the read of the slot.
  generalize hst1 : state.recordStorageRead message.currentTarget KEY = st1 at h3
  generalize hss1 : ({ substate with
      accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
        ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert KEY) } : Substate) =
    ss1 at h3
  have h4 := binary (fork := fork) (code := CODE) (message := message) (state := st1)
    (substate := ss1) (memory := .empty) (pc := 5) (x := 1) (y := current message state)
    (rest := []) (gas := gas - 3 - readCost cold - 3) (by decide) rfl
    (ofByte_of_decode (op := .add) rfl (Fork.frontier_le _)) instruction_add
    (by simp only [OPCODE_ADD, VERY_LOW]; omega)
  have hsum : add 1 (current message state) = current message state + 1 := BitVec.add_comm _ _
  rw [hsum] at h4
  have h5 := dup1 (fork := fork) (code := CODE) (message := message) (state := st1)
    (substate := ss1) (memory := .empty) (pc := 6) (x := current message state + 1) (rest := [])
    (gas := gas - 3 - readCost cold - 3 - OPCODE_ADD) (by decide) rfl
    (by simp only [OPCODE_ADD, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := st1)
    (substate := ss1) (pc := 7)
    (stack := [current message state + 1, current message state + 1]) (memory := .empty)
    (gas := gas - 3 - readCost cold - 3 - OPCODE_ADD - 3) (byte := 0x00) (by decide) rfl rfl
    (by simp only [OPCODE_ADD, VERY_LOW]; omega) (by simp [STACK_LIMIT])
  -- The read of the slot made it warm.
  have hwarm : decide (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat) ∉
      ss1.accessedStorageKeys.getD message.currentTarget ∅) = false := by
    subst hss1
    simp [KEY, Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insert]
  have h7 := sstore (fork := fork) (code := CODE) (message := message) (state := st1)
    (substate := ss1) (memory := .empty) (pc := 9) (key := BitVec.ofNat 256 (0 : UInt8).toNat)
    (new := current message state + 1) (rest := [current message state + 1])
    (gas := gas - 3 - readCost cold - 3 - OPCODE_ADD - 3 - 3) (state' := state')
    hfork hglam (by decide) rfl hstatic hwarm (by simp only [OPCODE_ADD, VERY_LOW]; omega)
    (by subst hst1; show writeCost fork message state ≤ _; simp only [OPCODE_ADD, VERY_LOW]; omega)
    (by subst hst1; exact hset)
  -- The substate after the write: the slot accessed once, and the refund added.
  generalize hss2 : ({ ss1 with
      accessedStorageKeys := ss1.accessedStorageKeys.insert message.currentTarget
        ((ss1.accessedStorageKeys.getD message.currentTarget ∅).insert
          (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat)))
      refundCounter := ss1.refundCounter + sstoreRefund fork
        (st1.getStorageOriginal message.currentTarget
          (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat)))
        (st1.getStorage message.currentTarget
          (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat))) (current message state + 1) } :
      Substate) = ss2 at h7
  have hss2' : ss2 = endSubstate fork message state substate := by
    subst hss2 hss1 hst1
    simp only [endSubstate, KEY]
    congr 1
    exact accessed_insert_insert _ _ _
  have hcost : sstoreCost fork
      (st1.getStorageOriginal message.currentTarget
        (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat)))
      (st1.getStorage message.currentTarget
        (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat))) (current message state + 1) false =
      writeCost fork message state := by
    subst hst1
    rfl
  rw [hcost, hss2'] at h7
  generalize hG : gas - 3 - readCost cold - 3 - OPCODE_ADD - 3 - 3 - writeCost fork message state =
    G at h7
  have hG' : 15 ≤ G := by
    subst hG
    simp only [OPCODE_ADD, VERY_LOW]
    omega
  have h8 := push1 (code := CODE) (fork := fork) (message := message) (state := state')
    (substate := endSubstate fork message state substate) (pc := 10)
    (stack := [current message state + 1]) (memory := .empty) (gas := G) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h9 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 12)
    (start := 0) (value := current message state + 1) (rest := []) (memory := .empty)
    (gas := G - 3) (state := state') (substate := endSubstate fork message state substate)
    (by decide) rfl (by simp only [hext]; omega)
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [hext, h0, CallFlag.memoryWrite_word] at h9
  have h10 := push1 (code := CODE) (fork := fork) (message := message) (state := state')
    (substate := endSubstate fork message state substate) (pc := 13) (stack := [])
    (memory := wordBytes (current message state + 1)) (gas := G - 3 - (3 + 3)) (byte := 0x20)
    (by decide) rfl rfl (by omega) (by decide)
  have h11 := push1 (code := CODE) (fork := fork) (message := message) (state := state')
    (substate := endSubstate fork message state substate) (pc := 15) (stack := [32])
    (memory := wordBytes (current message state + 1)) (gas := G - 3 - (3 + 3) - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have hext' : extendMemory (wordBytes (current message state + 1)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have h12 := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 17)
    (start := 0) (size := 32) (rest := []) (memory := wordBytes (current message state + 1))
    (gas := G - 3 - (3 + 3) - 3 - 3) (state := state')
    (substate := endSubstate fork message state substate) (by decide) rfl
    (by rw [hext']; exact Nat.zero_le _)
  rw [hext'] at h12
  have hread : memoryReadBytes (memoryExtend (wordBytes (current message state + 1)) 0)
      (0 : U256).toNat (32 : U256).toNat = wordBytes (current message state + 1) := by
    rw [memoryExtend_zero]
    have h := memoryReadBytes_whole (memory := wordBytes (current message state + 1))
    rwa [size_wordBytes] at h
  have hg : G - 3 - (3 + 3) - 3 - 3 - 0 = gas - 30 - readCost cold - writeCost fork message state :=
    by subst hG; simp only [OPCODE_ADD, VERY_LOW]; omega
  subst hst1 hss1
  have hc := h1.seq h2 |>.seq h3 |>.seq h4 |>.seq h5 |>.seq h6 |>.seq h7 |>.seq h8 |>.seq h9
    |>.seq h10 |>.seq h11
  exact Spec.seq hc (h12.consequence (fun _ hp => hp) fun _ hq => by rw [hread, hg] at hq; exact hq)

/-- The loop of the interpreter runs the code to its specification.

The slot at key 0 of the current account then holds `v + 1`.

It holds for every bound on the gas of messages and every runner of messages.

The code sends no message. -/
theorem runFrame_spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    {state' : TransactionState} (hstatic : message.isStatic = false)
    (hcold : decide (KEY ∉ substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hset : ((state.recordStorageRead message.currentTarget KEY).recordStorageRead
      message.currentTarget KEY).setStorage message.currentTarget KEY
      (current message state + 1) = .ok state')
    {gas : Nat} (hgas : 15 + readCost cold + writeCost fork message state + 15 ≤ gas)
    (hstipend : 15 + readCost cold + CALL_STIPEND < gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false (wordBytes (current message state + 1))
        (gas - 30 - readCost cold - writeCost fork message state) state'
        (endSubstate fork message state substate) stopped ∧
      stopped.state.getStorage message.currentTarget KEY = current message state + 1 := by
  obtain ⟨stopped, ran, hq⟩ :=
    (spec hfork hglam hstatic hcold hset hgas hstipend).runFrame start within
  refine ⟨stopped, ran, hq, ?_⟩
  rw [hq.2.2.2.2.1]
  exact State.TransactionState.getStorage_setStorage_self hset

end EthLib.Execution.Evm.Logic.Counter
