module

public import EthLib.Execution.Proofs.Blocks.SystemCall.FeePath

/-!
# Proofs: the start of the system call of a request contract

The codes of EIP-7002 and EIP-7251 start their system call with the same 23 bytes, at two offsets.

Those bytes read the tail and the head of the queue, and take at most the maximum of requests.

One theorem proves the system call for every code that holds these bytes and the fee path.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.RequestQueue

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract

/-- The 23 bytes of the start of the system call, the first byte highest, 0 at each constant. -/
def DEQUEUE_START_NUMBER : Nat := 0x5b600354600254808203806000116000575060005b5f5b

/-- A code holds the start of the system call from the offset `o`, for at most `max` requests. -/
structure DequeueStartCode (code : ByteArray) (o max : Nat) : Prop where
  -- The bytes lie inside the code, and the jump destination and the maximum each fit in one byte.
  size_le : o + 23 ≤ code.size
  dest_lt : o + 20 < 256
  max_lt : max < 256
  byte : ∀ i (h : o + i < code.size), i < 23 → i ≠ 12 → i ≠ 15 → i ≠ 19 →
    code[o + i] = NatCode.natByte DEQUEUE_START_NUMBER 23 i
  -- The slots 3 and 2, the maximum twice, and the jump destination `o + 20`.
  push1 : pushData code (o + 1) 1 = BitVec.ofNat 256 3
  push4 : pushData code (o + 4) 1 = BitVec.ofNat 256 2
  push11 : pushData code (o + 11) 1 = BitVec.ofNat 256 max
  push14 : pushData code (o + 14) 1 = BitVec.ofNat 256 (o + 20)
  push18 : pushData code (o + 18) 1 = BitVec.ofNat 256 max
  -- The byte at `o + 20` is a valid jump destination.
  dest20 : isValidJumpDest (validJumpDestinations code) (o + 20) = true

namespace DequeueStartCode

/-- The positions of the constants in the start of the system call. -/
def CONSTANTS : List Nat := [12, 15, 19]

/-- A code stored as a number holds the start, except at the constants, when the check passes. -/
theorem byte_ofNat {n len o : Nat}
    (hcheck : holdsExcept n len o DEQUEUE_START_NUMBER 23 CONSTANTS = true) :
    ∀ i (h : o + i < (NatCode.ofNat n len).size), i < 23 → i ≠ 12 → i ≠ 15 → i ≠ 19 →
      (NatCode.ofNat n len)[o + i] = NatCode.natByte DEQUEUE_START_NUMBER 23 i := by
  intro i h hi h1 h2 h3
  exact getElem_of_holdsExcept hcheck h hi (by simp [CONSTANTS]; omega)

end DequeueStartCode

namespace RequestContract

variable (c : RequestContract) {fork : Fork} {message : Message fork} {gas : Nat}
  {state : TransactionState} {substate : Substate} {returnData : ByteArray}

set_option hygiene false in
/-- Runs one step of the start, from the bytes of the start and its bounds. -/
local macro "start_step" : tactic => `(tactic| evm_step [hstart.byte, hl', hstart.push1,
  hstart.push4, hstart.push11, hstart.push14, hstart.push18, ne_eq, Nat.reduceEqDiff,
  not_false_eq_true, DEQUEUE_START_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Proves a fact about a byte of the start, from the bytes of the start and its bounds. -/
local macro "start_code" : tactic => `(tactic| evm_code [hstart.byte, hl', ne_eq,
  Nat.reduceEqDiff, not_false_eq_true, DEQUEUE_START_NUMBER, Nat.add_assoc])

/-- A call from the system address takes requests from the queue, from the start of the code.

The code holds the fee path, whose call of the system address jumps to the start at `system`. -/
theorem spec_dequeue {system revert rest : Nat}
    (hfee : FeePathCode c.code system c.feeFraction revert c.inputSize)
    (hstart : DequeueStartCode c.code system c.maxPerBlock)
    -- From the head of the loop at `system + 22`, the code takes the requests and ends the call.
    --
    -- It needs `rest` gas, scaled from Glamsterdam.
    (hrest : ∀ (S : TransactionState) (ss : Substate) (g : Nat) (r : U256 → U256),
      (S.getAccountOptional message.currentTarget).isSome = true →
      storageOf S message.currentTarget = r → Bounded r → rest * storageGasScale fork ≤ g →
      Spec fork (At c.code message (system + 22) [BitVec.ofNat 256 0,
          BitVec.ofNat 256 (numDequeued c.maxPerBlock r), r 2, r 3] .empty g S ss returnData)
        fun evm => evm.error = none ∧
          evm.output = taken c.record r (numDequeued c.maxPerBlock r) ∧
          WritesStorage message.currentTarget (afterDequeue c.maxPerBlock c.targetPerBlock r) S
            evm.state)
    (hfork : .shapella ≤ fork) (hcaller : message.caller = SYSTEM_ADDRESS)
    -- The account of the contract exists, and its counters meet the bounds of the queue.
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hbounded : Bounded (storageOf state message.currentTarget))
    -- The frame has 5,000 gas more than the rest of the call needs, scaled from Glamsterdam.
    (hgas : (rest + 5000) * storageGasScale fork ≤ gas) :
    -- From Glamsterdam, this one-counter frame is a model for the proof, not the meter of EIP-8037.
    Spec fork (At c.code message 0 [] .empty gas state substate returnData) fun evm =>
      -- The frame stops with no error, and returns the records of the requests it takes.
      evm.error = none ∧
      evm.output = dequeued c.maxPerBlock c.record (storageOf state message.currentTarget) ∧
      -- The state holds the storage after the requests are taken, and keeps the rest.
      WritesStorage message.currentTarget
        (afterDequeue c.maxPerBlock c.targetPerBlock (storageOf state message.currentTarget))
        state evm.state := by
  have hscale := one_le_storageGasScale fork
  -- The gas of the rest of the call as one number, so that each bound on gas is linear.
  have hgas' : rest * storageGasScale fork + 5000 ≤ gas := by
    rw [Nat.add_mul] at hgas
    have := Nat.mul_le_mul_left 5000 hscale
    omega
  generalize rest * storageGasScale fork = R at hgas' hrest
  clear hgas
  have hb := hfee.byte
  have hl : ∀ i, i < 143 → i < c.code.size := fun _ h => hfee.lt_size h
  have hsys := hfee.system_lt
  have hmax := hstart.max_lt
  have hdl := hstart.dest_lt
  have hl' : ∀ i, i < 23 → system + i < c.code.size := fun _ h => by
    have := hstart.size_le
    omega
  generalize hr : storageOf state message.currentTarget = r
  have hb' := hbounded
  rw [hr] at hb'
  obtain ⟨hht, hex⟩ := hb'
  have ht := (r 3).isLt
  -- The caller check of the fee path, from byte 0 to the JUMPI at byte 25.
  evm_step [hb, hl, hfee.push1, hfee.push23, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  rw [hcaller, toU256_SYSTEM_ADDRESS]
  evm_step [hb, hl, hfee.push1, hfee.push23, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hfee.push1, hfee.push23, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hfee.push1, hfee.push23, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  -- The caller is the system address, so the JUMPI at byte 25 lands at `system`.
  have hsw : (BitVec.ofNat 256 system).toNat = system := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hj := jumpi_taken (fork := fork) (message := message) (memory := .empty) (state := state)
    (substate := substate) (returnData := returnData) (rest := [])
    (destination := BitVec.ofNat 256 system) (condition := 1) (gas := gas - 11) (hl 25 (by decide))
    (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
    (by omega) (by decide) (by rw [hsw]; exact hfee.dest_system)
  rw [hsw] at hj
  refine Triple.seq hj ?_
  change Spec fork (At c.code message (system + 0) _ _ _ _ _ _) _
  -- The start reads the tail and the head of the queue.
  start_step
  start_step
  refine sload_then (Nat.le_trans (by decide) hfork) (by start_code) (by start_code) (by omega)
    fun g₁ ss₁ hg₁ _ => ?_
  start_step
  refine sload_then (Nat.le_trans (by decide) hfork) (by start_code) (by start_code) (by omega)
    fun g₂ ss₂ hg₂ _ => ?_
  simp only [storageOf_recordStorageRead, hr]
  have hS : storageOf ((state.recordStorageRead message.currentTarget (U256.toBeBytes 3#256)
      ).recordStorageRead message.currentTarget (U256.toBeBytes 2#256)) message.currentTarget =
      r := hr
  have hacc' : (((state.recordStorageRead message.currentTarget (U256.toBeBytes 3#256)
      ).recordStorageRead message.currentTarget (U256.toBeBytes 2#256)).getAccountOptional
      message.currentTarget).isSome = true := hacc
  have hsubv : sub (r 3#256) (r 2#256) = BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat) := by
    show sub (r 3) (r 2) = _
    apply BitVec.eq_of_toNat_eq
    simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (r 2).isLt
    rw [Nat.mod_eq_of_lt (by omega : (r 3).toNat - (r 2).toNat < 2 ^ 256)]
    rw [show 2 ^ 256 - (r 2).toNat + (r 3).toNat =
      ((r 3).toNat - (r 2).toNat) + 2 ^ 256 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  -- The reads of the two slots keep the storage and the rest of the state.
  have post : ∀ evm : Evm fork Nat,
      (evm.error = none ∧ evm.output = taken c.record r (numDequeued c.maxPerBlock r) ∧
      WritesStorage message.currentTarget (afterDequeue c.maxPerBlock c.targetPerBlock r)
        ((state.recordStorageRead message.currentTarget (U256.toBeBytes 3#256)
          ).recordStorageRead message.currentTarget (U256.toBeBytes 2#256)) evm.state) →
      evm.error = none ∧ evm.output = dequeued c.maxPerBlock c.record r ∧
        WritesStorage message.currentTarget (afterDequeue c.maxPerBlock c.targetPerBlock r)
          state evm.state :=
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, WritesStorage.trans (WritesStorage.trans
      (WritesStorage.recordStorageRead message.currentTarget state message.currentTarget
        (U256.toBeBytes 3#256))
      (WritesStorage.recordStorageRead message.currentTarget _ message.currentTarget
        (U256.toBeBytes 2#256))) h3⟩
  -- The start takes the number of requests in the queue, or the maximum if it is smaller.
  start_step
  start_step
  start_step
  rw [hsubv]
  start_step
  start_step
  start_step
  start_step
  have hd256 : (r 3).toNat - (r 2).toNat < 2 ^ 256 := by omega
  have hm256 : c.maxPerBlock < 2 ^ 256 := by omega
  by_cases hd : (r 3).toNat - (r 2).toNat < c.maxPerBlock
  · -- Fewer requests than the maximum: the JUMPI lands at `system + 20`.
    have hz : greaterThan (BitVec.ofNat 256 c.maxPerBlock)
        (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)) ≠ 0 := by
      have hlt : (BitVec.ofNat 256 c.maxPerBlock).toNat >
          (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)).toNat := by
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd256, Nat.mod_eq_of_lt hm256]
        omega
      rw [greaterThan, ite_eq_left hlt]
      decide
    have hn : numDequeued c.maxPerBlock r = (r 3).toNat - (r 2).toNat :=
      Nat.min_eq_left (by omega)
    have hdw : (BitVec.ofNat 256 (system + 20)).toNat = system + 20 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine Triple.seq (jumpi_taken (hl' 16 (by decide)) (by start_code) (by omega) hz
      (by rw [hdw]; exact hstart.dest20)) ?_
    rw [hdw]
    start_step
    start_step
    rw [← hn]
    exact Spec.consequence (hrest _ ss₂ _ r hacc' hS ⟨hht, hex⟩ (by omega)) (fun _ h => h) post
  · -- At least the maximum: the code takes the maximum.
    have hz : greaterThan (BitVec.ofNat 256 c.maxPerBlock)
        (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)) = 0 := by
      rw [greaterThan, ite_eq_right_iff]
      intro h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd256, Nat.mod_eq_of_lt hm256] at h
      omega
    have hn : numDequeued c.maxPerBlock r = c.maxPerBlock := Nat.min_eq_right (by omega)
    start_step
    start_step
    start_step
    start_step
    start_step
    refine Spec.reshape (s' := [BitVec.ofNat 256 0, BitVec.ofNat 256 (numDequeued c.maxPerBlock r),
      r 2, r 3]) (by rw [hn]; rfl) rfl rfl ?_
    exact Spec.consequence (hrest _ ss₂ _ r hacc' hS ⟨hht, hex⟩ (by omega)) (fun _ h => h) post

end RequestContract

end EthLib.Execution.Blocks.RequestQueue
