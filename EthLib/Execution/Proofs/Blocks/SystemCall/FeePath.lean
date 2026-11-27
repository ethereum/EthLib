module

public import EthLib.Execution.Proofs.Blocks.SystemCall.RequestQueue

/-!
# Proofs: the path of a call to a request contract from another address

The codes of EIP-7002 and EIP-7251 share their first 143 bytes, but for six bytes.

The path reads eleven of its bytes as constants.

The lemmas here run those bytes once, for every code that holds them.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.RequestQueue

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract
open EthLib.Execution.Fees.BlobBaseFee (fakeExponential)

/-- The first 143 bytes of the code of both contracts, the first byte highest.

The bytes 24, 27, 66, 67, 115, 122, 123, 127, 128, 140 and 141 hold constants, and are 0 here. -/
def FEE_PATH_NUMBER : Nat :=
  0x3373fffffffffffffffffffffffffffffffffffffffe1460005760005f54807fffffffffffffffff * 256 ^ 103 +
  0xffffffffffffffffffffffffffffffffffffffffffffffff1461000057600182026001905f5b5f82 * 256 ^ 63 +
  0x111560685781019083028483029004916001019190604d565b909390049250505036600014608857 * 256 ^ 23 +
  0x366100005734610000575f5260205ff35b341061000057

/-- A code runs the path of a call from another address, from byte 0 to byte 143.

Its bytes are those of the path, with the constants `system`, `fraction`, `revert` and `size`.

- `system` is where the call of the system address jumps to.
- `fraction` divides the excess in the exponent of the fee.
- `revert` is where four bytes revert with no output.
- `size` is the size of the input of a call that adds a request. -/
structure FeePathCode (code : ByteArray) (system fraction revert size : Nat) : Prop where
  size_le : 143 ≤ code.size
  byte : ∀ i (h : i < code.size), i < 143 → i ≠ 24 → i ≠ 27 → i ≠ 66 → i ≠ 67 → i ≠ 115 →
    i ≠ 122 → i ≠ 123 → i ≠ 127 → i ≠ 128 → i ≠ 140 → i ≠ 141 →
    code[i] = NatCode.natByte FEE_PATH_NUMBER 143 i
  -- The system address, the inhibitor, and the two other words that the path pushes.
  push1 : pushData code 1 20 = BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe
  push31 : pushData code 31 32 = BitVec.ofNat 256 (2 ^ 256 - 1)
  push117 : pushData code 117 1 = BitVec.ofNat 256 136
  push132 : pushData code 132 1 = BitVec.ofNat 256 32
  -- The words of the constants.
  push23 : pushData code 23 1 = BitVec.ofNat 256 system
  push26 : pushData code 26 1 = BitVec.ofNat 256 fraction
  push65 : pushData code 65 2 = BitVec.ofNat 256 revert
  push114 : pushData code 114 1 = BitVec.ofNat 256 size
  -- Each constant of one byte is below 256, and the call of the system address lands on a JUMPDEST.
  system_lt : system < 256
  fraction_lt : fraction < 256
  size_lt : size < 256
  dest_system : isValidJumpDest (validJumpDestinations code) system = true
  push121 : pushData code 121 2 = BitVec.ofNat 256 revert
  push126 : pushData code 126 2 = BitVec.ofNat 256 revert
  push139 : pushData code 139 2 = BitVec.ofNat 256 revert
  -- The loop of the fee runs from byte 69, and byte 136 is a valid jump destination.
  loop : FeeLoopCode code
  dest136 : isValidJumpDest (validJumpDestinations code) 136 = true
  -- From `revert`, JUMPDEST, PUSH0, PUSH0 and REVERT, where a jump may land.
  revert_lt : revert < 2 ^ 16
  revert_end : revert + 3 < code.size
  dest_revert : isValidJumpDest (validJumpDestinations code) revert = true
  revert0 : code[revert]'(by omega) = 0x5b
  revert1 : code[revert + 1]'(by omega) = 0x5f
  revert2 : code[revert + 1 + 1]'(by omega) = 0x5f
  revert3 : code[revert + 1 + 2]'(by omega) = 0xfd

namespace FeePathCode

/-- The positions of the constants in the path. -/
def FEE_PATH_CONSTANTS : List Nat := [24, 27, 66, 67, 115, 122, 123, 127, 128, 140, 141]

/-- Whether the code stored in `n` holds the bytes of the path, except at the constants. -/
def feePathNat (n size : Nat) : Bool :=
  (List.range 143).all fun i =>
    FEE_PATH_CONSTANTS.contains i ||
      NatCode.natByte n size i == NatCode.natByte FEE_PATH_NUMBER 143 i

/-- A code stored as a number holds the bytes of the path, except at the constants, by a check. -/
theorem byte_ofNat {n size : Nat} (hcheck : feePathNat n size = true) :
    ∀ i (h : i < (NatCode.ofNat n size).size), i < 143 → i ≠ 24 → i ≠ 27 → i ≠ 66 → i ≠ 67 →
      i ≠ 115 → i ≠ 122 → i ≠ 123 → i ≠ 127 → i ≠ 128 → i ≠ 140 → i ≠ 141 →
      (NatCode.ofNat n size)[i] = NatCode.natByte FEE_PATH_NUMBER 143 i := by
  intro i h hi h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [NatCode.getElem_ofNat]
  simp only [feePathNat, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem] at hcheck
  rcases hcheck i hi with hm | he
  · simp [FEE_PATH_CONSTANTS] at hm
    omega
  · exact he

variable {code : ByteArray} {system fraction revert size : Nat}
  (hc : FeePathCode code system fraction revert size)
  {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

include hc

/-- Each byte of the path lies inside the code. -/
theorem lt_size {i : Nat} (hi : i < 143) : i < code.size := by
  have := hc.size_le
  omega

/-- From `revert`, the code reverts with no output and keeps the state. -/
theorem revert_run {stack : List U256} (hfork : .shapella ≤ fork) (hstack : stack.length ≤ 6)
    (hgas : 10 ≤ gas) :
    Spec fork (At code message revert stack .empty gas state substate returnData)
      (Answer state none) := by
  have := hc.revert_end
  refine Triple.seq (jumpdest (by omega) hc.revert0 (by omega)) ?_
  exact revertEmpty hfork (by omega) hc.revert1 hc.revert2 hc.revert3
    (by simp only [STACK_LIMIT]; omega) (by omega)

/-- JUMPI to `revert`, on a condition that is not 0, reverts with no output. -/
theorem jumpi_revert {pc : Nat} {condition : U256} {rest : List U256} (hfork : .shapella ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57) (hcond : condition ≠ 0)
    (hstack : rest.length ≤ 6) (hgas : 20 ≤ gas) :
    Spec fork (At code message pc (BitVec.ofNat 256 revert :: condition :: rest) .empty gas state
      substate returnData) (Answer state none) := by
  have hr : (BitVec.ofNat 256 revert).toNat = revert := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hc.revert_lt; omega)]
  refine Triple.seq (jumpi_taken hlt hbyte (by omega) hcond (by rw [hr]; exact hc.dest_revert))
    ?_
  rw [hr]
  exact hc.revert_run hfork hstack (by omega)

/-- A call from another address reaches byte 113 with the fee, or reverts under the inhibitor. -/
theorem spec_fee {m : Nat} {Q : Evm fork Nat → Prop} (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits 1 fraction (storageOf state message.currentTarget 0).toNat m)
    (hgas : 2216 + 87 * m ≤ gas)
    -- The revert while the inhibitor holds meets `Q`.
    (hrev : storageOf state message.currentTarget 0 = EXCESS_INHIBITOR →
      ∀ evm, Answer state none evm → Q evm)
    -- So does every run on from byte 113, with the fee alone on the stack.
    --
    -- The read of slot 0 is recorded.
    (hcont : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR → ∀ g ss,
      gas - (2216 + 87 * m) ≤ g → ss.logs = substate.logs →
      Spec fork (At code message 113
        [BitVec.ofNat 256 (fakeExponential 1 (storageOf state message.currentTarget 0).toNat
          fraction)]
        .empty g (state.recordStorageRead message.currentTarget (U256.toBeBytes 0)) ss
        returnData) Q) :
    Spec fork (At code message 0 [] .empty gas state substate returnData) Q := by
  have hb := hc.byte
  have hl : ∀ i, i < 143 → i < code.size := fun _ h => hc.lt_size h
  have hc' : equal (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe)
      message.caller.toU256 = 0 := by
    rw [equal, ite_eq_right_iff]
    exact fun e => absurd e.symm (toU256_ne_of_ne_SYSTEM_ADDRESS hcaller)
  evm_step [hb, hl, hc.push1, hc.push23, hc.push26, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push1, hc.push23, hc.push26, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push1, hc.push23, hc.push26, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push1, hc.push23, hc.push26, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push1, hc.push23, hc.push26, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push1, hc.push23, hc.push26, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push1, hc.push23, hc.push26, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  refine Triple.seq (sload (code := code) (pc := 29) (gas := gas - 26) (key := 0)
    (rest := [BitVec.ofNat 256 fraction]) (Nat.le_trans (by decide) hfork)
    (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
    (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]) rfl
    (Nat.le_trans (sloadPrice_le _) (by omega))) ?_
  have hle := sloadPrice_le (decide (U256.toBeBytes 0 ∉
    substate.accessedStorageKeys.getD message.currentTarget ∅))
  generalize (if decide (U256.toBeBytes 0 ∉
    substate.accessedStorageKeys.getD message.currentTarget ∅) then 2100 else 100) = price at hle ⊢
  change Spec fork (At code message 30 (storageOf state message.currentTarget 0 ::
    [BitVec.ofNat 256 fraction]) _ _ _ _ _) Q
  generalize hx : storageOf state message.currentTarget 0 = x at hfits hcont
  evm_step [hb, hl, hc.push31, hc.push65, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push31, hc.push65, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  evm_step [hb, hl, hc.push31, hc.push65, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  have hw : BitVec.ofNat 256 (2 ^ 256 - 1) = EXCESS_INHIBITOR := rfl
  evm_step [hb, hl, hc.push31, hc.push65, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
    FEE_PATH_NUMBER]
  by_cases hinh : x = EXCESS_INHIBITOR
  · have hz : equal (BitVec.ofNat 256 (2 ^ 256 - 1)) x ≠ 0 := by simp [equal, hinh, hw]
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    refine Spec.consequence (hc.jumpi_revert hfork (hl 68 (by decide))
      (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]) hz
      (by simp) (by omega)) (fun _ h => h) fun evm h => ?_
    exact hrev (hx.trans hinh) evm (h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _))
  · have hz : equal (BitVec.ofNat 256 (2 ^ 256 - 1)) x = 0 := by
      rw [equal, ite_eq_right_iff, hw]
      exact fun e => absurd e.symm hinh
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    evm_step [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
    refine Triple.seq (feeLoop hfork hc.loop (d := fraction) (hfits hinh) ?_) ?_
    · omega
    rintro evm ⟨g', hg', hat⟩
    refine hcont hinh g' _ ?_ ?_ evm hat
    · omega
    · rfl

end FeePathCode

namespace RequestContract

variable (c : RequestContract) {system revert : Nat}
  {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- A call from another address, whose input is not a request, gets the fee or reverts.

An input is a request when its size is that of a request. -/
theorem spec_getFee {m : Nat} (hc : FeePathCode c.code system c.feeFraction revert c.inputSize)
    -- The loop of the code fixes the fee at an excess of 0 to 1 wei.
    (hmin : c.minFee = 1) (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hsize : message.data.size ≠ c.inputSize)
    -- It assumes fewer than `2^256` bytes of input, which the size word of the EVM can hold.
    (hbound : message.data.size < 2 ^ 256)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits c.minFee c.feeFraction (storageOf state message.currentTarget 0).toNat m)
    -- The frame has at least 2,300 gas, and 87 more for each of these steps.
    (hgas : 2300 + 87 * m ≤ gas) :
    Spec fork (At c.code message 0 [] .empty gas state substate returnData)
      -- The frame returns the fee as a word or reverts with no output, as the code does.
      --
      -- Its state reads as the state it starts from.
      (Answer state (c.getFeeResult (storageOf state message.currentTarget) message.data
        message.value)) := by
  have hb := hc.byte
  have hl : ∀ i, i < 143 → i < c.code.size := fun _ h => hc.lt_size h
  have hsz := hc.size_lt
  have hs : equal (BitVec.ofNat 256 c.inputSize) (BitVec.ofNat 256 message.data.size) = 0 := by
    rw [equal, ite_eq_right_iff]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound,
      Nat.mod_eq_of_lt (by omega : c.inputSize < 2 ^ 256)] at this
    omega
  rw [hmin] at hfits
  refine hc.spec_fee hfork hcaller hfits (by omega) (fun hinh evm h => ?_)
    (fun hinh g ss hg _ => ?_)
  · simp only [getFeeResult, fee, getFee, hinh, ite_true, Option.map_none, ite_self]
    exact h
  · have hread : ∀ result (evm : Evm fork Nat), Answer (state.recordStorageRead
        message.currentTarget (U256.toBeBytes 0)) result evm → Answer state result evm :=
      fun _ _ h => h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push121, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push121, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
    by_cases h0 : message.data.size = 0
    · have hz : BitVec.ofNat 256 message.data.size = 0 := by rw [h0]; rfl
      evm_step [hb, hl, hc.push126, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
      evm_step [hb, hl, hc.push126, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
      evm_step [hb, hl, hc.push126, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
      by_cases hv : message.value = 0
      · evm_step [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
        refine Spec.consequence (returnWord hfork
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
          ?_) (fun _ h => h) fun evm h => ?_
        · omega
        · simp only [getFeeResult, fee, getFee, hmin, hinh, ite_false, h0, hv, and_self,
            ite_true, Option.map_some]
          exact hread _ _ h
      · refine Spec.consequence (hc.jumpi_revert hfork (hl 129 (by decide))
          (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]) hv
          (by simp) (by omega)) (fun _ h => h) fun evm h => ?_
        simp only [getFeeResult, hv, and_false, ite_false]
        exact hread _ _ h
    · have hnz : BitVec.ofNat 256 message.data.size ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at this
        exact h0 this
      refine Spec.consequence (hc.jumpi_revert hfork (hl 124 (by decide))
        (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]) hnz
        (by simp) (by omega)) (fun _ h => h) fun evm h => ?_
      simp only [getFeeResult, h0, false_and, ite_false]
      exact hread _ _ h

/-- A call from another address, with an input of the size of a request, pays the fee or reverts.

When it pays, the run goes on from byte 143, with the read of slot 0 recorded. -/
theorem spec_pay {m : Nat} {P : Evm fork Nat → Prop}
    (hc : FeePathCode c.code system c.feeFraction revert c.inputSize)
    -- The loop of the code fixes the fee at an excess of 0 to 1 wei.
    (hmin : c.minFee = 1) (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hsize : message.data.size = c.inputSize)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits c.minFee c.feeFraction (storageOf state message.currentTarget 0).toNat m)
    -- The frame has at least 2,266 gas, and 87 more for each of these steps.
    (hgas : 2266 + 87 * m ≤ gas)
    -- Every run on from byte 143 meets `P`, when the value pays the fee.
    (hadd : c.pays (storageOf state message.currentTarget) message.value = true → ∀ g ss,
      gas - (2266 + 87 * m) ≤ g → ss.logs = substate.logs →
      Spec fork (At c.code message 143 [] .empty g
        (state.recordStorageRead message.currentTarget (U256.toBeBytes 0)) ss returnData) P) :
    Spec fork (At c.code message 0 [] .empty gas state substate returnData) fun evm =>
      -- When the value pays the fee, the frame meets `P`.
      if c.pays (storageOf state message.currentTarget) message.value then P evm
      -- Otherwise it reverts with no output, and its state reads as the state it starts from.
      else Answer state none evm := by
  have hb := hc.byte
  have hl : ∀ i, i < 143 → i < c.code.size := fun _ h => hc.lt_size h
  have hz : equal (BitVec.ofNat 256 c.inputSize) (BitVec.ofNat 256 message.data.size) ≠ 0 := by
    rw [hsize]
    simp [equal]
  rw [hmin] at hfits
  refine hc.spec_fee hfork hcaller hfits (by omega) (fun hinh evm h => ?_)
    (fun hinh g ss hg hlogs => ?_)
  · simp only [pays, fee, getFee, hinh, ite_true]
    exact h
  · have hF : fakeExponential 1 (storageOf state message.currentTarget 0).toNat c.feeFraction <
        2 ^ 256 := by
      obtain ⟨h1, h2, -, -⟩ := hfits hinh
      rw [Fees.BlobBaseFee.fakeExponential_eq_partialSum h1]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h2
    have hpays : c.pays (storageOf state message.currentTarget) message.value =
        decide (fakeExponential 1 (storageOf state message.currentTarget 0).toNat
          c.feeFraction ≤ message.value.toNat) := by
      simp only [pays, fee, getFee, hmin, hinh, ite_false]
    rw [hpays] at hadd ⊢
    generalize fakeExponential 1 (storageOf state message.currentTarget 0).toNat
      c.feeFraction = F at hF hadd ⊢
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push114, hc.push117, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      FEE_PATH_NUMBER]
    refine Triple.seq (jumpi_taken (hl 119 (by decide))
      (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER])
      (by omega) hz hc.dest136) ?_
    simp only [BitVec.reduceToNat]
    evm_step [hb, hl, hc.push139, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push139, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push139, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
    evm_step [hb, hl, hc.push139, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
    by_cases hp : F ≤ message.value.toNat
    · have hlt : lessThan message.value (BitVec.ofNat 256 F) = 0 := by
        simp only [lessThan, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF]
        rw [ite_eq_right_iff]
        intro h
        omega
      evm_step [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]
      simp only [hp, decide_true, ite_true]
      exact hadd (by simp [hp]) _ _ (by omega) hlogs
    · have hlt : lessThan message.value (BitVec.ofNat 256 F) ≠ 0 := by
        simp only [lessThan, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF]
        rw [ite_eq_left (by omega)]
        decide
      simp only [hp, decide_false]
      refine Spec.consequence (hc.jumpi_revert hfork (hl 142 (by decide))
        (by evm_code [hb, hl, ne_eq, Nat.reduceEqDiff, not_false_eq_true, FEE_PATH_NUMBER]) hlt
        (by simp) (by omega)) (fun _ h => h) fun evm h => ?_
      exact h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)

end RequestContract

end EthLib.Execution.Blocks.RequestQueue
