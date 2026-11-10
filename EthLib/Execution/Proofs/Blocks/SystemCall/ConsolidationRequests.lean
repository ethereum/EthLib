module

public import EthLib.Execution.Proofs.Blocks.SystemCall.RequestQueue

/-!
# Proofs: the consolidation request contract of EIP-7251 does what its EIP describes

The contract keeps a queue of consolidation requests, and a fee that rises with its use.

Its code is the 414 bytes of [EIP-7251][eip-7251-deployment], which its deployment installs.

A call from any other address with no input and no value gets the fee.

A call with 96 bytes of input adds a request, when its value pays the fee.

The input is the public key of the source validator, then that of the target validator.

The request holds the caller and the input, in four slots, and the call logs them.

A call from the system address takes at most 2 requests from the head of the queue.

It returns their records of 116 bytes each, and updates the excess for a target of 1 per block.

Each operation of [the EIP][eip-7251-contract] is a function here.

A theorem runs the code and shows that it computes that function.

It holds from Shapella, which adds PUSH0, up to BPO5, for a frame that counts gas as one number.

From Pectra up to BPO5, a system call to the contract succeeds.

It returns the requests and leaves the storage that the EIP describes.

At every fork from Pectra, the request phase of a block fails if this contract has no code.

This holds once the withdrawal request call before it succeeds.

[eip-7251-deployment]: https://eips.ethereum.org/EIPS/eip-7251#deployment
[eip-7251-contract]: https://eips.ethereum.org/EIPS/eip-7251#consolidation-request-contract
-/

@[expose] public section

namespace EthLib.Execution.Blocks.ConsolidationRequests

open EthLib.Base (Fork U256 Address)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract
open EthLib.Execution.Blocks.RequestQueue
open GasCosts
open EthLib.Base (byteAt_extract)
open EthLib.Execution.Fees.BlobBaseFee (fakeExponential)

/-! ## The contract -/

/-- The most requests that a block takes from the queue, 2, by EIP-7251. -/
def MAX_CONSOLIDATION_REQUESTS_PER_BLOCK : Nat := 2

/-- The requests per block that keep the fee where it is, 1, by EIP-7251. -/
def TARGET_CONSOLIDATION_REQUESTS_PER_BLOCK : Nat := 1

/-- The fee at an excess of 0, 1 wei, by EIP-7251. -/
def MIN_CONSOLIDATION_REQUEST_FEE : Nat := 1

/-- The divisor of the excess in the exponent of the fee, 17, by EIP-7251. -/
def CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION : Nat := 17

/-- The slots of each request in the queue: the caller, then the 96 bytes of input in three. -/
def SLOTS_PER_REQUEST : Nat := 4

/-- The code of the contract as one number: its 414 bytes, the first byte highest.

The input of the deployment transaction of EIP-7251 is 45 bytes of constructor, then these bytes.

Here they come in ten runs of 40 bytes, then a run of 14 bytes. -/
def CODE_NUMBER : Nat :=
  0x3373fffffffffffffffffffffffffffffffffffffffe1460d35760115f54807fffffffffffffffff * 256 ^ 374 +
  0xffffffffffffffffffffffffffffffffffffffffffffffff1461019a57600182026001905f5b5f82 * 256 ^ 334 +
  0x111560685781019083028483029004916001019190604d565b909390049250505036606014608857 * 256 ^ 294 +
  0x3661019a573461019a575f5260205ff35b341061019a576001546001016001556003548060040260 * 256 ^ 254 +
  0x04013381556001015f358155600101602035815560010160403590553360601b5f5260605f601437 * 256 ^ 214 +
  0x60745fa0600101600355005b6003546002548082038060021160e7575060025b5f5b818114610129 * 256 ^ 174 +
  0x5782810160040260040181607402815460601b815260140181600101548152602001816002015481 * 256 ^ 134 +
  0x526020019060030154905260010160e9565b910180921461013b5790600255610146565b90505f60 * 256 ^ 94 +
  0x02555f6003555b5f54807fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 256 ^ 54 +
  0xffffff141561017357505f5b6001546001828201116101885750505f61018e565b01600190035b5f * 256 ^ 14 +
  0x555f6001556074025ff35b5f5ffd

/-- The code of the consolidation request contract, 414 bytes, by EIP-7251. -/
def CODE : ByteArray := NatCode.ofNat CODE_NUMBER 414

/-! ## The operations -/

/-- The fee to add a request with the storage `read`, or none while the inhibitor holds. -/
def fee (read : U256 → U256) : Option Nat :=
  getFee MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION (read 0)

/-- What a call with the input `input` and the value `value` gets, when it adds no request.

With no input and no value, it gets the fee as a word, or reverts while the inhibitor holds.

Any input of a size other than 0 or 96 bytes reverts, and so does a value with no input.

The EIP gives only the fee for no input; these reverts come from its code. -/
def getFeeResult (read : U256 → U256) (input : ByteArray) (value : U256) : Option U256 :=
  if input.size = 0 ∧ value = 0 then (fee read).map (BitVec.ofNat 256) else none

/-- A call with the value `value` pays the fee: the fee is defined and at most the value. -/
def pays (read : U256 → U256) (value : U256) : Bool :=
  match fee read with
  | some f => decide (f ≤ value.toNat)
  | none => false

/-- The four words of a request from `caller` with the input `input`, as the queue holds them.

They are the caller, then the three words of the input, read big-endian. -/
def requestWords (caller : Address) (input : ByteArray) : List U256 :=
  [caller.toU256, loadWord input 0 32, loadWord input 32 32, loadWord input 64 32]

/-- The data of the log of a request: the 20 bytes of the caller, then the input. -/
def logData (caller : Address) (input : ByteArray) : ByteArray :=
  (wordBytes caller.toU256).extract 12 32 ++ input

/-- The record of 116 bytes of the request at the index `index` of the queue, from `read`.

It is the source address, the public key of the source, then that of the target.

The address is the last 20 bytes of the first slot, since the code stores the caller as a word.

The two keys are the 96 bytes of the next three slots. -/
def record (read : U256 → U256) (index : U256) : ByteArray :=
  let slot := 4 + 4 * index
  (wordBytes (read slot)).extract 12 32 ++ wordBytes (read (slot + 1)) ++
    wordBytes (read (slot + 2)) ++ wordBytes (read (slot + 3))

/-! ## The loop of the fee -/

/-- The number of the code as a run of 14 bytes, then ten runs of 40 bytes. -/
theorem CODE_NUMBER_eq : CODE_NUMBER =
    ((((((((((0x3373ffffffffffffffffffffffff * 256 ^ 40 +
    0xfffffffffffffffe1460d35760115f54807fffffffffffffffffffffffffffffffffffffffffffff) * 256 ^ 40 +
    0xffffffffffffffffffff1461019a57600182026001905f5b5f821115606857810190830284830290) * 256 ^ 40 +
    0x04916001019190604d565b9093900492505050366060146088573661019a573461019a575f526020) * 256 ^ 40 +
    0x5ff35b341061019a57600154600101600155600354806004026004013381556001015f3581556001) * 256 ^ 40 +
    0x01602035815560010160403590553360601b5f5260605f60143760745fa0600101600355005b6003) * 256 ^ 40 +
    0x546002548082038060021160e7575060025b5f5b8181146101295782810160040260040181607402) * 256 ^ 40 +
    0x815460601b8152601401816001015481526020018160020154815260200190600301549052600101) * 256 ^ 40 +
    0x60e9565b910180921461013b5790600255610146565b90505f6002555f6003555b5f54807fffffff) * 256 ^ 40 +
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff141561017357505f5b6001) * 256 ^ 40 +
    0x546001828201116101885750505f61018e565b01600190035b5f555f6001556074025ff35b5f5ffd) := by
  decide +kernel


/-- The code runs the loop of the fee from byte 69, as the withdrawal request contract does. -/
theorem feeLoopCode_CODE : FeeLoopCode CODE :=
  FeeLoopCode.of_ofNat (by decide) (by rw [CODE_NUMBER_eq, FEE_LOOP_NUMBER]; decide +kernel)
    (by evm_dest [CODE_NUMBER_eq]) (by evm_dest [CODE_NUMBER_eq])

/-! ## A call that adds no request -/

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- JUMPDEST, PUSH0, PUSH0 and REVERT, at byte 410, revert with no output. -/
private theorem revert_410 {stack : List U256} (hfork : .shapella ≤ fork)
    (hstack : stack.length ≤ 6) (hgas : 10 ≤ gas) :
    Spec fork (At CODE message 410 stack .empty gas state substate returnData)
      (Answer state none) := by
  evm_step [CODE, CODE_NUMBER_eq]
  exact revertEmpty hfork (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (by simp only [STACK_LIMIT]; omega) (by omega)

/-- A call from another address computes the fee, from byte 0 to byte 113.

It reverts with no output while the inhibitor holds.

Otherwise it reaches byte 113 with the fee on the stack, the read of slot 0 recorded. -/
private theorem user_fee {m : Nat} {Q : Evm fork Nat → Prop} (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS)
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    (hgas : 2216 + 87 * m ≤ gas)
    (hrev : storageOf state message.currentTarget 0 = EXCESS_INHIBITOR →
      ∀ evm, Answer state none evm → Q evm)
    (hcont : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR → ∀ g ss,
      gas - (2216 + 87 * m) ≤ g → ss.logs = substate.logs →
      Spec fork (At CODE message 113
        [BitVec.ofNat 256 (fakeExponential MIN_CONSOLIDATION_REQUEST_FEE
          (storageOf state message.currentTarget 0).toNat
          CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION)]
        .empty g (state.recordStorageRead message.currentTarget (U256.toBeBytes 0)) ss
        returnData) Q) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) Q := by
  have hc : equal (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe)
      message.caller.toU256 = 0 := by
    rw [equal, ite_eq_right_iff]
    exact fun e => absurd e.symm (toU256_ne_of_ne_SYSTEM_ADDRESS hcaller)
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine Triple.seq (sload (code := CODE) (pc := 29) (gas := gas - 26) (key := 0)
    (rest := [17#256]) (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) rfl (Nat.le_trans (sloadPrice_le _) (by omega))) ?_
  have hle := sloadPrice_le (decide (U256.toBeBytes 0 ∉
    substate.accessedStorageKeys.getD message.currentTarget ∅))
  generalize (if decide (U256.toBeBytes 0 ∉
    substate.accessedStorageKeys.getD message.currentTarget ∅) then 2100 else 100) = price at hle ⊢
  change Spec fork (At CODE message 30 (storageOf state message.currentTarget 0 :: [17#256]) _ _ _
    _ _) Q
  generalize hx : storageOf state message.currentTarget 0 = x at hfits hcont
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have hw : BitVec.ofNat 256 (2 ^ 256 - 1) = EXCESS_INHIBITOR := rfl
  by_cases hinh : x = EXCESS_INHIBITOR
  · have hz : equal (BitVec.ofNat 256 (2 ^ 256 - 1)) x ≠ 0 := by simp [equal, hinh, hw]
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine Spec.consequence (revert_410 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
    · simp
    · omega
    · exact hrev (hx.trans hinh) evm (h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _))
  · have hz : equal (BitVec.ofNat 256 (2 ^ 256 - 1)) x = 0 := by
      rw [equal, ite_eq_right_iff, hw]
      exact fun e => absurd e.symm hinh
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine Triple.seq (feeLoop hfork feeLoopCode_CODE (d := 17) (hfits hinh) ?_) ?_
    · omega
    rintro evm ⟨g', hg', hat⟩
    refine hcont hinh g' _ ?_ ?_ evm hat
    · omega
    · rfl

/-- A call from another address, whose input is not 96 bytes, gets the fee or reverts.

It holds from Shapella up to BPO5; the bound on the fork matches the other theorems.

The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.

The frame has at least 100,000 gas, and 100 more for each of these steps.

It assumes fewer than `2^256` bytes of input, which the size word of the EVM can hold.

The frame returns the fee as a word, or reverts with no output, as the code of the EIP does.

Its state reads as the state it starts from. -/
theorem spec_getFee {m : Nat} (hfork : .shapella ≤ fork) (_hglam : fork < .glamsterdam)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hsize : message.data.size ≠ 96)
    (hbound : message.data.size < 2 ^ 256)
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    (hgas : 100000 + 100 * m ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData)
      (Answer state (getFeeResult (storageOf state message.currentTarget) message.data
        message.value)) := by
  have hs : equal 96#256 (BitVec.ofNat 256 message.data.size) = 0 := by
    rw [equal, ite_eq_right_iff]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at this
    omega
  refine user_fee hfork hcaller hfits (by omega) (fun hinh evm h => ?_)
    (fun hinh g ss hg _ => ?_)
  · simp only [getFeeResult, fee, getFee, hinh, ite_true, Option.map_none, ite_self]
    exact h
  · evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    have hread : ∀ result (evm : Evm fork Nat), Answer (state.recordStorageRead
        message.currentTarget (U256.toBeBytes 0)) result evm → Answer state result evm :=
      fun _ _ h => h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)
    by_cases h0 : message.data.size = 0
    · have hz : BitVec.ofNat 256 message.data.size = 0 := by rw [h0]; rfl
      evm_step [CODE, CODE_NUMBER_eq]
      evm_step [CODE, CODE_NUMBER_eq]
      evm_step [CODE, CODE_NUMBER_eq]
      evm_step [CODE, CODE_NUMBER_eq]
      by_cases hv : message.value = 0
      · evm_step [CODE, CODE_NUMBER_eq]
        refine Spec.consequence (returnWord hfork (by evm_code [CODE, CODE_NUMBER_eq])
          (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
          (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
          (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq]) ?_)
          (fun _ h => h) fun evm h => ?_
        · omega
        · simp only [getFeeResult, fee, getFee, hinh, ite_false, h0, hv, and_self, ite_true,
            Option.map_some]
          exact hread _ _ h
      · evm_step [CODE, CODE_NUMBER_eq]
        refine Spec.consequence (revert_410 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
        · simp
        · omega
        · simp only [getFeeResult, hv, and_false, ite_false]
          exact hread _ _ h
    · have hnz : BitVec.ofNat 256 message.data.size ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at this
        exact h0 this
      evm_step [CODE, CODE_NUMBER_eq]
      evm_step [CODE, CODE_NUMBER_eq]
      refine Spec.consequence (revert_410 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
      · simp
      · omega
      · simp only [getFeeResult, h0, false_and, ite_false]
        exact hread _ _ h

/-! ## A call that adds a request -/

/-- From byte 143, the code adds the request of the caller and the input, and logs it. -/
private theorem add_tail {S : TransactionState} {ss : Substate} {g : Nat}
    (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam) (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hsize : message.data.size = 96) (hgas : 150000 ≤ g) :
    Spec fork (At CODE message 143 [] .empty g S ss returnData)
      (Added SLOTS_PER_REQUEST message.currentTarget (requestWords message.caller message.data)
        (logData message.caller message.data) S ss) := by
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g0 ss0 hg0 hl0 => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc (by omega)
    fun S1 hw1 hacc1 g1 ss1 hg1 hl1 => ?_
  have hw1 := WritesStorage.trans (WritesStorage.recordStorageRead _ _ _ _) hw1
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g2 ss2 hg2 hl2 => ?_
  have h3 : storageOf S1 message.currentTarget 3#256 = storageOf S message.currentTarget 3#256 := by
    rw [hw1.1]
    simp only [setSlot]
    rfl
  rw [h3]
  have hw2 := WritesStorage.trans hw1
    (WritesStorage.recordStorageRead _ S1 message.currentTarget (U256.toBeBytes 3#256))
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  generalize ht : storageOf S message.currentTarget 3#256 = t at hw2 ⊢
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc1 (by omega)
    fun S3 hw3 hacc3 g3 ss3 hg3 hl3 => ?_
  have hw3 := WritesStorage.trans hw2 hw3
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc3 (by omega)
    fun S4 hw4 hacc4 g4 ss4 hg4 hl4 => ?_
  have hw4 := WritesStorage.trans hw3 hw4
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc4 (by omega)
    fun S5 hw5 hacc5 g5 ss5 hg5 hl5 => ?_
  have hw5 := WritesStorage.trans hw4 hw5
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc5 (by omega)
    fun S6 hw6 hacc6 g6 ss6 hg6 hl6 => ?_
  have hw6 := WritesStorage.trans hw5 hw6
  have hg6' : 35000 ≤ g6 := by omega
  clear hg0 hg1 hg2 hg3 hg4 hg5 hg6 hgas
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine Triple.seq (mstore (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq])
    (by simp only [ByteArray.size_empty, extendMemory_word]; omega)) ?_
  rw [ByteArray.size_empty, extendMemory_word]
  dsimp only
  rw [show BitVec.toNat (0 : U256) = 0 from rfl,
    memoryWrite_whole (by rw [size_memoryExtend, size_wordBytes]; rfl)]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have hext : extendMemory 32 [(20#256, 96#256)] = ⟨9, 96⟩ := by decide
  have hwc : wordCount (96#256).toNat = 3 := by decide
  refine Triple.seq (calldatacopy (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by rw [size_wordBytes, hext, hwc]; dsimp only; omega)) ?_
  rw [size_wordBytes, hext]
  dsimp only
  simp only [BitVec.reduceToNat, show BitVec.toNat (0 : U256) = 0 from rfl,
    show wordCount 96 = 3 by decide]
  have hM := log_memory (c := message.caller.toU256) hsize (e := 96) (by omega)
  have hMs : (memoryWrite (memoryExtend (wordBytes (bitwiseShl 96#256 message.caller.toU256)) 96)
      20 ⟨(bufferRead message.data 0 96).toArray⟩).size = 128 := by
    have hb : (⟨(bufferRead message.data 0 96).toArray⟩ : ByteArray).size = 96 := by
      show (bufferRead _ _ _).toArray.size = 96
      rw [List.size_toArray, bufferRead_length]
    rw [size_memoryWrite (by rw [hb, size_memoryExtend, size_wordBytes]; omega), size_memoryExtend,
      size_wordBytes]
  generalize memoryWrite (memoryExtend (wordBytes (bitwiseShl 96#256 message.caller.toU256)) 96)
    20 ⟨(bufferRead message.data 0 96).toArray⟩ = M at hM hMs ⊢
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have hle : extendMemory M.size [((0 : U256), 116#256)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [hMs]; decide)
  refine Triple.seq (log (n := 0) (words := []) (rest := [t]) rfl
    (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq]) (by decide)
    hstatic (by rw [hle]; simp only [logCost, OPCODE_LOG_BASE, OPCODE_LOG_DATA_PER_BYTE,
      OPCODE_LOG_TOPIC, BitVec.reduceToNat]; omega)) ?_
  rw [hle]
  dsimp only
  rw [memoryExtend_zero]
  have hM' : memoryReadBytes M 0 116 = logData message.caller message.data := hM
  simp only [BitVec.reduceToNat, show BitVec.toNat (0 : U256) = 0 from rfl, List.map_nil, hM',
    logCost, OPCODE_LOG_BASE, OPCODE_LOG_DATA_PER_BYTE, OPCODE_LOG_TOPIC, Nat.add_zero,
    Fin.val_zero, Nat.mul_zero, Nat.reduceMul, Nat.reduceAdd, Nat.sub_sub]
  clear hM hM' hle hMs hext hwc
  evm_step [CODE, CODE_NUMBER_eq]
  refine Triple.seq (binary (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (ofByte_of_decode rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) (by simp only [OPCODE_ADD, VERY_LOW]; omega)) ?_
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc6 (by omega)
    fun S7 hw7 _ g7 ss7 _ hl7 => ?_
  have hw7 := WritesStorage.trans hw6 hw7
  refine Spec.consequence (stop (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq])) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, hss⟩
  refine ⟨by simpa using herr, hout, ?_, ?_⟩
  · rw [hst]
    refine ⟨fun slot => ?_, hw7.2.1, hw7.2.2.1, hw7.2.2.2⟩
    have e1 := funext hw1.1
    have e3 := funext hw3.1
    have e4 := funext hw4.1
    have e5 := funext hw5.1
    have e6 := funext hw6.1
    rw [hw7.1, e6, e5, e4, e3]
    change setSlot (setSlot (setSlot (setSlot (setSlot (storageOf S1 message.currentTarget) _ _)
      _ _) _ _) _ _) _ _ slot = _
    rw [e1, ← ht]
    simp only [afterAdd, requestWords, SLOTS_PER_REQUEST, List.zipIdx_cons, List.zipIdx_nil,
      List.foldl_cons, List.foldl_nil]
    refine congrFun (setSlot_congr (setSlot_congr (setSlot_congr (setSlot_congr (setSlot_congr
      (setSlot_congr rfl rfl ?_) ?_ rfl) ?_ rfl) ?_ rfl) ?_ rfl) rfl ?_) slot <;>
      simp only [add, mul] <;> bv_omega
  · rw [hss, hl7]
    simp only [hl6, hl5, hl4, hl3, hl2, hl1, hl0]

/-- A call from another address with 96 bytes of input adds a request, as EIP-7251 describes.

It holds from Shapella up to BPO5, on a frame that may change the state.

The account of the contract exists.

The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.

The frame has at least 200,000 gas, and 100 more for each of these steps.

When the value pays the fee, the frame adds the request of the caller and the input.

It stores the words of the request at the tail of the queue, and logs the caller and the input.

Otherwise it reverts with no output, and its state reads as the state it starts from. -/
theorem spec_add {m : Nat} (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hsize : message.data.size = 96)
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    (hgas : 200000 + 100 * m ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      if pays (storageOf state message.currentTarget) message.value then
        Added SLOTS_PER_REQUEST message.currentTarget (requestWords message.caller message.data)
          (logData message.caller message.data) state substate evm
      else Answer state none evm := by
  have hz : equal 96#256 (BitVec.ofNat 256 message.data.size) ≠ 0 := by
    rw [hsize]
    decide
  refine user_fee hfork hcaller hfits (by omega) (fun hinh evm h => ?_)
    (fun hinh g ss hg hlogs => ?_)
  · simp only [pays, fee, getFee, hinh, ite_true]
    exact h
  · have hF : fakeExponential MIN_CONSOLIDATION_REQUEST_FEE
        (storageOf state message.currentTarget 0).toNat CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION <
        2 ^ 256 := by
      obtain ⟨h1, h2, -, -⟩ := hfits hinh
      unfold MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION at h1 h2 ⊢
      rw [Fees.BlobBaseFee.fakeExponential_eq_partialSum h1]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h2
    have hpays : pays (storageOf state message.currentTarget) message.value =
        decide (fakeExponential MIN_CONSOLIDATION_REQUEST_FEE
          (storageOf state message.currentTarget 0).toNat
          CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION ≤ message.value.toNat) := by
      simp only [pays, fee, getFee, hinh, ite_false]
    rw [hpays]
    generalize fakeExponential MIN_CONSOLIDATION_REQUEST_FEE
      (storageOf state message.currentTarget 0).toNat
      CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION = F at hF ⊢
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    by_cases hp : F ≤ message.value.toNat
    · have hlt : lessThan message.value (BitVec.ofNat 256 F) = 0 := by
        simp only [lessThan, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF]
        rw [ite_eq_right_iff]
        intro h
        omega
      evm_step [CODE, CODE_NUMBER_eq]
      evm_step [CODE, CODE_NUMBER_eq]
      simp only [hp, decide_true, ite_true]
      refine Spec.consequence (add_tail
        (S := state.recordStorageRead message.currentTarget (U256.toBeBytes 0)) hfork hglam
        hstatic hacc hsize ?_) (fun _ h => h) ?_
      · omega
      · rintro evm ⟨herr, hout, hw, hlog⟩
        exact ⟨herr, hout, hw, by rw [hlog, hlogs]⟩
    · have hlt : lessThan message.value (BitVec.ofNat 256 F) ≠ 0 := by
        simp only [lessThan, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF]
        rw [ite_eq_left (by omega)]
        decide
      evm_step [CODE, CODE_NUMBER_eq]
      evm_step [CODE, CODE_NUMBER_eq]
      simp only [hp, decide_false]
      refine Spec.consequence (revert_410 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
      · simp
      · omega
      · exact h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)

/-! ## The system call -/

/-- A record has 116 bytes. -/
private theorem size_record (read : U256 → U256) (index : U256) :
    (record read index).size = 116 := by
  simp [record, ByteArray.size_append, size_wordBytes]

/-- The four writes of a record of 116 bytes, after the bytes `pre` from offset 0.

The first word holds the address in its first 20 bytes, the next three the words of the record.

Each write starts where the bytes before it end, so it overwrites the tail of the first word.

Memory then holds `pre`, then the address and the three words. -/
theorem holds_record {M M₁ M₂ M₃ M₄ pre : ByteArray} {off e₁ e₂ e₃ e₄ : Nat}
    {v₀ v₁ v₂ v₃ : U256} (hpre : Holds M 0 pre) (hoff : pre.size = off)
    (hM₁ : M₁ = memoryWrite (memoryExtend M e₁) off (wordBytes (bitwiseShl 96#256 v₀)))
    (hM₂ : M₂ = memoryWrite (memoryExtend M₁ e₂) (off + 20) (wordBytes v₁))
    (hM₃ : M₃ = memoryWrite (memoryExtend M₂ e₃) (off + 52) (wordBytes v₂))
    (hM₄ : M₄ = memoryWrite (memoryExtend M₃ e₄) (off + 84) (wordBytes v₃))
    (h₁ : off + 32 ≤ M.size + e₁) (h₂ : off + 52 ≤ M₁.size + e₂)
    (h₃ : off + 84 ≤ M₂.size + e₃) (h₄ : off + 116 ≤ M₃.size + e₄) :
    Holds M₄ 0 (pre ++ ((wordBytes v₀).extract 12 32 ++ wordBytes v₁ ++ wordBytes v₂ ++
      wordBytes v₃)) := by
  have s := size_wordBytes
  have w₁ : off + (wordBytes (bitwiseShl 96#256 v₀)).size ≤ M.size + e₁ := by rw [s]; exact h₁
  have w₂ : off + 20 + (wordBytes v₁).size ≤ M₁.size + e₂ := by rw [s]; omega
  have w₃ : off + 52 + (wordBytes v₂).size ≤ M₂.size + e₃ := by rw [s]; omega
  have w₄ : off + 84 + (wordBytes v₃).size ≤ M₃.size + e₄ := by rw [s]; omega
  have hA₁ : Holds M₁ off ((wordBytes v₀).extract 12 32) := by
    have hw := hM₁ ▸ holds_extend_write w₁
    have hfit : off + ((wordBytes v₀).extract 12 32).size ≤ M₁.size := by
      have := hw.1
      simp only [s, ByteArray.size_extract] at this ⊢
      omega
    refine Holds.of_byteAt hfit fun i hi => ?_
    simp only [ByteArray.size_extract, s] at hi
    rw [hw.byteAt_eq (by rw [s]; omega), byteAt_wordBytes_shl v₀ (by omega), byteAt_extract, s,
      ite_eq_left (by omega)]
  have hsA : ((wordBytes v₀).extract 12 32).size = 20 := by simp [s]
  have hA₂ : Holds M₂ off ((wordBytes v₀).extract 12 32) :=
    hM₂ ▸ Holds.extend_write hA₁ w₂ (by omega)
  have hA₃ : Holds M₃ off ((wordBytes v₀).extract 12 32) :=
    hM₃ ▸ Holds.extend_write hA₂ w₃ (by omega)
  have hA₄ : Holds M₄ off ((wordBytes v₀).extract 12 32) :=
    hM₄ ▸ Holds.extend_write hA₃ w₄ (by omega)
  have hB₂ : Holds M₂ (off + 20) (wordBytes v₁) := hM₂ ▸ holds_extend_write w₂
  have hB₃ : Holds M₃ (off + 20) (wordBytes v₁) :=
    hM₃ ▸ Holds.extend_write hB₂ w₃ (by rw [s]; omega)
  have hB₄ : Holds M₄ (off + 20) (wordBytes v₁) :=
    hM₄ ▸ Holds.extend_write hB₃ w₄ (by rw [s]; omega)
  have hC₃ : Holds M₃ (off + 52) (wordBytes v₂) := hM₃ ▸ holds_extend_write w₃
  have hC₄ : Holds M₄ (off + 52) (wordBytes v₂) :=
    hM₄ ▸ Holds.extend_write hC₃ w₄ (by rw [s]; omega)
  have hD₄ : Holds M₄ (off + 84) (wordBytes v₃) := hM₄ ▸ holds_extend_write w₄
  have hP₁ : Holds M₁ 0 pre := hM₁ ▸ Holds.extend_write hpre w₁ (by omega)
  have hP₂ : Holds M₂ 0 pre := hM₂ ▸ Holds.extend_write hP₁ w₂ (by omega)
  have hP₃ : Holds M₃ 0 pre := hM₃ ▸ Holds.extend_write hP₂ w₃ (by omega)
  have hP₄ : Holds M₄ 0 pre := hM₄ ▸ Holds.extend_write hP₃ w₄ (by omega)
  have hR := ((Holds.append hA₄ (by rw [hsA]; exact hB₄)).append
    (by rw [ByteArray.size_append, hsA, s]; exact hC₄)).append
    (by rw [ByteArray.size_append, ByteArray.size_append, hsA, s, s]; exact hD₄)
  exact Holds.append hP₄ (by rw [Nat.zero_add, hoff]; exact hR)

/-- From the head of the loop at byte 233, one run writes the record of the request `k`.

The memory holds the first `k` records, and grows to hold one more. -/
private theorem deq_body {read : U256 → U256} {S : TransactionState} {ss : Substate}
    {M : ByteArray} {g k c : Nat} {tail : U256} {Q : Evm fork Nat → Prop}
    (hfork : .shapella ≤ fork) (hk : k < c) (hc : c ≤ 2)
    (hread : storageOf S message.currentTarget = read) (hM : Holds M 0 (taken record read k))
    (hMs : M.size = 128 * k) (hg : 9000 ≤ g)
    (next : ∀ M' S' g' ss', Holds M' 0 (taken record read (k + 1)) → M'.size = 128 * (k + 1) →
      WritesStorage message.currentTarget read S S' → g ≤ g' + 9000 →
      Spec fork (At CODE message 233 [BitVec.ofNat 256 (k + 1), BitVec.ofNat 256 c, read 2, tail]
        M' g' S' ss' returnData) Q) :
    Spec fork (At CODE message 233 [BitVec.ofNat 256 k, BitVec.ofNat 256 c, read 2, tail] M g S
      ss returnData) Q := by
  have hne : equal (BitVec.ofNat 256 k) (BitVec.ofNat 256 c) = 0 := by
    rw [equal, ite_eq_right_iff]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have k01 : k = 0 ∨ k = 1 := by omega
  have hoff : (mul 116#256 (BitVec.ofNat 256 k)).toNat = 116 * k := by
    rcases k01 with rfl | rfl <;> decide
  have hsl : add 4#256 (mul 4#256 (add (BitVec.ofNat 256 k) (read 2))) =
      4 + 4 * (read 2 + BitVec.ofNat 256 k) := by
    simp only [add, mul]
    bv_omega
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  rw [hsl]
  generalize hgo : mul 116#256 (BitVec.ofNat 256 k) = off at hoff
  generalize hsl' : 4 + 4 * (read 2 + BitVec.ofNat 256 k) = sl
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g0 ss0 hg0 _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore_then (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    hMs hoff (e := 32) (by rw [← hgo]; rcases k01 with rfl | rfl <;> decide) (by omega)
    (by omega)
    fun M₁ hM₁ hM₁s => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g1 ss1 hg1 _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore_then (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    hM₁s (t := off.toNat + 20) (by rw [← hgo]; rcases k01 with rfl | rfl <;> decide) (e := 32)
    (by rw [← hgo]; rcases k01 with rfl | rfl <;> decide) (by omega) (by omega)
    fun M₂ hM₂ hM₂s => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g2 ss2 hg2 _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore_then (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    hM₂s (t := off.toNat + 52) (by rw [← hgo]; rcases k01 with rfl | rfl <;> decide) (e := 32)
    (by rw [← hgo]; rcases k01 with rfl | rfl <;> decide) (by omega) (by omega)
    fun M₃ hM₃ hM₃s => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g3 ss3 hg3 _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore_then (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    hM₃s (t := off.toNat + 84) (by rw [← hgo]; rcases k01 with rfl | rfl <;> decide) (e := 32)
    (by rw [← hgo]; rcases k01 with rfl | rfl <;> decide) (by omega) (by omega)
    fun M₄ hM₄ hM₄s => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine Triple.seq (jump (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) (by evm_dest [CODE, CODE_NUMBER_eq])) ?_
  simp only [BitVec.reduceToNat]
  have hrec := holds_record hM (size_taken size_record read k) hM₁ (hoff ▸ hM₂) (hoff ▸ hM₃)
    (hoff ▸ hM₄)
    (by rw [hMs]; omega) (by rw [hM₁s]; omega) (by rw [hM₂s]; omega) (by rw [hM₃s]; omega)
  refine Spec.reshape (s' := [BitVec.ofNat 256 (k + 1), BitVec.ofNat 256 c, read 2, tail])
    (by rw [add, BitVec.ofNat_add_ofNat, Nat.add_comm]) rfl rfl
    (next M₄ _ _ _ ?_ (by rw [hM₄s]; omega)
      ⟨fun _ => by simp [hread, storageOf_recordStorageRead], fun _ _ _ => rfl, fun _ => rfl,
        fun _ => rfl⟩ (by omega))
  rw [taken_succ]
  simp only [storageOf_recordStorageRead, hread] at hrec
  have e : record read (read 2 + BitVec.ofNat 256 k) = (wordBytes (read sl)).extract 12 32 ++
      wordBytes (read (add 1#256 sl)) ++ wordBytes (read (add 2#256 sl)) ++
      wordBytes (read (add 3#256 sl)) := by
    simp only [record, hsl', add, BitVec.add_comm sl]
    rfl
  rw [e]
  exact hrec

/-- From the head of the loop at byte 233, the loop writes the records from request `k` up to `c`.

It leaves at byte 297, with the records of the first `c` requests in memory. -/
private theorem deq_loop {read : U256 → U256} {tail : U256} {c : Nat} {Q : Evm fork Nat → Prop}
    (hfork : .shapella ≤ fork) (hc : c ≤ 2) (n : Nat) :
    ∀ {S : TransactionState} {ss : Substate} {M : ByteArray} {g k : Nat}, k + n = c →
    storageOf S message.currentTarget = read → Holds M 0 (taken record read k) →
    M.size = 128 * k → deqGas n ≤ g →
    (∀ M' S' g' ss', Holds M' 0 (taken record read c) → M'.size = 128 * c →
      WritesStorage message.currentTarget read S S' → g ≤ g' + deqGas n →
      Spec fork (At CODE message 297 [BitVec.ofNat 256 c, BitVec.ofNat 256 c, read 2, tail] M' g'
        S' ss' returnData) Q) →
    Spec fork (At CODE message 233 [BitVec.ofNat 256 k, BitVec.ofNat 256 c, read 2, tail] M g S
      ss returnData) Q := by
  induction n with
  | zero =>
    intro S ss M g k hk hread hM hMs hg next
    rw [Nat.add_zero] at hk
    subst hk
    simp only [deqGas] at hg next
    have heq : equal (BitVec.ofNat 256 k) (BitVec.ofNat 256 k) ≠ 0 := by simp [equal]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    exact next M S _ ss hM hMs (hread ▸ WritesStorage.refl _ _) (by omega)
  | succ n ih =>
    intro S ss M g k hk hread hM hMs hg next
    simp only [deqGas] at hg next
    refine deq_body hfork (by omega) hc hread hM hMs (by omega) fun M₁ S₁ g₁ ss₁ hM₁ hM₁s hw₁ hg₁ =>
      ih (by omega) (funext hw₁.1) hM₁ hM₁s (by omega) fun M' S' g' ss' hM' hM's hw' hg' =>
        next M' S' g' ss' hM' hM's (WritesStorage.trans hw₁ hw')
          (Nat.le_trans hg₁ (by rw [← Nat.add_assoc]; exact Nat.add_le_add_right hg' _))

/-- From byte 398, the code writes the excess `v` and resets the count of the block.

It then returns the records, `116` bytes for each request taken. -/
private theorem deq_end {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {v x : U256} (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hM : (mul 116#256 x).toNat ≤ M.size) (hg : 50000 ≤ g) :
    Spec fork (At CODE message 398 [v, x] M g S ss returnData)
      (Returned message.currentTarget M (mul 116#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0) S) := by
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc (by omega)
    fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc₁ (by omega)
    fun S₂ hw₂ _ g₂ ss₂ hg₂ _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have hle : extendMemory M.size [((0 : U256), mul 116#256 x)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by simpa using hM)
  refine Spec.consequence («return» (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by rw [hle]; exact Nat.zero_le _)) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, -⟩
  refine ⟨by simpa using herr, ?_, ?_⟩
  · rw [hout, hle]
    dsimp only
    rw [memoryExtend_zero]
    rfl
  · rw [hst]
    have hw := WritesStorage.trans hw₁ hw₂
    rw [show storageOf S₁ message.currentTarget = _ from funext hw₁.1] at hw
    exact hw

/-- From byte 371, the code computes the new excess from the previous excess `p` and the count.

The previous excess plus the count is below `2^256`. -/
private theorem deq_count {S : TransactionState} {ss : Substate} {M : ByteArray} {g p : Nat}
    {x : U256} (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hp : p + (storageOf S message.currentTarget 1#256).toNat < 2 ^ 256)
    (hM : (mul 116#256 x).toNat ≤ M.size) (hg : 60000 ≤ g) :
    Spec fork (At CODE message 371 [BitVec.ofNat 256 p, x] M g S ss returnData)
      (Returned message.currentTarget M (mul 116#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (if p + (storageOf S message.currentTarget 1#256).toNat > 1 then
            p + (storageOf S message.currentTarget 1#256).toNat - 1 else 0))) 1 0) S) := by
  generalize hn : (storageOf S message.currentTarget 1#256).toNat = n at hp
  have hs : add (storageOf S message.currentTarget 1#256) (BitVec.ofNat 256 p) =
      BitVec.ofNat 256 (p + n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [add, BitVec.toNat_add, BitVec.toNat_ofNat, hn]
    have hp' : p < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.le_add_right p n) hp
    rw [Nat.mod_eq_of_lt hp', Nat.add_comm, Nat.mod_eq_of_lt hp]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g₁ ss₁ hg₁ _ => ?_
  have hacc₁ : ((S.recordStorageRead message.currentTarget (U256.toBeBytes 1#256)
      ).getAccountOptional message.currentTarget).isSome = true := hacc
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  rw [hs]
  have hsub : 1 ≤ p + n → sub (BitVec.ofNat 256 (p + n)) 1#256 =
      BitVec.ofNat 256 (p + n - 1) := by
    intro h1
    apply BitVec.eq_of_toNat_eq
    simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
    omega
  have post : ∀ v, ∀ evm : Evm fork Nat, Returned message.currentTarget M (mul 116#256 x).toNat
      (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0)
      (S.recordStorageRead message.currentTarget (U256.toBeBytes 1#256)) evm →
      Returned message.currentTarget M (mul 116#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0) S evm :=
    fun _ _ ⟨h1, h2, h3⟩ =>
      ⟨h1, h2, WritesStorage.trans (WritesStorage.recordStorageRead _ _ _ _) h3⟩
  by_cases hgt : p + n > 1
  · have hz : greaterThan (BitVec.ofNat 256 (p + n)) 1#256 ≠ 0 := by
      simp [greaterThan, Nat.mod_eq_of_lt hp, hgt]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    rw [hs]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    rw [hsub (by omega)]
    simp only [hgt, ite_true]
    exact Spec.consequence (deq_end hfork hglam hstatic hacc₁ hM (by omega)) (fun _ h => h)
      (post _)
  · have hz : greaterThan (BitVec.ofNat 256 (p + n)) 1#256 = 0 := by
      simp [greaterThan, Nat.mod_eq_of_lt hp, hgt]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    simp only [hgt, ite_false]
    exact Spec.consequence (deq_end hfork hglam hstatic hacc₁ hM (by omega)) (fun _ h => h)
      (post _)

/-- From byte 326, the code updates the excess for a target of 1 per block, and resets the count.

It then returns the records, `116` bytes for each request taken. -/
private theorem deq_excess {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {x : U256} (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hb : previousExcess (storageOf S message.currentTarget 0) +
      (storageOf S message.currentTarget 1#256).toNat < 2 ^ 256)
    (hM : (mul 116#256 x).toNat ≤ M.size) (hg : 70000 ≤ g) :
    Spec fork (At CODE message 326 [x] M g S ss returnData)
      (Returned message.currentTarget M (mul 116#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (newExcess 1 (storageOf S message.currentTarget 0)
            (storageOf S message.currentTarget 1)))) 1 0) S) := by
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g₁ ss₁ hg₁ _ => ?_
  have hacc₁ : ((S.recordStorageRead message.currentTarget (U256.toBeBytes 0)).getAccountOptional
      message.currentTarget).isSome = true := hacc
  have post : ∀ evm : Evm fork Nat, Returned message.currentTarget M (mul 116#256 x).toNat
      (setSlot (setSlot (storageOf S message.currentTarget) 0
        (BitVec.ofNat 256 (newExcess 1 (storageOf S message.currentTarget 0)
          (storageOf S message.currentTarget 1)))) 1 0)
      (S.recordStorageRead message.currentTarget (U256.toBeBytes 0)) evm →
      Returned message.currentTarget M (mul 116#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (newExcess 1 (storageOf S message.currentTarget 0)
            (storageOf S message.currentTarget 1)))) 1 0) S evm :=
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, WritesStorage.trans (WritesStorage.recordStorageRead _ _ _ _) h3⟩
  have hw : BitVec.ofNat 256 (2 ^ 256 - 1) = EXCESS_INHIBITOR := rfl
  by_cases hinh : storageOf S message.currentTarget 0 = EXCESS_INHIBITOR
  · have hz : isZero (equal (BitVec.ofNat 256 (2 ^ 256 - 1))
        (storageOf S message.currentTarget 0)) = 0 := by
      rw [hinh, ← hw]
      decide
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    have hp : previousExcess (storageOf S message.currentTarget 0) = 0 := by
      unfold previousExcess
      rw [ite_eq_left hinh]
    rw [hp] at hb
    refine Spec.consequence (deq_count (p := 0) hfork hglam hstatic hacc₁ hb hM (by omega))
      (fun _ h => h) fun evm h => post evm ?_
    unfold newExcess
    rw [hp]
    exact h
  · have hz : isZero (equal (BitVec.ofNat 256 (2 ^ 256 - 1))
        (storageOf S message.currentTarget 0)) ≠ 0 := by
      have hne : BitVec.ofNat 256 (2 ^ 256 - 1) ≠ storageOf S message.currentTarget 0 :=
        fun e => hinh (e.symm.trans hw)
      rw [equal, ite_eq_right hne, isZero, ite_eq_left rfl]
      decide
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    have hp : previousExcess (storageOf S message.currentTarget 0) =
        (storageOf S message.currentTarget 0).toNat := by
      unfold previousExcess
      rw [ite_eq_right hinh]
    rw [hp] at hb
    refine Spec.reshape (s' := [BitVec.ofNat 256 (storageOf S message.currentTarget 0).toNat, x])
      (by simp) rfl rfl ?_
    refine Spec.consequence (deq_count hfork hglam hstatic hacc₁ hb hM (by omega))
      (fun _ h => h) fun evm h => post evm ?_
    unfold newExcess
    rw [hp]
    exact h

/-- From byte 297, the code moves the head of the queue, or empties it, then updates the excess.

It returns the records of the requests it took, which memory holds. -/
private theorem deq_head {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {r : U256 → U256} (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hr : storageOf S message.currentTarget = r) (hb : Bounded r)
    (hMs : M.size = 128 * numDequeued 2 r) (hg : 120000 ≤ g) :
    Spec fork (At CODE message 297 [BitVec.ofNat 256 (numDequeued 2 r),
        BitVec.ofNat 256 (numDequeued 2 r), r 2, r 3] M g S ss returnData)
      (Returned message.currentTarget M (116 * numDequeued 2 r) (afterDequeue 2 1 r) S) := by
  obtain ⟨hht, hex⟩ := hb
  have hc2 : numDequeued 2 r ≤ 2 := Nat.min_le_right _ _
  have hle : (r 2).toNat + numDequeued 2 r ≤ (r 3).toNat := by
    unfold numDequeued
    have h : Nat.min ((r 3).toNat - (r 2).toNat) 2 ≤ (r 3).toNat - (r 2).toNat :=
      Nat.min_le_left _ _
    omega
  have ht := (r 3).isLt
  generalize hc : numDequeued 2 r = c at hc2 hle hMs ⊢
  have hnh : add (r 2) (BitVec.ofNat 256 c) = BitVec.ofNat 256 ((r 2).toNat + c) := by
    apply BitVec.eq_of_toNat_eq
    simp only [add, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 256), Nat.mod_eq_of_lt (by omega)]
  have hmul : (mul 116#256 (BitVec.ofNat 256 c)).toNat = 116 * c := by
    simp only [mul, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 256)]
    omega
  have hM : (mul 116#256 (BitVec.ofNat 256 c)).toNat ≤ M.size := by rw [hmul, hMs]; omega
  have hr0 : ∀ F : U256 → U256, F 0 = r 0 → F 1#256 = r 1 →
      previousExcess (F 0) + (F 1#256).toNat < 2 ^ 256 := fun F h0 h1 => by
    rw [h0, h1]; exact hex
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  rw [hnh]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have heqv : r 3 = BitVec.ofNat 256 ((r 2).toNat + c) ↔ (r 2).toNat + c = (r 3).toNat := by
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      omega
    · intro e
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  by_cases hnt : (r 2).toNat + c = (r 3).toNat
  · have hz : equal (r 3) (BitVec.ofNat 256 ((r 2).toNat + c)) ≠ 0 := by
      rw [equal, ite_eq_left (heqv.mpr hnt)]
      decide
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
      (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc (by omega)
      fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine sstore_then (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER_eq])
      (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc₁ (by omega)
      fun S₂ hw₂ hacc₂ g₂ ss₂ hg₂ _ => ?_
    have eF : storageOf S₂ message.currentTarget = setSlot (setSlot r 2 0) 3 0 := by
      rw [funext hw₂.1, funext hw₁.1, hr]
      rfl
    refine Spec.consequence (deq_excess hfork hglam hstatic hacc₂
      (hr0 _ (by rw [eF]; simp [setSlot]) (by rw [eF]; simp [setSlot])) hM (by omega))
      (fun _ h => h) fun evm h => ?_
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [h2, hmul], ?_⟩
    have hw := WritesStorage.trans (WritesStorage.trans hw₁ hw₂) h3
    rw [eF, deq_store 2 1 r (setSlot (setSlot r 2 0) 3 0) (by rw [hc, ite_eq_left hnt])] at hw
    exact hw
  · have hz : equal (r 3) (BitVec.ofNat 256 ((r 2).toNat + c)) = 0 := by
      simp only [equal]
      rw [ite_eq_right_iff]
      exact fun e => absurd (heqv.mp e) hnt
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine sstore_then (Nat.le_trans (by decide) hfork) hglam
      (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc
      (by omega) fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    have eF : storageOf S₁ message.currentTarget =
        setSlot r 2 (BitVec.ofNat 256 ((r 2).toNat + c)) := by
      rw [funext hw₁.1, hr]
      rfl
    refine Spec.consequence (deq_excess hfork hglam hstatic hacc₁
      (hr0 _ (by rw [eF]; simp [setSlot]) (by rw [eF]; simp [setSlot])) hM (by omega))
      (fun _ h => h) fun evm h => ?_
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [h2, hmul], ?_⟩
    have hw := WritesStorage.trans hw₁ h3
    rw [eF, deq_store 2 1 r (setSlot r 2 (BitVec.ofNat 256 ((r 2).toNat + c)))
      (by rw [hc, ite_eq_right hnt])] at hw
    exact hw

/-- At most 2 runs of the loop of the system call take at most 18,030 gas. -/
private theorem deqGas_le {n : Nat} (hn : n ≤ 2) : deqGas n ≤ 18030 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with h | h | h <;> subst h <;> decide

/-- From the head of the loop at byte 233, with memory empty, the code takes the requests.

It returns their records, and holds the storage after the requests are taken. -/
private theorem deq_rest {S : TransactionState} {ss : Substate} {g : Nat} {r : U256 → U256}
    (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hr : storageOf S message.currentTarget = r) (hb : Bounded r) (hg : 140000 ≤ g) :
    Spec fork (At CODE message 233 [BitVec.ofNat 256 0, BitVec.ofNat 256 (numDequeued 2 r), r 2,
        r 3] .empty g S ss returnData) fun evm =>
      evm.error = none ∧ evm.output = taken record r (numDequeued 2 r) ∧
      WritesStorage message.currentTarget (afterDequeue 2 1 r) S evm.state := by
  have hc2 : numDequeued 2 r ≤ 2 := Nat.min_le_right _ _
  have hdg := deqGas_le hc2
  refine deq_loop hfork hc2 (numDequeued 2 r) (by omega) hr (holds_empty (Nat.le_refl _)) rfl
    (by omega) fun M' S' g' ss' hM' hM's hw' hg' => ?_
  have hacc' : (S'.getAccountOptional message.currentTarget).isSome = true := by
    rw [hw'.2.2.1]; exact hacc
  refine Spec.consequence (deq_head hfork hglam hstatic hacc' (funext hw'.1) hb hM's
    (by omega)) (fun _ h => h) fun evm ⟨h1, h2, h3⟩ => ⟨h1, ?_, WritesStorage.trans hw' h3⟩
  rw [h2]
  have := hM'.2
  rw [size_taken size_record] at this
  exact this

/-- A call from the system address takes requests from the queue, as EIP-7251 describes.

It holds from Shapella up to BPO5, on a frame that may change the state.

The account of the contract exists, and the frame has at least 200,000 gas.

The counters of the storage meet the bounds under which the code computes as the EIP.

The frame stops with no error, and returns the records of at most 2 requests from the head.

The state holds the storage after the requests are taken, the excess updated and the count reset.

It keeps the storage of every other account, the accounts and the codes. -/
theorem spec_dequeue (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hcaller : message.caller = SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hbounded : Bounded (storageOf state message.currentTarget)) (hgas : 200000 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      evm.error = none ∧
      evm.output = dequeued MAX_CONSOLIDATION_REQUESTS_PER_BLOCK record
        (storageOf state message.currentTarget) ∧
      WritesStorage message.currentTarget
        (afterDequeue MAX_CONSOLIDATION_REQUESTS_PER_BLOCK TARGET_CONSOLIDATION_REQUESTS_PER_BLOCK
          (storageOf state message.currentTarget))
        state evm.state := by
  generalize hr : storageOf state message.currentTarget = r
  have hb := hbounded
  rw [hr] at hb
  obtain ⟨hht, hex⟩ := hb
  have ht := (r 3).isLt
  evm_step [CODE, CODE_NUMBER_eq]
  rw [hcaller, toU256_SYSTEM_ADDRESS]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g₁ ss₁ hg₁ _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g₂ ss₂ hg₂ _ => ?_
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
  have post : ∀ evm : Evm fork Nat,
      (evm.error = none ∧ evm.output = taken record r (numDequeued 2 r) ∧
      WritesStorage message.currentTarget (afterDequeue 2 1 r)
        ((state.recordStorageRead message.currentTarget (U256.toBeBytes 3#256)
          ).recordStorageRead message.currentTarget (U256.toBeBytes 2#256)) evm.state) →
      evm.error = none ∧ evm.output = dequeued MAX_CONSOLIDATION_REQUESTS_PER_BLOCK record r ∧
        WritesStorage message.currentTarget
          (afterDequeue MAX_CONSOLIDATION_REQUESTS_PER_BLOCK
            TARGET_CONSOLIDATION_REQUESTS_PER_BLOCK r) state evm.state :=
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, WritesStorage.trans (WritesStorage.trans
      (WritesStorage.recordStorageRead message.currentTarget state message.currentTarget
        (U256.toBeBytes 3#256))
      (WritesStorage.recordStorageRead message.currentTarget _ message.currentTarget
        (U256.toBeBytes 2#256))) h3⟩
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  rw [hsubv]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  by_cases hd : (r 3).toNat - (r 2).toNat < 2
  · have hz : greaterThan 2#256 (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)) ≠ 0 := by
      have hlt : (2#256).toNat > (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)).toNat := by
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : (r 3).toNat - (r 2).toNat < 2 ^ 256)]
        omega
      rw [greaterThan, ite_eq_left hlt]
      decide
    have hn : numDequeued 2 r = (r 3).toNat - (r 2).toNat := Nat.min_eq_left (by omega)
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    rw [← hn]
    refine Spec.consequence (deq_rest hfork hglam hstatic hacc' hS ⟨hht, hex⟩ ?_)
      (fun _ h => h) post
    omega
  · have hz : greaterThan 2#256 (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)) = 0 := by
      rw [greaterThan, ite_eq_right_iff]
      intro h
      have h' : 2 > (r 3).toNat - (r 2).toNat := by
        simp only [BitVec.toNat_ofNat] at h
        rw [Nat.mod_eq_of_lt (by omega : (r 3).toNat - (r 2).toNat < 2 ^ 256)] at h
        omega
      exact absurd h' hd
    have hn : numDequeued 2 r = 2 := Nat.min_eq_right (by omega)
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine Spec.reshape (s' := [BitVec.ofNat 256 0, BitVec.ofNat 256 (numDequeued 2 r), r 2, r 3])
      (by rw [hn]; rfl) rfl rfl ?_
    refine Spec.consequence (deq_rest hfork hglam hstatic hacc' hS ⟨hht, hex⟩ ?_)
      (fun _ h => h) post
    omega

/-- The consolidation request address is not a precompile. -/
theorem addedAt_CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS :
    Precompiles.addedAt CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS.toU256.toNat = none := by
  rw [CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS, EthLib.Base.toNat_toU256_toAddressMasked]
  rfl

/-- The code is not a delegation indicator: it has 414 bytes, not 23. -/
theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  simp [delegatedAddress, isValidDelegation, CODE, NatCode.size_ofNat, DELEGATION_SIZE]

/-- From Pectra up to BPO5, the system call of a block to the contract takes its requests.

The account at the consolidation request address must hold the code of EIP-7251.

The counters of its storage meet the bounds under which the code computes as the EIP.

The call succeeds, whatever its data, and returns the records of at most 2 requests.

The storage of the contract is then the storage after the requests are taken.

The call keeps the storage of every other account, the accounts and the codes. -/
theorem systemCall_dequeue {env : BlockEnvironment fork} {block : State.BlockState}
    {data : ByteArray} (hfork : .pectra ≤ fork) (hglam : fork < .glamsterdam)
    (hcode : codeAt block CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS = .ok CODE)
    (hbounded : Bounded (storageOf (.ofBlock block) CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS)) :
    ∃ out, systemCall env block CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS data = .ok out ∧
      out.error = none ∧
      out.output = dequeued MAX_CONSOLIDATION_REQUESTS_PER_BLOCK record
        (storageOf (.ofBlock block) CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS) ∧
      WritesStorage CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS
        (afterDequeue MAX_CONSOLIDATION_REQUESTS_PER_BLOCK TARGET_CONSOLIDATION_REQUESTS_PER_BLOCK
          (storageOf (.ofBlock block) CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS))
        (.ofBlock block) out.state :=
  systemCall_of_writesStorage (P := Bounded) _ _ (Nat.le_trans (by decide) hfork) hglam hcode
    (by simp [CODE, NatCode.size_ofNat]) addedAt_CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS
    delegatedAddress_CODE hbounded
    fun message _ _ hcaller htarget hstatic _ _ hgas hacc hread => by
      rw [← htarget]
      exact spec_dequeue (Nat.le_trans (by decide) hfork) hglam hcaller hstatic (htarget ▸ hacc)
        (htarget ▸ hread) (by rw [hgas]; decide)

/-- Empty consolidation code after the withdrawal request call rejects the request phase.

The preceding call must succeed; an earlier failure takes precedence.

This is the empty-code rejection required by [EIP-7251][eip7251].

[eip7251]: https://eips.ethereum.org/EIPS/eip-7251#system-call -/
theorem readRequests_of_empty {env : BlockEnvironment fork} {body : BodyState}
    {mid : BodyState × List ByteArray} (hfork : .pectra ≤ fork)
    (hwithdrawal : readRequest env (body, [])
      (WITHDRAWAL_REQUEST_TYPE, WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS) = .ok mid)
    (hcode : codeAt mid.1.block CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS = .ok .empty) :
    readRequests env body =
      .error (.systemContractEmpty CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS) := by
  have hread := readRequest_of_empty (env := env)
    (contract := (CONSOLIDATION_REQUEST_TYPE, CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS)) hcode
  rw [readRequests_of_pectra hfork]
  unfold requestContracts
  split <;> simp [REQUEST_CONTRACTS, List.foldlM_cons, hwithdrawal, hread, bind, Except.bind]

/-- No block request result succeeds when consolidation code is empty after withdrawals.

[EIP-7251][eip7251] requires rejection, not an empty list of consolidation requests.

[eip7251]: https://eips.ethereum.org/EIPS/eip-7251#system-call -/
theorem blockRequests_ne_ok_of_empty {env : BlockEnvironment fork} {body : BodyState}
    {mid : BodyState × List ByteArray} {depositContract : Address} {logs : List Log}
    {result : BodyState × List ByteArray} (hfork : .pectra ≤ fork)
    (hwithdrawal : readRequest env (body, [])
      (WITHDRAWAL_REQUEST_TYPE, WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS) = .ok mid)
    (hcode : codeAt mid.1.block CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS = .ok .empty) :
    blockRequests depositContract env body logs ≠ .ok result :=
  blockRequests_ne_ok_of_readRequests_error hfork (readRequests_of_empty hfork hwithdrawal hcode)

end EthLib.Execution.Blocks.ConsolidationRequests
