module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Meter
public import EthLib.Execution.Proofs.Blocks.SystemCall.WithdrawalRequests.Record

/-!
# Proofs: the withdrawal request contract of EIP-7002 does what its EIP describes

The contract keeps a queue of withdrawal requests, and a fee that rises with its use.

Its code is the 504 bytes of [EIP-7002][eip-7002-deployment], which its deployment installs.

A call from any other address with no input and no value gets the fee.

A call with 56 bytes of input adds a request, when its value pays the fee.

The input is the public key of the validator, then the amount as 8 bytes, big-endian.

The request holds the caller and the input, in three slots, and the call logs them.

A call from the system address takes at most 16 requests from the head of the queue.

It returns their records of 76 bytes each, and updates the excess for a target of 2 per block.

A record ends with the amount as 8 bytes, little-endian, as the EIP encodes it.

The code keeps the amount big-endian in storage, and reverses its bytes when it reads a request.

The pseudocode of the EIP stores it little-endian, and reads it as it is.

So the third slot of a request differs from the pseudocode, but the records are the same.

Each operation of [the EIP][eip-7002-contract] is a function here.

A theorem runs the code and shows that it computes that function.

The fee and addition specifications use a one-counter frame from Shapella up to BPO5.

The dequeue specification uses a conservative one-counter budget from Shapella.

From Pectra, a system call to the contract succeeds with the gas meter of its fork.

It returns the requests and leaves the storage that the EIP describes.

[eip-7002-deployment]: https://eips.ethereum.org/EIPS/eip-7002#deployment
[eip-7002-contract]: https://eips.ethereum.org/EIPS/eip-7002#withdrawal-request-contract
-/

@[expose] public section

namespace EthLib.Execution.Blocks.WithdrawalRequests

open EthLib.Base (Fork U256 Address)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract
open EthLib.Execution.Blocks.RequestQueue
open GasCosts
open EthLib.Execution.Fees.BlobBaseFee (fakeExponential)

/-! ## The contract -/

/-- The most requests that a block takes from the queue, 16, by EIP-7002. -/
def MAX_WITHDRAWAL_REQUESTS_PER_BLOCK : Nat := 16

/-- The requests per block that keep the fee where it is, 2, by EIP-7002. -/
def TARGET_WITHDRAWAL_REQUESTS_PER_BLOCK : Nat := 2

/-- The fee at an excess of 0, 1 wei, by EIP-7002. -/
def MIN_WITHDRAWAL_REQUEST_FEE : Nat := 1

/-- The divisor of the excess in the exponent of the fee, 17, by EIP-7002. -/
def WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION : Nat := 17

/-- The slots of each request in the queue: the caller, then the 56 bytes of input in two. -/
def SLOTS_PER_REQUEST : Nat := 3

/-- The code of the contract as one number: its 504 bytes, the first byte highest.

The input of the deployment transaction of EIP-7002 is 45 bytes of constructor, then these bytes.

Here they come in twelve runs of 40 bytes, then a run of 24 bytes. -/
def CODE_NUMBER : Nat :=
  0x3373fffffffffffffffffffffffffffffffffffffffe1460cb5760115f54807fffffffffffffffff * 256 ^ 464 +
  0xffffffffffffffffffffffffffffffffffffffffffffffff146101f457600182026001905f5b5f82 * 256 ^ 424 +
  0x111560685781019083028483029004916001019190604d565b909390049250505036603814608857 * 256 ^ 384 +
  0x366101f457346101f4575f5260205ff35b34106101f4576001546001016001556003548060030260 * 256 ^ 344 +
  0x04013381556001015f35815560010160203590553360601b5f5260385f601437604c5fa060010160 * 256 ^ 304 +
  0x0355005b6003546002548082038060101160df575060105b5f5b8181146101835782810160030260 * 256 ^ 264 +
  0x040181604c02815460601b8152601401816001015481526020019060020154807fffffffffffffff * 256 ^ 224 +
  0xffffffffffffffffff00000000000000000000000000000000168252906010019060401c90816038 * 256 ^ 184 +
  0x1c81600701538160301c81600601538160281c81600501538160201c81600401538160181c816003 * 256 ^ 144 +
  0x01538160101c81600201538160081c81600101535360010160e1565b910180921461019557906002 * 256 ^ 104 +
  0x556101a0565b90505f6002555f6003555b5f54807fffffffffffffffffffffffffffffffffffffff * 256 ^ 64 +
  0xffffffffffffffffffffffffff14156101cd57505f5b6001546002828201116101e25750505f6101 * 256 ^ 24 +
  0xe8565b01600290035b5f555f600155604c025ff35b5f5ffd

/-- The code of the withdrawal request contract, 504 bytes, by EIP-7002. -/
def CODE : ByteArray := NatCode.ofNat CODE_NUMBER 504

/-- The opcode scan skips PUSH data and finds only instructions supported by both meters. -/
theorem supportedCode_CODE : SupportedCode CODE = true := by
  decide +kernel

/-! ## The operations -/

/-- The fee to add a request with the storage `read`, or none while the inhibitor holds. -/
def fee (read : U256 → U256) : Option Nat :=
  getFee MIN_WITHDRAWAL_REQUEST_FEE WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION (read 0)

/-- What a call with the input `input` and the value `value` gets, when it adds no request.

With no input and no value, it gets the fee as a word, or reverts while the inhibitor holds.

Any input of a size other than 0 or 56 bytes reverts, and so does a value with no input.

The EIP gives only the fee for no input; these reverts come from its code. -/
def getFeeResult (read : U256 → U256) (input : ByteArray) (value : U256) : Option U256 :=
  if input.size = 0 ∧ value = 0 then (fee read).map (BitVec.ofNat 256) else none

/-- A call with the value `value` pays the fee: the fee is defined and at most the value. -/
def pays (read : U256 → U256) (value : U256) : Bool :=
  match fee read with
  | some f => decide (f ≤ value.toNat)
  | none => false

/-- The three words of a request from `caller` with the input `input`, as the queue holds them.

They are the caller, then the two words of the input, read big-endian with zeros past its end.

The last word holds the end of the public key, the amount big-endian, then 8 zero bytes. -/
def requestWords (caller : Address) (input : ByteArray) : List U256 :=
  [caller.toU256, loadWord input 0 32, loadWord input 32 32]

/-- The data of the log of a request: the 20 bytes of the caller, then the input. -/
def logData (caller : Address) (input : ByteArray) : ByteArray :=
  (wordBytes caller.toU256).extract 12 32 ++ input

/-- The record of 76 bytes of the request at the index `index`, counted from the start of the queue.

It is the source address, the public key of the validator, then the amount, little-endian.

The address is the last 20 bytes of the first slot, since the code stores the caller as a word.

The pseudocode of the EIP slices bytes 0 to 20 instead.

The key is the 32 bytes of the second slot, then the first 16 bytes of the third.

The amount is the next 8 bytes of the third slot, in reverse order. -/
def record (read : U256 → U256) (index : U256) : ByteArray :=
  let slot := 4 + 3 * index
  (wordBytes (read slot)).extract 12 32 ++ wordBytes (read (slot + 1)) ++
    (wordBytes (read (slot + 2))).extract 0 16 ++
    ⟨((wordBytes (read (slot + 2))).extract 16 24).data.reverse⟩

/-! ## The loop of the fee -/

/-- The number of the code in sixteen runs: 24 bytes, then fifteen runs of 32 bytes.

The runs nest in a balanced tree, so that each power of 256 stays below `256^256`. -/
theorem CODE_NUMBER_eq : CODE_NUMBER =
    (((0x3373fffffffffffffffffffffffffffffffffffffffe1460 * 256 ^ 32 +
    0xcb5760115f54807fffffffffffffffffffffffffffffffffffffffffffffffff) * 256 ^ 64 +
    (0xffffffffffffffff146101f457600182026001905f5b5f821115606857810190 * 256 ^ 32 +
    0x83028483029004916001019190604d565b909390049250505036603814608857)) * 256 ^ 160 +
    ((0x366101f457346101f4575f5260205ff35b34106101f457600154600101600155 * 256 ^ 32 +
    0x600354806003026004013381556001015f35815560010160203590553360601b) * 256 ^ 96 +
    (0x5f5260385f601437604c5fa0600101600355005b600354600254808203806010 * 256 ^ 64 +
    (0x1160df575060105b5f5b8181146101835782810160030260040181604c028154 * 256 ^ 32 +
    0x60601b8152601401816001015481526020019060020154807fffffffffffffff)))) * 256 ^ 224 +
    ((0xffffffffffffffffff0000000000000000000000000000000016825290601001 * 256 ^ 64 +
    (0x9060401c908160381c81600701538160301c81600601538160281c8160050153 * 256 ^ 32 +
    0x8160201c81600401538160181c81600301538160101c81600201538160081c81)) * 256 ^ 128 +
    ((0x600101535360010160e1565b910180921461019557906002556101a0565b9050 * 256 ^ 32 +
    0x5f6002555f6003555b5f54807fffffffffffffffffffffffffffffffffffffff) * 256 ^ 64 +
    (0xffffffffffffffffffffffffff14156101cd57505f5b60015460028282011161 * 256 ^ 32 +
    0x01e25750505f6101e8565b01600290035b5f555f600155604c025ff35b5f5ffd))) := by
  decide +kernel

/-- The code runs the loop of the fee from byte 69, as the consolidation request contract does. -/
theorem feeLoopCode_CODE : FeeLoopCode CODE :=
  FeeLoopCode.of_ofNat (by decide) (by rw [CODE_NUMBER_eq, FEE_LOOP_NUMBER]; decide +kernel)
    (by evm_dest [CODE_NUMBER_eq]) (by evm_dest [CODE_NUMBER_eq])

/-! The proofs read the code through the equation above, never by unfolding it.

The number of the code is a sum of terms with powers of 256 up to `256^464`.

Without the attribute, each step reduces these powers, and the step exceeds the recursion depth.

The attribute keeps the code opaque, so the steps read it only through the equation. -/
attribute [local irreducible] CODE

/-! ## A call that adds no request -/

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- JUMPDEST, PUSH0, PUSH0 and REVERT, at byte 500, revert with no output. -/
private theorem revert_500 {stack : List U256} (hfork : .shapella ≤ fork)
    (hstack : stack.length ≤ 6) (hgas : 10 ≤ gas) :
    Spec fork (At CODE message 500 stack .empty gas state substate returnData)
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
      FeeFits MIN_WITHDRAWAL_REQUEST_FEE WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    (hgas : 2216 + 87 * m ≤ gas)
    (hrev : storageOf state message.currentTarget 0 = EXCESS_INHIBITOR →
      ∀ evm, Answer state none evm → Q evm)
    (hcont : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR → ∀ g ss,
      gas - (2216 + 87 * m) ≤ g → ss.logs = substate.logs →
      Spec fork (At CODE message 113
        [BitVec.ofNat 256 (fakeExponential MIN_WITHDRAWAL_REQUEST_FEE
          (storageOf state message.currentTarget 0).toNat
          WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION)]
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
    refine Spec.consequence (revert_500 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
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

/-- A call from another address, whose input is not 56 bytes, gets the fee or reverts.

It holds from Shapella up to BPO5, with the one-counter meter.

The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.

The frame has at least 100,000 gas, and 100 more for each of these steps.

It assumes fewer than `2^256` bytes of input, which the size word of the EVM can hold.

The frame returns the fee as a word, or reverts with no output, as the code of the EIP does.

Its state reads as the state it starts from. -/
theorem spec_getFee {m : Nat} (hfork : .shapella ≤ fork) (_hglam : fork < .glamsterdam)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hsize : message.data.size ≠ 56)
    (hbound : message.data.size < 2 ^ 256)
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_WITHDRAWAL_REQUEST_FEE WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    (hgas : 100000 + 100 * m ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData)
      (Answer state (getFeeResult (storageOf state message.currentTarget) message.data
        message.value)) := by
  have hs : equal 56#256 (BitVec.ofNat 256 message.data.size) = 0 := by
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
        refine Spec.consequence (revert_500 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
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
      refine Spec.consequence (revert_500 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
      · simp
      · omega
      · simp only [getFeeResult, h0, false_and, ite_false]
        exact hread _ _ h

/-! ## A call that adds a request -/

/-- From byte 143, the code adds the request of the caller and the input, and logs it. -/
private theorem add_tail {S : TransactionState} {ss : Substate} {g : Nat}
    (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam) (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hsize : message.data.size = 56) (hgas : 150000 ≤ g) :
    Spec fork (At CODE message 143 [] .empty g S ss returnData)
      (Added SLOTS_PER_REQUEST message.currentTarget (requestWords message.caller message.data)
        (logData message.caller message.data) S ss) := by
  have hscale := storageGasScale_of_lt hglam
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g0 ss0 hg0 hl0 => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
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
  refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc1 (by omega)
    fun S3 hw3 hacc3 g3 ss3 hg3 hl3 => ?_
  have hw3 := WritesStorage.trans hw2 hw3
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc3 (by omega)
    fun S4 hw4 hacc4 g4 ss4 hg4 hl4 => ?_
  have hw4 := WritesStorage.trans hw3 hw4
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc4 (by omega)
    fun S5 hw5 hacc5 g5 ss5 hg5 hl5 => ?_
  have hw5 := WritesStorage.trans hw4 hw5
  have hg5' : 35000 ≤ g5 := by omega
  clear hg0 hg1 hg2 hg3 hg4 hg5 hgas
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
  have hext : extendMemory 32 [(20#256, 56#256)] = ⟨6, 64⟩ := by decide
  have hwc : wordCount (56#256).toNat = 2 := by decide
  refine Triple.seq (calldatacopy (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by rw [size_wordBytes, hext, hwc]; dsimp only; omega)) ?_
  rw [size_wordBytes, hext]
  dsimp only
  simp only [BitVec.reduceToNat, show BitVec.toNat (0 : U256) = 0 from rfl,
    show wordCount 56 = 2 by decide]
  have hM := log_memory (c := message.caller.toU256) hsize (e := 64) (by omega)
  have hMs : (memoryWrite (memoryExtend (wordBytes (bitwiseShl 96#256 message.caller.toU256)) 64)
      20 ⟨(bufferRead message.data 0 56).toArray⟩).size = 96 := by
    have hb : (⟨(bufferRead message.data 0 56).toArray⟩ : ByteArray).size = 56 := by
      show (bufferRead _ _ _).toArray.size = 56
      rw [List.size_toArray, bufferRead_length]
    rw [size_memoryWrite (by rw [hb, size_memoryExtend, size_wordBytes]; omega), size_memoryExtend,
      size_wordBytes]
  generalize memoryWrite (memoryExtend (wordBytes (bitwiseShl 96#256 message.caller.toU256)) 64)
    20 ⟨(bufferRead message.data 0 56).toArray⟩ = M at hM hMs ⊢
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have hle : extendMemory M.size [((0 : U256), 76#256)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [hMs]; decide)
  refine Triple.seq (log (n := 0) (words := []) (rest := [t]) rfl
    (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq]) (by decide)
    hstatic (by rw [hle]; simp only [logCost, OPCODE_LOG_BASE, OPCODE_LOG_DATA_PER_BYTE,
      OPCODE_LOG_TOPIC, BitVec.reduceToNat]; omega)) ?_
  rw [hle]
  dsimp only
  rw [memoryExtend_zero]
  have hM' : memoryReadBytes M 0 76 = logData message.caller message.data := hM
  simp only [BitVec.reduceToNat, show BitVec.toNat (0 : U256) = 0 from rfl, List.map_nil, hM',
    logCost, OPCODE_LOG_BASE, OPCODE_LOG_DATA_PER_BYTE, OPCODE_LOG_TOPIC, Nat.add_zero,
    Fin.val_zero, Nat.mul_zero, Nat.reduceMul, Nat.reduceAdd, Nat.sub_sub]
  clear hM hM' hle hMs hext hwc
  evm_step [CODE, CODE_NUMBER_eq]
  refine Triple.seq (binary (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (ofByte_of_decode rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) (by simp only [OPCODE_ADD, VERY_LOW]; omega)) ?_
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc5 (by omega)
    fun S6 hw6 _ g6 ss6 _ hl6 => ?_
  have hw6 := WritesStorage.trans hw5 hw6
  refine Spec.consequence (stop (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq])) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, hss⟩
  refine ⟨by simpa using herr, hout, ?_, ?_⟩
  · rw [hst]
    refine ⟨fun slot => ?_, hw6.2.1, hw6.2.2.1, hw6.2.2.2⟩
    have e1 := funext hw1.1
    have e3 := funext hw3.1
    have e4 := funext hw4.1
    have e5 := funext hw5.1
    rw [hw6.1, e5, e4, e3]
    change setSlot (setSlot (setSlot (setSlot (storageOf S1 message.currentTarget) _ _)
      _ _) _ _) _ _ slot = _
    rw [e1, ← ht]
    simp only [afterAdd, requestWords, SLOTS_PER_REQUEST, List.zipIdx_cons, List.zipIdx_nil,
      List.foldl_cons, List.foldl_nil]
    refine congrFun (setSlot_congr (setSlot_congr (setSlot_congr (setSlot_congr
      (setSlot_congr rfl rfl ?_) ?_ rfl) ?_ rfl) ?_ rfl) rfl ?_) slot <;>
      simp only [add, mul] <;> bv_omega
  · rw [hss, hl6]
    simp only [hl5, hl4, hl3, hl2, hl1, hl0]

/-- A call from another address with 56 bytes of input adds a request, as the code of EIP-7002 does.

It stores the amount big-endian, where the pseudocode of the EIP stores it little-endian.

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
    (hsize : message.data.size = 56)
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_WITHDRAWAL_REQUEST_FEE WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    (hgas : 200000 + 100 * m ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      if pays (storageOf state message.currentTarget) message.value then
        Added SLOTS_PER_REQUEST message.currentTarget (requestWords message.caller message.data)
          (logData message.caller message.data) state substate evm
      else Answer state none evm := by
  have hz : equal 56#256 (BitVec.ofNat 256 message.data.size) ≠ 0 := by
    rw [hsize]
    decide
  refine user_fee hfork hcaller hfits (by omega) (fun hinh evm h => ?_)
    (fun hinh g ss hg hlogs => ?_)
  · simp only [pays, fee, getFee, hinh, ite_true]
    exact h
  · have hF : fakeExponential MIN_WITHDRAWAL_REQUEST_FEE
        (storageOf state message.currentTarget 0).toNat WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION <
        2 ^ 256 := by
      obtain ⟨h1, h2, -, -⟩ := hfits hinh
      unfold MIN_WITHDRAWAL_REQUEST_FEE WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION at h1 h2 ⊢
      rw [Fees.BlobBaseFee.fakeExponential_eq_partialSum h1]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h2
    have hpays : pays (storageOf state message.currentTarget) message.value =
        decide (fakeExponential MIN_WITHDRAWAL_REQUEST_FEE
          (storageOf state message.currentTarget 0).toNat
          WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION ≤ message.value.toNat) := by
      simp only [pays, fee, getFee, hinh, ite_false]
    rw [hpays]
    generalize fakeExponential MIN_WITHDRAWAL_REQUEST_FEE
      (storageOf state message.currentTarget 0).toNat
      WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION = F at hF ⊢
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
      refine Spec.consequence (revert_500 hfork ?_ ?_) (fun _ h => h) fun evm h => ?_
      · simp
      · omega
      · exact h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)

/-! ## The system call -/

/-- A record has 76 bytes. -/
private theorem size_record (read : U256 → U256) (index : U256) :
    (record read index).size = 76 := by
  have hr : ∀ a : ByteArray, (⟨a.data.reverse⟩ : ByteArray).size = a.size := fun a => by
    simp [← ByteArray.size_data]
  simp only [record, ByteArray.size_append, ByteArray.size_extract, size_wordBytes, hr]
  decide

/-- From byte 308, the code writes the amount of a record, then comes back to the head of the loop.

The record starts at offset `76 * k`.

Memory holds `R` from offset 0: the first `k` records, then the first 68 bytes of this one.

The eight bytes of the amount are bytes 16 to 23 of the third word `v`, in reverse order. -/
private theorem deq_amount {S : TransactionState} {ss : Substate} {M R : ByteArray}
    {g k c : Nat} {v o r2 tail : U256} {Q : Evm fork Nat → Prop} (hfork : .shapella ≤ fork)
    (hR : Holds M 0 R) (hRs : R.size = 76 * k + 68) (hM : 76 * k + 76 ≤ M.size)
    (ho : o.toNat = 76 * k + 52) (hk : k < 16) (hg : 200 ≤ g)
    (next : ∀ M' g', Holds M' 0 (R ++ ⟨((wordBytes v).extract 16 24).data.reverse⟩) →
      M'.size = M.size → g ≤ g' + 200 →
      Spec fork (At CODE message 225 [BitVec.ofNat 256 (k + 1), BitVec.ofNat 256 c, r2, tail] M'
        g' S ss returnData) Q) :
    Spec fork (At CODE message 308 [v, o, BitVec.ofNat 256 k, BitVec.ofNat 256 c, r2, tail] M g S
      ss returnData) Q := by
  have hD : Holds M (76 * k + 76) ⟨([] : List UInt8).toArray⟩ := holds_empty (by omega)
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have h68 : (add 16#256 o).toNat = 76 * k + 68 := toNat_add_ofNat_of_lt ho (by omega)
  generalize add 16#256 o = o' at h68 ⊢
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (toNat_add_ofNat_of_lt h68 (by omega)) hR (by omega) hD (by omega) (by omega)
    fun M₄ hR₄ hD₄ hs₄ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (toNat_add_ofNat_of_lt h68 (by omega)) hR₄ (by omega) hD₄ (by omega) (by omega)
    fun M₅ hR₅ hD₅ hs₅ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (toNat_add_ofNat_of_lt h68 (by omega)) hR₅ (by omega) hD₅ (by omega) (by omega)
    fun M₆ hR₆ hD₆ hs₆ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (toNat_add_ofNat_of_lt h68 (by omega)) hR₆ (by omega) hD₆ (by omega) (by omega)
    fun M₇ hR₇ hD₇ hs₇ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (toNat_add_ofNat_of_lt h68 (by omega)) hR₇ (by omega) hD₇ (by omega) (by omega)
    fun M₈ hR₈ hD₈ hs₈ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (toNat_add_ofNat_of_lt h68 (by omega)) hR₈ (by omega) hD₈ (by omega) (by omega)
    fun M₉ hR₉ hD₉ hs₉ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    (toNat_add_ofNat_of_lt h68 (by omega)) hR₉ (by omega) hD₉ (by omega) (by omega)
    fun M₁₀ hR₁₀ hD₁₀ hs₁₀ => ?_
  refine mstore8_step (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    h68 hR₁₀ (by omega) hD₁₀ (by omega) (by omega) fun M₁₁ hR₁₁ hD₁₁ hs₁₁ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  rw [amount_bytes] at hD₁₁
  exact Spec.reshape (s' := [BitVec.ofNat 256 (k + 1), BitVec.ofNat 256 c, r2, tail])
    (by rw [add, BitVec.ofNat_add_ofNat, Nat.add_comm]) rfl rfl
    (next M₁₁ _ (hR₁₁.append (by rw [Nat.zero_add, hRs]; exact hD₁₁)) (by omega) (by omega))

/-- From the head of the loop at byte 225, one run writes the record `k` places after the head.

The memory holds the first `k` records, and grows to hold one more. -/
private theorem deq_body {read : U256 → U256} {S : TransactionState} {ss : Substate}
    {M : ByteArray} {g k c : Nat} {tail : U256} {Q : Evm fork Nat → Prop}
    (hfork : .shapella ≤ fork) (hk : k < c) (hc : c ≤ 16)
    (hread : storageOf S message.currentTarget = read) (hM : Holds M 0 (taken record read k))
    (hMs : M.size % 32 = 0) (hg : 9000 ≤ g)
    (next : ∀ M' S' g' ss', Holds M' 0 (taken record read (k + 1)) → M'.size % 32 = 0 →
      WritesStorage message.currentTarget read S S' → g ≤ g' + 9000 →
      Spec fork (At CODE message 225 [BitVec.ofNat 256 (k + 1), BitVec.ofNat 256 c, read 2, tail]
        M' g' S' ss' returnData) Q) :
    Spec fork (At CODE message 225 [BitVec.ofNat 256 k, BitVec.ofNat 256 c, read 2, tail] M g S
      ss returnData) Q := by
  have hne : equal (BitVec.ofNat 256 k) (BitVec.ofNat 256 c) = 0 := by
    rw [equal, ite_eq_right_iff]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hoff : (mul 76#256 (BitVec.ofNat 256 k)).toNat = 76 * k := by
    simp only [mul, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 256)]
    omega
  have hsl : add 4#256 (mul 3#256 (add (BitVec.ofNat 256 k) (read 2))) =
      4 + 3 * (read 2 + BitVec.ofNat 256 k) := by
    simp only [add, mul]
    bv_omega
  have hMk := hM.1
  rw [Nat.zero_add, size_taken size_record] at hMk
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
  generalize hgo : mul 76#256 (BitVec.ofNat 256 k) = off at hoff
  generalize hsl' : 4 + 3 * (read 2 + BitVec.ofNat 256 k) = sl
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g0 ss0 hg0 _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine mstore_grow (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    hMs hoff (by omega) (by omega) fun M₁ e₁ g₁ hM₁ hf₁ hs₁ hm₁ hg₁ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g2 ss2 hg2 _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  have h20 : (add 20#256 off).toNat = 76 * k + 20 := toNat_add_ofNat_of_lt hoff (by omega)
  refine mstore_grow (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    hm₁ h20 (by omega) (by omega) fun M₂ e₂ g3 hM₂ hf₂ hs₂ hm₂ hg3 => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g4 ss4 hg4 _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have h52 : (add 32#256 (add 20#256 off)).toNat = 76 * k + 52 :=
    toNat_add_ofNat_of_lt h20 (by omega)
  refine mstore_grow (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq])
    hm₂ h52 (by omega) (by omega) fun M₃ e₃ g5 hM₃ hf₃ hs₃ hm₃ hg5 => ?_
  simp only [storageOf_recordStorageRead, hread] at hM₁ hM₂ hM₃ ⊢
  have hR := holds_head hM (size_taken size_record read k) hM₁ hM₂ hM₃ hf₁ hf₂ hf₃
  have hRs : (taken record read k ++ ((wordBytes (read sl)).extract 12 32 ++
      wordBytes (read (add 1#256 sl)) ++ (wordBytes (read (add 2#256 sl))).extract 0 16)).size =
      76 * k + 68 := by
    simp only [ByteArray.size_append, ByteArray.size_extract, size_wordBytes,
      size_taken size_record]
    omega
  refine deq_amount hfork hR hRs (by omega) h52 (by omega) (by omega) fun M' g' hR' hs' hg' => ?_
  refine next M' _ g' _ ?_ (by rw [hs']; exact hm₃)
    ⟨fun _ => by simp [hread, storageOf_recordStorageRead], fun _ _ _ => rfl, fun _ => rfl,
      fun _ => rfl⟩ (by omega)
  have e : record read (read 2 + BitVec.ofNat 256 k) = (wordBytes (read sl)).extract 12 32 ++
      wordBytes (read (add 1#256 sl)) ++ (wordBytes (read (add 2#256 sl))).extract 0 16 ++
      ⟨((wordBytes (read (add 2#256 sl))).extract 16 24).data.reverse⟩ := by
    simp only [record, hsl', add, BitVec.add_comm sl]
    rfl
  rw [taken_succ, e]
  rw [ByteArray.append_assoc] at hR'
  exact hR'

/-- From the head of the loop at byte 225, the loop writes the records from request `k` up to `c`.

It leaves at byte 387, with the records of the first `c` requests in memory. -/
private theorem deq_loop {read : U256 → U256} {tail : U256} {c : Nat} {Q : Evm fork Nat → Prop}
    (hfork : .shapella ≤ fork) (hc : c ≤ 16) (n : Nat) :
    ∀ {S : TransactionState} {ss : Substate} {M : ByteArray} {g k : Nat}, k + n = c →
    storageOf S message.currentTarget = read → Holds M 0 (taken record read k) →
    M.size % 32 = 0 → deqGas n ≤ g →
    (∀ M' S' g' ss', Holds M' 0 (taken record read c) →
      WritesStorage message.currentTarget read S S' → g ≤ g' + deqGas n →
      Spec fork (At CODE message 387 [BitVec.ofNat 256 c, BitVec.ofNat 256 c, read 2, tail] M' g'
        S' ss' returnData) Q) →
    Spec fork (At CODE message 225 [BitVec.ofNat 256 k, BitVec.ofNat 256 c, read 2, tail] M g S
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
    exact next M S _ ss hM (hread ▸ WritesStorage.refl _ _) (by omega)
  | succ n ih =>
    intro S ss M g k hk hread hM hMs hg next
    simp only [deqGas] at hg next
    refine deq_body hfork (by omega) hc hread hM hMs (by omega) fun M₁ S₁ g₁ ss₁ hM₁ hM₁s hw₁ hg₁ =>
      ih (by omega) (funext hw₁.1) hM₁ hM₁s (by omega) fun M' S' g' ss' hM' hw' hg' =>
        next M' S' g' ss' hM' (WritesStorage.trans hw₁ hw')
          (Nat.le_trans hg₁ (by rw [← Nat.add_assoc]; exact Nat.add_le_add_right hg' _))

/-- From byte 488, the code writes the excess `v` and resets the count of the block.

It then returns the records, `76` bytes for each request taken. -/
private theorem deq_end {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {v x : U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hM : (mul 76#256 x).toNat ≤ M.size) (hg : 50000 * storageGasScale fork ≤ g) :
    Spec fork (At CODE message 488 [v, x] M g S ss returnData)
      (Returned message.currentTarget M (mul 76#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0) S) := by
  have hscale := one_le_storageGasScale fork
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc (by omega)
    fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc₁ (by omega)
    fun S₂ hw₂ _ g₂ ss₂ hg₂ _ => ?_
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  have hle : extendMemory M.size [((0 : U256), mul 76#256 x)] = ⟨0, 0⟩ :=
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

/-- From byte 461, the code computes the new excess from the previous excess `p` and the count.

The previous excess plus the count is below `2^256`. -/
private theorem deq_count {S : TransactionState} {ss : Substate} {M : ByteArray} {g p : Nat}
    {x : U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hp : p + (storageOf S message.currentTarget 1#256).toNat < 2 ^ 256)
    (hM : (mul 76#256 x).toNat ≤ M.size) (hg : 60000 * storageGasScale fork ≤ g) :
    Spec fork (At CODE message 461 [BitVec.ofNat 256 p, x] M g S ss returnData)
      (Returned message.currentTarget M (mul 76#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (if p + (storageOf S message.currentTarget 1#256).toNat > 2 then
            p + (storageOf S message.currentTarget 1#256).toNat - 2 else 0))) 1 0) S) := by
  have hscale := one_le_storageGasScale fork
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
  have hsub : 2 ≤ p + n → sub (BitVec.ofNat 256 (p + n)) 2#256 =
      BitVec.ofNat 256 (p + n - 2) := by
    intro h2
    apply BitVec.eq_of_toNat_eq
    simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
    omega
  have post : ∀ v, ∀ evm : Evm fork Nat, Returned message.currentTarget M (mul 76#256 x).toNat
      (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0)
      (S.recordStorageRead message.currentTarget (U256.toBeBytes 1#256)) evm →
      Returned message.currentTarget M (mul 76#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0) S evm :=
    fun _ _ ⟨h1, h2, h3⟩ =>
      ⟨h1, h2, WritesStorage.trans (WritesStorage.recordStorageRead _ _ _ _) h3⟩
  by_cases hgt : p + n > 2
  · have hz : greaterThan (BitVec.ofNat 256 (p + n)) 2#256 ≠ 0 := by
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
    exact Spec.consequence (deq_end hfork hstatic hacc₁ hM (by omega)) (fun _ h => h)
      (post _)
  · have hz : greaterThan (BitVec.ofNat 256 (p + n)) 2#256 = 0 := by
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
    exact Spec.consequence (deq_end hfork hstatic hacc₁ hM (by omega)) (fun _ h => h)
      (post _)

/-- From byte 416, the code updates the excess for a target of 2 per block, and resets the count.

It then returns the records, `76` bytes for each request taken. -/
private theorem deq_excess {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {x : U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hb : previousExcess (storageOf S message.currentTarget 0) +
      (storageOf S message.currentTarget 1#256).toNat < 2 ^ 256)
    (hM : (mul 76#256 x).toNat ≤ M.size) (hg : 70000 * storageGasScale fork ≤ g) :
    Spec fork (At CODE message 416 [x] M g S ss returnData)
      (Returned message.currentTarget M (mul 76#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (newExcess 2 (storageOf S message.currentTarget 0)
            (storageOf S message.currentTarget 1)))) 1 0) S) := by
  have hscale := one_le_storageGasScale fork
  evm_step [CODE, CODE_NUMBER_eq]
  evm_step [CODE, CODE_NUMBER_eq]
  refine sload_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
    (by evm_code [CODE, CODE_NUMBER_eq]) (by omega) fun g₁ ss₁ hg₁ _ => ?_
  have hacc₁ : ((S.recordStorageRead message.currentTarget (U256.toBeBytes 0)).getAccountOptional
      message.currentTarget).isSome = true := hacc
  have post : ∀ evm : Evm fork Nat, Returned message.currentTarget M (mul 76#256 x).toNat
      (setSlot (setSlot (storageOf S message.currentTarget) 0
        (BitVec.ofNat 256 (newExcess 2 (storageOf S message.currentTarget 0)
          (storageOf S message.currentTarget 1)))) 1 0)
      (S.recordStorageRead message.currentTarget (U256.toBeBytes 0)) evm →
      Returned message.currentTarget M (mul 76#256 x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (newExcess 2 (storageOf S message.currentTarget 0)
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
    refine Spec.consequence (deq_count (p := 0) hfork hstatic hacc₁ hb hM (by omega))
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
    refine Spec.consequence (deq_count hfork hstatic hacc₁ hb hM (by omega))
      (fun _ h => h) fun evm h => post evm ?_
    unfold newExcess
    rw [hp]
    exact h

/-- From byte 387, the code moves the head of the queue, or empties it, then updates the excess.

It returns the records of the requests it took, which memory holds. -/
private theorem deq_head {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {r : U256 → U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hr : storageOf S message.currentTarget = r) (hb : Bounded r)
    (hMs : 76 * numDequeued 16 r ≤ M.size) (hg : 120000 * storageGasScale fork ≤ g) :
    Spec fork (At CODE message 387 [BitVec.ofNat 256 (numDequeued 16 r),
        BitVec.ofNat 256 (numDequeued 16 r), r 2, r 3] M g S ss returnData)
      (Returned message.currentTarget M (76 * numDequeued 16 r) (afterDequeue 16 2 r) S) := by
  have hscale := one_le_storageGasScale fork
  obtain ⟨hht, hex⟩ := hb
  have hc2 : numDequeued 16 r ≤ 16 := Nat.min_le_right _ _
  have hle : (r 2).toNat + numDequeued 16 r ≤ (r 3).toNat := by
    unfold numDequeued
    have h : Nat.min ((r 3).toNat - (r 2).toNat) 16 ≤ (r 3).toNat - (r 2).toNat :=
      Nat.min_le_left _ _
    omega
  have ht := (r 3).isLt
  generalize hc : numDequeued 16 r = c at hc2 hle hMs ⊢
  have hnh : add (r 2) (BitVec.ofNat 256 c) = BitVec.ofNat 256 ((r 2).toNat + c) := by
    apply BitVec.eq_of_toNat_eq
    simp only [add, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 256), Nat.mod_eq_of_lt (by omega)]
  have hmul : (mul 76#256 (BitVec.ofNat 256 c)).toNat = 76 * c := by
    simp only [mul, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 256)]
    omega
  have hM : (mul 76#256 (BitVec.ofNat 256 c)).toNat ≤ M.size := by rw [hmul]; exact hMs
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
    refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
      (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc (by omega)
      fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine sstore_then (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER_eq])
      (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc₁ (by omega)
      fun S₂ hw₂ hacc₂ g₂ ss₂ hg₂ _ => ?_
    have eF : storageOf S₂ message.currentTarget = setSlot (setSlot r 2 0) 3 0 := by
      rw [funext hw₂.1, funext hw₁.1, hr]
      rfl
    refine Spec.consequence (deq_excess hfork hstatic hacc₂
      (hr0 _ (by rw [eF]; simp [setSlot]) (by rw [eF]; simp [setSlot])) hM (by omega))
      (fun _ h => h) fun evm h => ?_
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [h2, hmul], ?_⟩
    have hw := WritesStorage.trans (WritesStorage.trans hw₁ hw₂) h3
    rw [eF, deq_store 16 2 r (setSlot (setSlot r 2 0) 3 0) (by rw [hc, ite_eq_left hnt])] at hw
    exact hw
  · have hz : equal (r 3) (BitVec.ofNat 256 ((r 2).toNat + c)) = 0 := by
      simp only [equal]
      rw [ite_eq_right_iff]
      exact fun e => absurd (heqv.mp e) hnt
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine sstore_then (Nat.le_trans (by decide) hfork)
      (by evm_code [CODE, CODE_NUMBER_eq]) (by evm_code [CODE, CODE_NUMBER_eq]) hstatic hacc
      (by omega) fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    have eF : storageOf S₁ message.currentTarget =
        setSlot r 2 (BitVec.ofNat 256 ((r 2).toNat + c)) := by
      rw [funext hw₁.1, hr]
      rfl
    refine Spec.consequence (deq_excess hfork hstatic hacc₁
      (hr0 _ (by rw [eF]; simp [setSlot]) (by rw [eF]; simp [setSlot])) hM (by omega))
      (fun _ h => h) fun evm h => ?_
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [h2, hmul], ?_⟩
    have hw := WritesStorage.trans hw₁ h3
    rw [eF, deq_store 16 2 r (setSlot r 2 (BitVec.ofNat 256 ((r 2).toNat + c)))
      (by rw [hc, ite_eq_right hnt])] at hw
    exact hw

/-- At most 16 runs of the loop of the system call take at most 144,030 gas. -/
private theorem deqGas_le {n : Nat} (hn : n ≤ 16) : deqGas n ≤ 144030 := by
  have h : ∀ n, deqGas n = 30 + 9000 * n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [deqGas, ih]; omega
  rw [h]
  omega

/-- From the head of the loop at byte 225, with memory empty, the code takes the requests.

It returns their records, and holds the storage after the requests are taken. -/
private theorem deq_rest {S : TransactionState} {ss : Substate} {g : Nat} {r : U256 → U256}
    (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hr : storageOf S message.currentTarget = r) (hb : Bounded r)
    (hg : 265000 * storageGasScale fork ≤ g) :
    Spec fork (At CODE message 225 [BitVec.ofNat 256 0, BitVec.ofNat 256 (numDequeued 16 r), r 2,
        r 3] .empty g S ss returnData) fun evm =>
      evm.error = none ∧ evm.output = taken record r (numDequeued 16 r) ∧
      WritesStorage message.currentTarget (afterDequeue 16 2 r) S evm.state := by
  have hscale := one_le_storageGasScale fork
  have hc2 : numDequeued 16 r ≤ 16 := Nat.min_le_right _ _
  have hdg := deqGas_le hc2
  refine deq_loop hfork hc2 (numDequeued 16 r) (by omega) hr (holds_empty (Nat.le_refl _)) rfl
    (by omega) fun M' S' g' ss' hM' hw' hg' => ?_
  have hacc' : (S'.getAccountOptional message.currentTarget).isSome = true := by
    rw [hw'.2.2.1]; exact hacc
  have hMs := hM'.1
  rw [Nat.zero_add, size_taken size_record] at hMs
  refine Spec.consequence (deq_head hfork hstatic hacc' (funext hw'.1) hb hMs
    (by omega)) (fun _ h => h) fun evm ⟨h1, h2, h3⟩ => ⟨h1, ?_, WritesStorage.trans hw' h3⟩
  rw [h2]
  have := hM'.2
  rw [size_taken size_record] at this
  exact this

/-- A call from the system address takes requests from the queue, as EIP-7002 describes.

It holds from Shapella, on a frame that may change the state.

The account of the contract exists.

The one-counter budget is 300,000 gas before Glamsterdam and 1,500,000 from Glamsterdam.

The counters of the storage meet the bounds under which the code computes as the EIP.

The frame stops with no error, and returns the records of at most 16 requests from the head.

The state holds the storage after the requests are taken, the excess updated and the count reset.

It keeps the storage of every other account, the accounts and the codes. -/
theorem spec_dequeue (hfork : .shapella ≤ fork)
    (hcaller : message.caller = SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hbounded : Bounded (storageOf state message.currentTarget))
    (hgas : 300000 * storageGasScale fork ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      evm.error = none ∧
      evm.output = dequeued MAX_WITHDRAWAL_REQUESTS_PER_BLOCK record
        (storageOf state message.currentTarget) ∧
      WritesStorage message.currentTarget
        (afterDequeue MAX_WITHDRAWAL_REQUESTS_PER_BLOCK TARGET_WITHDRAWAL_REQUESTS_PER_BLOCK
          (storageOf state message.currentTarget))
        state evm.state := by
  have hscale := one_le_storageGasScale fork
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
      (evm.error = none ∧ evm.output = taken record r (numDequeued 16 r) ∧
      WritesStorage message.currentTarget (afterDequeue 16 2 r)
        ((state.recordStorageRead message.currentTarget (U256.toBeBytes 3#256)
          ).recordStorageRead message.currentTarget (U256.toBeBytes 2#256)) evm.state) →
      evm.error = none ∧ evm.output = dequeued MAX_WITHDRAWAL_REQUESTS_PER_BLOCK record r ∧
        WritesStorage message.currentTarget
          (afterDequeue MAX_WITHDRAWAL_REQUESTS_PER_BLOCK
            TARGET_WITHDRAWAL_REQUESTS_PER_BLOCK r) state evm.state :=
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
  by_cases hd : (r 3).toNat - (r 2).toNat < 16
  · have hz : greaterThan 16#256 (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)) ≠ 0 := by
      have hlt : (16#256).toNat > (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)).toNat := by
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : (r 3).toNat - (r 2).toNat < 2 ^ 256)]
        omega
      rw [greaterThan, ite_eq_left hlt]
      decide
    have hn : numDequeued 16 r = (r 3).toNat - (r 2).toNat := Nat.min_eq_left (by omega)
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    rw [← hn]
    refine Spec.consequence (deq_rest hfork hstatic hacc' hS ⟨hht, hex⟩ ?_)
      (fun _ h => h) post
    omega
  · have hz : greaterThan 16#256 (BitVec.ofNat 256 ((r 3).toNat - (r 2).toNat)) = 0 := by
      rw [greaterThan, ite_eq_right_iff]
      intro h
      have h' : 16 > (r 3).toNat - (r 2).toNat := by
        simp only [BitVec.toNat_ofNat] at h
        rw [Nat.mod_eq_of_lt (by omega : (r 3).toNat - (r 2).toNat < 2 ^ 256)] at h
        omega
      exact absurd h' hd
    have hn : numDequeued 16 r = 16 := Nat.min_eq_right (by omega)
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    evm_step [CODE, CODE_NUMBER_eq]
    refine Spec.reshape (s' := [BitVec.ofNat 256 0, BitVec.ofNat 256 (numDequeued 16 r), r 2, r 3])
      (by rw [hn]; rfl) rfl rfl ?_
    refine Spec.consequence (deq_rest hfork hstatic hacc' hS ⟨hht, hex⟩ ?_)
      (fun _ h => h) post
    omega

/-- The withdrawal request address is not a precompile. -/
theorem addedAt_WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS :
    Precompiles.addedAt WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS.toU256.toNat = none := by
  rw [WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS, EthLib.Base.toNat_toU256_toAddressMasked]
  rfl

/-- The code is not a delegation indicator: it has 504 bytes, not 23. -/
theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  simp [delegatedAddress, isValidDelegation, CODE, NatCode.size_ofNat, DELEGATION_SIZE]

/-- From Pectra, the system call of a block to the contract takes its requests.

The account at the withdrawal request address must hold the code of EIP-7002.

The counters of its storage meet the bounds under which the code computes as the EIP.

The call succeeds, whatever its data, and returns the records of at most 16 requests.

The storage of the contract is then the storage after the requests are taken.

The call keeps the storage of every other account, the accounts and the codes. -/
theorem systemCall_dequeue {env : BlockEnvironment fork} {block : State.BlockState}
    {data : ByteArray} (hfork : .pectra ≤ fork)
    (hcode : codeAt block WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS = .ok CODE)
    (hbounded : Bounded (storageOf (.ofBlock block) WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS)) :
    ∃ out, systemCall env block WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS data = .ok out ∧
      out.error = none ∧
      out.output = dequeued MAX_WITHDRAWAL_REQUESTS_PER_BLOCK record
        (storageOf (.ofBlock block) WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS) ∧
      WritesStorage WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS
        (afterDequeue MAX_WITHDRAWAL_REQUESTS_PER_BLOCK TARGET_WITHDRAWAL_REQUESTS_PER_BLOCK
          (storageOf (.ofBlock block) WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS))
        (.ofBlock block) out.state :=
  systemCall_of_writesStorage_all (P := Bounded) _ _ (Nat.le_trans (by decide) hfork)
    supportedCode_CODE hcode
    (by simp [CODE, NatCode.size_ofNat]) addedAt_WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS
    delegatedAddress_CODE hbounded
    fun message _ _ hcaller htarget hstatic _ _ hgas hacc hread => by
      rw [← htarget]
      exact spec_dequeue (Nat.le_trans (by decide) hfork) hcaller hstatic (htarget ▸ hacc)
        (htarget ▸ hread) (by
          rw [hgas]
          have := storageGasScale_le fork
          simp only [SYSTEM_TRANSACTION_GAS]
          omega)

end EthLib.Execution.Blocks.WithdrawalRequests
