module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract
public import EthLib.Execution.Proofs.Blocks.SystemCall.WithdrawalRequests.Record
public import EthLib.Execution.Proofs.Blocks.SystemCall.FeePath
public import EthLib.Execution.Proofs.Blocks.SystemCall.DequeueTail
public import EthLib.Execution.Proofs.Blocks.SystemCall.AddPath

/-!
# Proofs: the withdrawal request contract of EIP-7002 does what its EIP describes

The contract keeps a queue of withdrawal requests, and a fee that rises with its use.

Each operation of the EIP is a function here.

A theorem runs the code and shows that it computes that function.

The code is the 504 bytes of [EIP-7002][eip-7002-deployment], which its deployment installs.

Source: [EIP-7002][eip-7002-contract].

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

/-- The three words of a request from `caller` with the input `input`, as the queue holds them.

They are the caller, then the two words of the input, read big-endian with zeros past its end.

The last word holds the end of the public key, the amount big-endian, then 8 zero bytes. -/
def requestWords (caller : Address) (input : ByteArray) : List U256 :=
  requestWordsOf 2 caller input

/-- The data of the log of a request: the 20 bytes of the caller, then the input. -/
def logData (caller : Address) (input : ByteArray) : ByteArray :=
  requestLog caller input

/-- The record of 76 bytes of the request at the index `index`, counted from the start of the queue.

It is the source address, the public key of the validator, then the amount, little-endian. -/
def record (read : U256 → U256) (index : U256) : ByteArray :=
  let slot := 4 + 3 * index
  -- The address is the last 20 bytes of the first slot, since the code stores the caller as a word.
  --
  -- The pseudocode of the EIP slices bytes 0 to 20 instead.
  --
  -- The key starts with the 32 bytes of the second slot.
  (wordBytes (read slot)).extract 12 32 ++ wordBytes (read (slot + 1)) ++
    -- The key ends with the first 16 bytes of the third slot.
    (wordBytes (read (slot + 2))).extract 0 16 ++
    -- The amount is the next 8 bytes of the third slot, in reverse order.
    --
    -- A record ends with the amount as 8 bytes, little-endian, as the EIP encodes it.
    --
    -- The code keeps the amount big-endian in storage, and reverses its bytes to read a request.
    --
    -- The pseudocode of the EIP stores it little-endian, and reads it as it is.
    --
    -- So the third slot of a request differs from the pseudocode, but the records are the same.
    ⟨((wordBytes (read (slot + 2))).extract 16 24).data.reverse⟩

/-- The code is not a delegation indicator: it has 504 bytes, not 23. -/
theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  simp [delegatedAddress, isValidDelegation, CODE, NatCode.size_ofNat, DELEGATION_SIZE]

/-- The contract as a request contract, with the code, the constants and the record of EIP-7002. -/
def WITHDRAWAL_REQUEST : RequestContract where
  entry := WITHDRAWAL_REQUEST_CONTRACT
  type := WITHDRAWAL_REQUEST_TYPE
  code := CODE
  maxPerBlock := MAX_WITHDRAWAL_REQUESTS_PER_BLOCK
  targetPerBlock := TARGET_WITHDRAWAL_REQUESTS_PER_BLOCK
  minFee := MIN_WITHDRAWAL_REQUEST_FEE
  feeFraction := WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION
  inputSize := 56
  record := record
  mem := by simp [SYSTEM_CONTRACTS]
  kind_eq := rfl
  size_ne_zero := by simp [CODE, NatCode.size_ofNat]
  supported := supportedCode_CODE
  delegatedAddress_eq_none := delegatedAddress_CODE

/-- What a call with the input `input` and the value `value` gets, when it adds no request.

With no input and no value, it gets the fee as a word, or reverts while the inhibitor holds.

Any input of a size other than 0 or 56 bytes reverts, and so does a value with no input.

The EIP gives only the fee for no input; these reverts come from its code. -/
def getFeeResult (read : U256 → U256) (input : ByteArray) (value : U256) : Option U256 :=
  WITHDRAWAL_REQUEST.getFeeResult read input value

/-- A call with the value `value` pays the fee: the fee is defined and at most the value. -/
def pays (read : U256 → U256) (value : U256) : Bool :=
  WITHDRAWAL_REQUEST.pays read value

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

/-- The code runs the path of a call from another address, with the constants of EIP-7002. -/
theorem feePathCode_CODE :
    FeePathCode CODE 0xcb WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION 500 56 where
  size_le := by simp [CODE, NatCode.size_ofNat]
  byte := FeePathCode.byte_ofNat (by decide +kernel)
  push1 := by evm_code [CODE, CODE_NUMBER_eq]
  push31 := by evm_code [CODE, CODE_NUMBER_eq]
  push117 := by evm_code [CODE, CODE_NUMBER_eq]
  push132 := by evm_code [CODE, CODE_NUMBER_eq]
  push23 := by evm_code [CODE, CODE_NUMBER_eq]
  push26 := by evm_code [CODE, CODE_NUMBER_eq, WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION]
  push65 := by evm_code [CODE, CODE_NUMBER_eq]
  push114 := by evm_code [CODE, CODE_NUMBER_eq]
  system_lt := by decide
  fraction_lt := by decide
  size_lt := by decide
  dest_system := by evm_dest [CODE, CODE_NUMBER_eq]
  push121 := by evm_code [CODE, CODE_NUMBER_eq]
  push126 := by evm_code [CODE, CODE_NUMBER_eq]
  push139 := by evm_code [CODE, CODE_NUMBER_eq]
  loop := feeLoopCode_CODE
  dest136 := by evm_dest [CODE, CODE_NUMBER_eq]
  revert_lt := by decide
  revert_end := by simp [CODE, NatCode.size_ofNat]
  dest_revert := by evm_dest [CODE, CODE_NUMBER_eq]
  revert0 := by evm_code [CODE, CODE_NUMBER_eq]
  revert1 := by evm_code [CODE, CODE_NUMBER_eq]
  revert2 := by evm_code [CODE, CODE_NUMBER_eq]
  revert3 := by evm_code [CODE, CODE_NUMBER_eq]

/-- The code ends its system call from byte 387, for a target of 2 and records of 76 bytes. -/
theorem dequeueTailCode_CODE : DequeueTailCode CODE 387 2 76 where
  size_le := by simp [CODE, NatCode.size_ofNat]
  end_lt := by decide
  byte := DequeueTailCode.byte_ofNat (by decide +kernel)
  push11 := by evm_code [CODE, CODE_NUMBER_eq]
  push22 := by evm_code [CODE, CODE_NUMBER_eq]
  push26 := by evm_code [CODE, CODE_NUMBER_eq]
  push33 := by evm_code [CODE, CODE_NUMBER_eq]
  push75 := by evm_code [CODE, CODE_NUMBER_eq]
  push105 := by evm_code [CODE, CODE_NUMBER_eq]
  push6 := by evm_code [CODE, CODE_NUMBER_eq]
  push14 := by evm_code [CODE, CODE_NUMBER_eq]
  push68 := by evm_code [CODE, CODE_NUMBER_eq]
  push84 := by evm_code [CODE, CODE_NUMBER_eq]
  push91 := by evm_code [CODE, CODE_NUMBER_eq]
  dest18 := by evm_dest [CODE, CODE_NUMBER_eq]
  dest29 := by evm_dest [CODE, CODE_NUMBER_eq]
  dest74 := by evm_dest [CODE, CODE_NUMBER_eq]
  dest95 := by evm_dest [CODE, CODE_NUMBER_eq]
  dest101 := by evm_dest [CODE, CODE_NUMBER_eq]
  push78 := by evm_code [CODE, CODE_NUMBER_eq]
  push97 := by evm_code [CODE, CODE_NUMBER_eq]
  push108 := by evm_code [CODE, CODE_NUMBER_eq]
  target_lt := by decide
  size_lt := by decide

/-- From byte 143, the code adds a request of 2 input words, 56 bytes long. -/
theorem addPathCode_CODE : AddPathCode CODE 2 56 where
  two_le := by decide
  log_lt := by decide
  size_le := by simp [CODE, NatCode.size_ofNat]
  head := fun i h h1 h2 h3 => by
    obtain ⟨k, rfl⟩ : ∃ k, i = 143 + k := ⟨i - 143, by omega⟩
    rw [Nat.add_sub_cancel_left]
    exact AddPathCode.getElem_of_holdsExcept (skip := [14]) (by decide +kernel) h (by omega)
      (by simp; omega)
  push156 := by evm_code [CODE, CODE_NUMBER_eq]
  word := fun j h1 h2 => absurd h2 (by omega)
  pushWord := fun j h1 h2 => absurd h2 (by omega)
  last := fun i h hi h1 =>
    AddPathCode.getElem_of_holdsExcept (skip := [1]) (by decide +kernel) h hi (by simpa using h1)
  pushLast := by evm_code [CODE, CODE_NUMBER_eq]
  log := fun i h hi h1 h2 =>
    AddPathCode.getElem_of_holdsExcept (skip := [7, 13]) (by decide +kernel) h hi
      (by simp; omega)
  pushSize := by evm_code [CODE, CODE_NUMBER_eq]
  pushLog := by evm_code [CODE, CODE_NUMBER_eq]

/-! The proofs read the code through the equation above, never by unfolding it.

The number of the code is a sum of terms with powers of 256 up to `256^464`.

Without the attribute, each step reduces these powers, and the step exceeds the recursion depth.

The attribute keeps the code opaque, so the steps read it only through the equation. -/
attribute [local irreducible] CODE

/-! ## A call that adds no request -/

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- A call from another address, whose input is not 56 bytes, gets the fee or reverts.

It holds from Shapella, with the one-counter meter.

From Glamsterdam, a run with no error carries to the state gas meter of the protocol. -/
theorem spec_getFee {m : Nat} (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hsize : message.data.size ≠ 56)
    -- It assumes fewer than `2^256` bytes of input, which the size word of the EVM can hold.
    (hbound : message.data.size < 2 ^ 256)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_WITHDRAWAL_REQUEST_FEE WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    -- The frame has at least 100,000 gas, and 100 more for each of these steps.
    (hgas : 100000 + 100 * m ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData)
      -- The frame returns the fee as a word or reverts with no output, as the code of the EIP does.
      --
      -- Its state reads as the state it starts from.
      (Answer state (getFeeResult (storageOf state message.currentTarget) message.data
        message.value)) :=
  WITHDRAWAL_REQUEST.spec_getFee feePathCode_CODE rfl hfork hcaller hsize hbound hfits (by omega)

/-! ## A call that adds a request -/

/-- A call from another address with 56 bytes of input adds a request, as the code of EIP-7002 does.

It stores the amount big-endian, where the pseudocode of the EIP stores it little-endian.

It holds from Shapella up to BPO5, on a frame that may change the state. -/
theorem spec_add {m : Nat} (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    -- The account of the contract exists.
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    -- The input is the public key of the validator, then the amount as 8 bytes, big-endian.
    (hsize : message.data.size = 56)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_WITHDRAWAL_REQUEST_FEE WITHDRAWAL_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    -- The frame has at least 200,000 gas, and 100 more for each of these steps.
    (hgas : 200000 + 100 * m ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- When the value pays the fee, the frame adds the request of the caller and the input.
      if pays (storageOf state message.currentTarget) message.value then
        -- It stores the request words at the tail of the queue, and logs the caller and the input.
        Added SLOTS_PER_REQUEST message.currentTarget (requestWords message.caller message.data)
          (logData message.caller message.data) state substate evm
      -- Otherwise it reverts with no output, and its state reads as the state it starts from.
      else Answer state none evm := by
  refine WITHDRAWAL_REQUEST.spec_pay feePathCode_CODE rfl hfork hcaller hsize hfits (by omega)
    fun _ g ss hg hlogs => Spec.consequence (addPathCode_CODE.spec_add
      (S := state.recordStorageRead message.currentTarget (U256.toBeBytes 0)) hfork hglam
      hstatic hacc hsize (by omega)) (fun _ h => h) ?_
  rintro evm ⟨⟨herr, hout, hw, hlog⟩, -⟩
  exact ⟨herr, hout, hw, by rw [hlog, hlogs]; rfl⟩

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
  refine Spec.consequence (dequeueTailCode_CODE.spec_head hfork hstatic hacc' (funext hw'.1) hb
    (by decide) hMs
    (by omega)) (fun _ h => h) fun evm ⟨h1, h2, h3⟩ => ⟨h1, ?_, WritesStorage.trans hw' h3⟩
  rw [h2]
  have := hM'.2
  rw [size_taken size_record] at this
  exact this

/-- A call from the system address takes requests from the queue, as EIP-7002 describes.

It holds from Shapella, on a frame that may change the state. -/
theorem spec_dequeue (hfork : .shapella ≤ fork)
    (hcaller : message.caller = SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    -- The account of the contract exists.
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    -- The counters of the storage meet the bounds under which the code computes as the EIP.
    (hbounded : Bounded (storageOf state message.currentTarget))
    -- The conservative one-counter budget is 300,000 gas before Glamsterdam and 1,500,000 from it.
    (hgas : 300000 * storageGasScale fork ≤ gas) :
    -- From Glamsterdam, this one-counter frame is a model for the proof, not the meter of EIP-8037.
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- The frame stops with no error.
      evm.error = none ∧
      -- It returns the records, of 76 bytes each, of at most 16 requests from the head.
      evm.output = dequeued MAX_WITHDRAWAL_REQUESTS_PER_BLOCK record
        (storageOf state message.currentTarget) ∧
      -- The state holds the storage after the requests are taken and the count reset.
      --
      -- The excess is updated for a target of 2 requests per block.
      --
      -- It keeps the storage of every other account, the accounts and the codes.
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
    Precompiles.addedAt WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS.toU256.toNat = none :=
  WITHDRAWAL_REQUEST.addedAt

/-- From Shapella, the code takes the requests with 300,000 gas, scaled from Glamsterdam. -/
theorem dequeues (hfork : .shapella ≤ fork) : WITHDRAWAL_REQUEST.Dequeues fork 300000 :=
  fun _ _ _ _ hcaller hstatic hacc hread hgas =>
    spec_dequeue hfork hcaller hstatic hacc hread hgas

/-- From Pectra, the system call of a block to the contract takes its requests.

It runs with the gas meter of its fork. -/
theorem systemCall_dequeue {env : BlockEnvironment fork} {block : State.BlockState}
    {data : ByteArray} (hfork : .pectra ≤ fork)
    -- The account at the withdrawal request address must hold the code of EIP-7002.
    (hcode : codeAt block WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS = .ok CODE)
    -- The counters of its storage meet the bounds under which the code computes as the EIP.
    (hbounded : Bounded (storageOf (.ofBlock block) WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS)) :
    -- The call succeeds, whatever its data, and returns the records of at most 16 requests.
    ∃ out, systemCall env block WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS data = .ok out ∧
      out.error = none ∧
      out.output = dequeued MAX_WITHDRAWAL_REQUESTS_PER_BLOCK record
        (storageOf (.ofBlock block) WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS) ∧
      -- The storage of the contract is then the storage after the requests are taken.
      --
      -- The call keeps the storage of every other account, the accounts and the codes.
      WritesStorage WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS
        (afterDequeue MAX_WITHDRAWAL_REQUESTS_PER_BLOCK TARGET_WITHDRAWAL_REQUESTS_PER_BLOCK
          (storageOf (.ofBlock block) WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS))
        (.ofBlock block) out.state :=
  WITHDRAWAL_REQUEST.systemCall_dequeue (Nat.le_trans (by decide) hfork)
    (dequeues (Nat.le_trans (by decide) hfork))
    (by have := storageGasScale_le fork; simp only [SYSTEM_TRANSACTION_GAS]; omega)
    hcode hbounded

/-- Empty withdrawal request code rejects the request phase of a block from Pectra.

Reading the requests then fails with the empty-contract error.

This is the rejection that [EIP-7002][eip7002] requires.

[eip7002]: https://eips.ethereum.org/EIPS/eip-7002#system-call -/
theorem readRequests_of_empty {env : BlockEnvironment fork} {body : BodyState}
    (hfork : .pectra ≤ fork)
    (hcode : codeAt body.block WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS = .ok .empty) :
    readRequests env body = .error (.systemContractEmpty WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS) :=
  readRequests_of_empty_after (pre := []) (requestContracts_of_pectra hfork) rfl hcode

/-- No block request result succeeds when the withdrawal contract has no code.

This is the rejection required by [EIP-7002][eip7002].

[eip7002]: https://eips.ethereum.org/EIPS/eip-7002#system-call -/
theorem blockRequests_ne_ok_of_empty {env : BlockEnvironment fork} {body : BodyState}
    {depositContract : Address} {logs : List Log} {result : BodyState × List ByteArray}
    (hfork : .pectra ≤ fork)
    (hcode : codeAt body.block WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS = .ok .empty) :
    blockRequests depositContract env body logs ≠ .ok result :=
  blockRequests_ne_ok_of_readRequests_error hfork (readRequests_of_empty hfork hcode)

end EthLib.Execution.Blocks.WithdrawalRequests
