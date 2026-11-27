module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract
public import EthLib.Execution.Proofs.Blocks.SystemCall.FeePath
public import EthLib.Execution.Proofs.Blocks.SystemCall.DequeueStart
public import EthLib.Execution.Proofs.Blocks.SystemCall.DequeueTail
public import EthLib.Execution.Proofs.Blocks.SystemCall.AddPath

/-!
# Proofs: the consolidation request contract of EIP-7251 does what its EIP describes

The contract keeps a queue of consolidation requests, and a fee that rises with its use.

Each operation of the EIP is a function here.

A theorem runs the code and shows that it computes that function.

The code is the 414 bytes of [EIP-7251][eip-7251-deployment], which its deployment installs.

Source: [EIP-7251][eip-7251-contract].

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
open EthLib.Base (byteAtOrZero_extract)
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

/-- The opcode scan skips PUSH data and finds only instructions supported by both meters. -/
theorem supportedCode_CODE : SupportedCode CODE = true := by
  decide +kernel

/-! ## The operations -/

/-- The four words of a request from `caller` with the input `input`, as the queue holds them.

They are the caller, then the three words of the input, read big-endian. -/
def requestWords (caller : Address) (input : ByteArray) : List U256 :=
  requestWordsOf 3 caller input

/-- The data of the log of a request: the 20 bytes of the caller, then the input. -/
def logData (caller : Address) (input : ByteArray) : ByteArray :=
  requestLog caller input

/-- The record of 116 bytes of the request at the index `index` of the queue, from `read`.

It is the source address, the public key of the source, then that of the target.

The address is the last 20 bytes of the first slot, since the code stores the caller as a word.

The two keys are the 96 bytes of the next three slots. -/
def record (read : U256 → U256) (index : U256) : ByteArray :=
  let slot := 4 + 4 * index
  (wordBytes (read slot)).extract 12 32 ++ wordBytes (read (slot + 1)) ++
    wordBytes (read (slot + 2)) ++ wordBytes (read (slot + 3))

/-- The code is not a delegation indicator: it has 414 bytes, not 23. -/
theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  simp [delegatedAddress, isValidDelegation, CODE, NatCode.size_ofNat, DELEGATION_SIZE]

/-- The contract as a request contract, with the code, the constants and the record of EIP-7251. -/
def CONSOLIDATION_REQUEST : RequestContract where
  entry := CONSOLIDATION_REQUEST_CONTRACT
  type := CONSOLIDATION_REQUEST_TYPE
  code := CODE
  maxPerBlock := MAX_CONSOLIDATION_REQUESTS_PER_BLOCK
  targetPerBlock := TARGET_CONSOLIDATION_REQUESTS_PER_BLOCK
  minFee := MIN_CONSOLIDATION_REQUEST_FEE
  feeFraction := CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION
  inputSize := 96
  record := record
  mem := by simp [SYSTEM_CONTRACTS]
  kind_eq := rfl
  size_ne_zero := by simp [CODE, NatCode.size_ofNat]
  supported := supportedCode_CODE
  delegatedAddress_eq_none := delegatedAddress_CODE

/-- What a call with the input `input` and the value `value` gets, when it adds no request.

With no input and no value, it gets the fee as a word, or reverts while the inhibitor holds.

Any input of a size other than 0 or 96 bytes reverts, and so does a value with no input.

The EIP gives only the fee for no input; these reverts come from its code. -/
def getFeeResult (read : U256 → U256) (input : ByteArray) (value : U256) : Option U256 :=
  CONSOLIDATION_REQUEST.getFeeResult read input value

/-- A call with the value `value` pays the fee: the fee is defined and at most the value. -/
def pays (read : U256 → U256) (value : U256) : Bool :=
  CONSOLIDATION_REQUEST.pays read value

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

/-- The code runs the path of a call from another address, with the constants of EIP-7251. -/
theorem feePathCode_CODE :
    FeePathCode CODE 0xd3 CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION 410 96 where
  size_le := by simp [CODE, NatCode.size_ofNat]
  byte := FeePathCode.byte_ofNat (by decide +kernel)
  push1 := by evm_code [CODE, CODE_NUMBER_eq]
  push31 := by evm_code [CODE, CODE_NUMBER_eq]
  push117 := by evm_code [CODE, CODE_NUMBER_eq]
  push132 := by evm_code [CODE, CODE_NUMBER_eq]
  push23 := by evm_code [CODE, CODE_NUMBER_eq]
  push26 := by evm_code [CODE, CODE_NUMBER_eq, CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION]
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

/-- The code starts its system call from byte 211, for at most 2 requests. -/
theorem dequeueStartCode_CODE :
    DequeueStartCode CODE 0xd3 MAX_CONSOLIDATION_REQUESTS_PER_BLOCK where
  size_le := by simp [CODE, NatCode.size_ofNat]
  dest_lt := by decide
  max_lt := by decide
  byte := DequeueStartCode.byte_ofNat (by decide +kernel)
  push1 := by evm_code [CODE, CODE_NUMBER_eq]
  push4 := by evm_code [CODE, CODE_NUMBER_eq]
  push11 := by evm_code [CODE, CODE_NUMBER_eq, MAX_CONSOLIDATION_REQUESTS_PER_BLOCK]
  push14 := by evm_code [CODE, CODE_NUMBER_eq]
  push18 := by evm_code [CODE, CODE_NUMBER_eq, MAX_CONSOLIDATION_REQUESTS_PER_BLOCK]
  dest20 := by evm_dest [CODE, CODE_NUMBER_eq]

/-- The code ends its system call from byte 297, for a target of 1 and records of 116 bytes. -/
theorem dequeueTailCode_CODE : DequeueTailCode CODE 297 1 116 where
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

/-- From byte 143, the code adds a request of 3 input words, 96 bytes long. -/
theorem addPathCode_CODE : AddPathCode CODE 3 96 where
  two_le := by decide
  log_lt := by decide
  size_le := by simp [CODE, NatCode.size_ofNat]
  head := fun i h h1 h2 h3 => by
    obtain ⟨k, rfl⟩ : ∃ k, i = 143 + k := ⟨i - 143, by omega⟩
    rw [Nat.add_sub_cancel_left]
    exact getElem_of_holdsExcept (skip := [14]) (by decide +kernel) h (by omega)
      (by simp; omega)
  push156 := by evm_code [CODE, CODE_NUMBER_eq]
  word := fun j h1 h2 i h hi h1' => by
    obtain rfl : j = 1 := by omega
    exact getElem_of_holdsExcept (skip := [1]) (by decide +kernel) h hi
      (by simpa using h1')
  pushWord := fun j h1 h2 => by
    obtain rfl : j = 1 := by omega
    evm_code [CODE, CODE_NUMBER_eq]
  last := fun i h hi h1 =>
    getElem_of_holdsExcept (skip := [1]) (by decide +kernel) h hi (by simpa using h1)
  pushLast := by evm_code [CODE, CODE_NUMBER_eq]
  log := fun i h hi h1 h2 =>
    getElem_of_holdsExcept (skip := [7, 13]) (by decide +kernel) h hi
      (by simp; omega)
  pushSize := by evm_code [CODE, CODE_NUMBER_eq]
  pushLog := by evm_code [CODE, CODE_NUMBER_eq]

/-! ## A call that adds no request -/

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- A call from another address, whose input is not 96 bytes, gets the fee or reverts.

It holds from Shapella, with the one-counter meter.

From Glamsterdam, a run with no error carries to the state gas meter of the protocol. -/
theorem spec_getFee {m : Nat} (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hsize : message.data.size ≠ 96)
    -- It assumes fewer than `2^256` bytes of input, which the size word of the EVM can hold.
    (hbound : message.data.size < 2 ^ 256)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    -- The frame has at least 100,000 gas, and 100 more for each of these steps.
    (hgas : 100000 + 100 * m ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData)
      -- The frame returns the fee as a word or reverts with no output, as the code of the EIP does.
      --
      -- Its state reads as the state it starts from.
      (Answer state (getFeeResult (storageOf state message.currentTarget) message.data
        message.value)) :=
  CONSOLIDATION_REQUEST.spec_getFee feePathCode_CODE rfl hfork hcaller hsize hbound hfits (by omega)

/-! ## A call that adds a request -/

/-- A call from another address with 96 bytes of input adds a request, as EIP-7251 describes.

It holds from Shapella, with the one-counter meter, on a frame that may change the state. -/
theorem spec_add {m : Nat} (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    -- The account of the contract exists.
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    -- The input is the public key of the source validator, then that of the target validator.
    (hsize : message.data.size = 96)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    -- The frame has at least 200,000 gas before Glamsterdam and 1,000,000 from it.
    --
    -- It has 100 more for each of these steps.
    (hgas : 200000 * storageGasScale fork + 100 * m ≤ gas) :
    -- From Glamsterdam, this one-counter frame is a model for the proof, not the meter of EIP-8037.
    --
    -- A run that reverts or stops with no error carries to a state gas meter with this gas left.
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- When the value pays the fee, the frame adds the request of the caller and the input.
      if pays (storageOf state message.currentTarget) message.value then
        -- It stores the request words at the tail of the queue, and logs the caller and the input.
        Added SLOTS_PER_REQUEST message.currentTarget (requestWords message.caller message.data)
          (logData message.caller message.data) state substate evm
      -- Otherwise it reverts with no output, and its state reads as the state it starts from.
      else Answer state none evm := by
  have hscale := one_le_storageGasScale fork
  refine CONSOLIDATION_REQUEST.spec_pay feePathCode_CODE rfl hfork hcaller hsize hfits (by omega)
    fun _ g ss hg hlogs => Spec.consequence (addPathCode_CODE.spec_add
      (S := state.recordStorageRead message.currentTarget (U256.toBeBytes 0)) hfork
      hstatic hacc hsize (by omega)) (fun _ h => h) ?_
  rintro evm ⟨⟨herr, hout, hw, hlog⟩, -⟩
  exact ⟨herr, hout, hw, by rw [hlog, hlogs]; rfl⟩

/-- The rule of a call that adds a request holds under the state gas meter of EIP-8037.

That meter is the one of every fork from Glamsterdam.

Its execution gas alone must cover `gas`, and the reservoir is not used. -/
theorem spec_add_covered {m : Nat} (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    -- The account of the contract exists.
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    -- The input is the public key of the source validator, then that of the target validator.
    (hsize : message.data.size = 96)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits MIN_CONSOLIDATION_REQUEST_FEE CONSOLIDATION_REQUEST_FEE_UPDATE_FRACTION
        (storageOf state message.currentTarget 0).toNat m)
    -- The frame has at least 200,000 gas before Glamsterdam and 1,000,000 from it.
    --
    -- It has 100 more for each of these steps.
    (hgas : 200000 * storageGasScale fork + 100 * m ≤ gas) :
    Spec (Meter := StateGasMeter) fork
      (Covered (At CODE message 0 [] .empty gas state substate returnData))
      (Covered fun evm =>
        if pays (storageOf state message.currentTarget) message.value then
          Added SLOTS_PER_REQUEST message.currentTarget (requestWords message.caller message.data)
            (logData message.caller message.data) state substate evm
        else Answer state none evm) :=
  (spec_add (returnData := returnData) hfork hcaller hstatic hacc hsize hfits hgas).covered
    (fun _ hat => hat.ready supportedCode_CODE (zero_boundary CODE)) fun _ => carried_of_added

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
    refine Holds.of_byteAtOrZero hfit fun i hi => ?_
    simp only [ByteArray.size_extract, s] at hi
    rw [hw.byteAtOrZero_eq (by rw [s]; omega), byteAtOrZero_wordBytes_shl v₀ (by omega), byteAtOrZero_extract, s,
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

/-- At most 2 runs of the loop of the system call take at most 18,030 gas. -/
private theorem deqGas_le {n : Nat} (hn : n ≤ 2) : deqGas n ≤ 18030 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with h | h | h <;> subst h <;> decide

/-- From the head of the loop at byte 233, with memory empty, the code takes the requests.

It returns their records, and holds the storage after the requests are taken. -/
private theorem deq_rest {S : TransactionState} {ss : Substate} {g : Nat} {r : U256 → U256}
    (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hr : storageOf S message.currentTarget = r) (hb : Bounded r)
    (hg : 140000 * storageGasScale fork ≤ g) :
    Spec fork (At CODE message 233 [BitVec.ofNat 256 0, BitVec.ofNat 256 (numDequeued 2 r), r 2,
        r 3] .empty g S ss returnData) fun evm =>
      evm.error = none ∧ evm.output = taken record r (numDequeued 2 r) ∧
      WritesStorage message.currentTarget (afterDequeue 2 1 r) S evm.state := by
  have hscale := one_le_storageGasScale fork
  have hc2 : numDequeued 2 r ≤ 2 := Nat.min_le_right _ _
  have hdg := deqGas_le hc2
  refine deq_loop hfork hc2 (numDequeued 2 r) (by omega) hr (holds_empty (Nat.le_refl _)) rfl
    (by omega) fun M' S' g' ss' hM' hM's hw' hg' => ?_
  have hacc' : (S'.getAccountOptional message.currentTarget).isSome = true := by
    rw [hw'.2.2.1]; exact hacc
  refine Spec.consequence (dequeueTailCode_CODE.spec_head hfork hstatic hacc' (funext hw'.1) hb
    (by decide) (by rw [hM's]; omega)
    (by omega)) (fun _ h => h) fun evm ⟨h1, h2, h3⟩ => ⟨h1, ?_, WritesStorage.trans hw' h3⟩
  rw [h2]
  have := hM'.2
  rw [size_taken size_record] at this
  exact this

/-- A call from the system address takes requests from the queue, as EIP-7251 describes.

It holds from Shapella, on a frame that may change the state. -/
theorem spec_dequeue (hfork : .shapella ≤ fork)
    (hcaller : message.caller = SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    -- The account of the contract exists.
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    -- The counters of the storage meet the bounds under which the code computes as the EIP.
    (hbounded : Bounded (storageOf state message.currentTarget))
    -- The conservative one-counter budget is 200,000 gas before Glamsterdam and 1,000,000 from it.
    (hgas : 200000 * storageGasScale fork ≤ gas) :
    -- From Glamsterdam, this one-counter frame is a model for the proof, not the meter of EIP-8037.
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      -- The frame stops with no error.
      evm.error = none ∧
      -- It returns the records, of 116 bytes each, of at most 2 requests from the head.
      evm.output = dequeued MAX_CONSOLIDATION_REQUESTS_PER_BLOCK record
        (storageOf state message.currentTarget) ∧
      -- The state holds the storage after the requests are taken and the count reset.
      --
      -- The excess is updated for a target of 1 request per block.
      --
      -- It keeps the storage of every other account, the accounts and the codes.
      WritesStorage message.currentTarget
        (afterDequeue MAX_CONSOLIDATION_REQUESTS_PER_BLOCK TARGET_CONSOLIDATION_REQUESTS_PER_BLOCK
          (storageOf state message.currentTarget))
        state evm.state := by
  exact CONSOLIDATION_REQUEST.spec_dequeue (rest := 140000) feePathCode_CODE dequeueStartCode_CODE
    (fun _ _ _ _ hacc' hr hb hg => deq_rest hfork hstatic hacc' hr hb hg) hfork hcaller hacc
    hbounded (Nat.le_trans (Nat.mul_le_mul_right _ (by decide)) hgas)

/-- The consolidation request address is not a precompile. -/
theorem addedAt_CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS :
    Precompiles.addedAt CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS.toU256.toNat = none :=
  CONSOLIDATION_REQUEST.addedAt

/-- From Shapella, the code takes the requests with 200,000 gas, scaled from Glamsterdam. -/
theorem dequeues (hfork : .shapella ≤ fork) : CONSOLIDATION_REQUEST.Dequeues fork 200000 :=
  fun _ _ _ _ hcaller hstatic hacc hread hgas =>
    spec_dequeue hfork hcaller hstatic hacc hread hgas

/-- From Pectra, the system call of a block to the contract takes its requests.

It runs with the gas meter of its fork. -/
theorem systemCall_dequeue {env : BlockEnvironment fork} {block : State.BlockState}
    {data : ByteArray} (hfork : .pectra ≤ fork)
    -- The account at the consolidation request address must hold the code of EIP-7251.
    (hcode : codeAt block CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS = .ok CODE)
    -- The counters of its storage meet the bounds under which the code computes as the EIP.
    (hbounded : Bounded (storageOf (.ofBlock block) CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS)) :
    -- The call succeeds, whatever its data, and returns the records of at most 2 requests.
    ∃ out, systemCall env block CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS data = .ok out ∧
      out.error = none ∧
      out.output = dequeued MAX_CONSOLIDATION_REQUESTS_PER_BLOCK record
        (storageOf (.ofBlock block) CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS) ∧
      -- The storage of the contract is then the storage after the requests are taken.
      --
      -- The call keeps the storage of every other account, the accounts and the codes.
      WritesStorage CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS
        (afterDequeue MAX_CONSOLIDATION_REQUESTS_PER_BLOCK TARGET_CONSOLIDATION_REQUESTS_PER_BLOCK
          (storageOf (.ofBlock block) CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS))
        (.ofBlock block) out.state :=
  CONSOLIDATION_REQUEST.systemCall_dequeue (Nat.le_trans (by decide) hfork)
    (dequeues (Nat.le_trans (by decide) hfork))
    (by have := storageGasScale_le fork; simp only [SYSTEM_TRANSACTION_GAS]; omega)
    hcode hbounded

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
      .error (.systemContractEmpty CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS) :=
  readRequests_of_empty_after
    (pre := [(WITHDRAWAL_REQUEST_TYPE, WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS)])
    (requestContracts_of_pectra hfork) (by simp [List.foldlM_cons, hwithdrawal]) hcode

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
