module

/-!
# `Fees.BlobBaseFee`

The base fee per blob gas of EIP-4844, with the reserve price of EIP-7918.

Sources: <https://eips.ethereum.org/EIPS/eip-4844> and <https://eips.ethereum.org/EIPS/eip-7918>.

Blobs pay in blob gas, which has a fee market of its own.

Each header carries the excess blob gas: the blob gas used above the target so far.

The fee grows exponentially with the excess:

```text
    base_fee_per_blob_gas ~ MIN_BASE_FEE_PER_BLOB_GAS * e^(excess_blob_gas / baseFeeUpdateFraction)
```

The excess is a `Nat` here, and the header extension of EIP-4844 stores it in 64 bits.

With the blob schedules of the forks so far, it grows by less than 2^20 per block.

So it cannot reach 2^64 within 2^44 blocks.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

/-- The blob gas of one blob.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters). -/
def GAS_PER_BLOB : Nat := 2 ^ 17

/-- The fee at an excess of 0.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters). -/
def MIN_BASE_FEE_PER_BLOB_GAS : Nat := 1

/-- The execution gas that prices the reserve.

Source: [EIP-7918](https://eips.ethereum.org/EIPS/eip-7918#parameters). -/
def BLOB_BASE_COST : Nat := 2 ^ 13

/-- The blob parameters of one fork.

Source: [EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#blob-base-fee-computations).

The bounds exclude the schedules that would divide by 0 or subtract below 0.

For a schedule written in numbers, `decide` proves them. -/
structure BlobSchedule where
  /-- The blobs per block that the fee aims for. -/
  target : Nat
  /-- The most blobs a block may carry. -/
  max : Nat
  /-- The excess that multiplies the fee by about e. -/
  baseFeeUpdateFraction : Nat
  /-- The target is at most the maximum, so the subtraction `max - target` never truncates. -/
  target_le_max : target ≤ max := by decide
  /-- The maximum is positive, so the reserve price rule never divides by 0. -/
  max_pos : 0 < max := by decide
  /-- The update fraction is positive, so the exponential never divides by 0. -/
  baseFeeUpdateFraction_pos : 0 < baseFeeUpdateFraction := by decide
  deriving Repr, DecidableEq

/-- The loop of the exponential of EIP-4844, from step `i`, run at most `fuel` times.

The accumulator can grow before it shrinks, so the recursion counts down `fuel`.

With the fuel below, the loop always stops on its own first. -/
def fakeExponentialLoop (numerator denominator : Nat) : Nat → Nat → Nat → Nat → Nat
  -- Out of fuel: unreachable with the fuel below.
  | 0, _, _, output => output
  | fuel + 1, i, numeratorAccum, output =>
    -- `while numerator_accum > 0`
    if numeratorAccum = 0 then
      output
    else
      fakeExponentialLoop numerator denominator fuel (i + 1)
        (numeratorAccum * numerator / (denominator * i)) (output + numeratorAccum)

/-- Enough steps for the loop of the exponential to stop.

- From step `2 * numerator` on, each step at least halves the accumulator.
- By then the accumulator is below `2^(factor * denominator + 2 * numerator^2)`.
- So that many more steps reach 0. -/
def fakeExponentialFuel (factor numerator denominator : Nat) : Nat :=
  2 * numerator + (factor * denominator + 2 * numerator * numerator) + 1

/-- `factor * e^(numerator / denominator)`, from the Taylor series in integers.

Source: `fake_exponential` in [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#helpers), Helpers.

```text
    i = 1
    output = 0
    numerator_accum = factor * denominator
    while numerator_accum > 0:
        output += numerator_accum
        numerator_accum = (numerator_accum * numerator) // (denominator * i)
        i += 1
    return output // denominator
```

A denominator of 0 gives 0, where the EIP divides by 0. -/
def fakeExponential (factor numerator denominator : Nat) : Nat :=
  fakeExponentialLoop numerator denominator (fakeExponentialFuel factor numerator denominator) 1
    (factor * denominator) 0 / denominator

/-- The base fee per blob gas at a given excess.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#gas-accounting), Gas accounting. -/
def getBaseFeePerBlobGas (schedule : BlobSchedule) (excessBlobGas : Nat) : Nat :=
  fakeExponential MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas schedule.baseFeeUpdateFraction

namespace Cancun

/-- The excess blob gas of Cancun and Prague.

It is the excess of the parent plus its blob gas, minus the target, and at least 0.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#header-extension), Header extension.

A parent without the blob gas fields counts both as 0. -/
def calcExcessBlobGas (schedule : BlobSchedule) (parentExcessBlobGas parentBlobGasUsed : Nat) : Nat :=
  let targetBlobGas := GAS_PER_BLOB * schedule.target
  if parentExcessBlobGas + parentBlobGasUsed < targetBlobGas then
    0
  else
    parentExcessBlobGas + parentBlobGasUsed - targetBlobGas

end Cancun

namespace Osaka

/-- The excess blob gas since Osaka: below the reserve price, the target is not subtracted.

Source: [EIP-7918](https://eips.ethereum.org/EIPS/eip-7918#functions), Functions.

- Below the reserve price, a blob costs less than `2^13` units of execution gas.
- The excess then grows by `parentBlobGasUsed * (max - target) // max`.
- Below the target, the excess is 0 whatever the prices.
- The parent's blob base fee uses this block's schedule.

A parent without the blob gas fields counts all three as 0. -/
def calcExcessBlobGas (schedule : BlobSchedule) (parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat) :
    Nat :=
  let targetBlobGas := GAS_PER_BLOB * schedule.target
  if parentExcessBlobGas + parentBlobGasUsed < targetBlobGas then
    0
  else if BLOB_BASE_COST * parentBaseFeePerGas > GAS_PER_BLOB * getBaseFeePerBlobGas schedule parentExcessBlobGas then
    parentExcessBlobGas + parentBlobGasUsed * (schedule.max - schedule.target) / schedule.max
  else
    parentExcessBlobGas + parentBlobGasUsed - targetBlobGas

end Osaka

end EthLib.Execution.Fees.BlobBaseFee
