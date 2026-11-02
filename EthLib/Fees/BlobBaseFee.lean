module

/-!
# `Fees.BlobBaseFee`

The base fee per blob gas, the rule of [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844), with the reserve price of [EIP-7918](https://eips.ethereum.org/EIPS/eip-7918).

A blob costs `GAS_PER_BLOB` units of blob gas, a gas of its own with its own fee market.

Each block header carries the excess blob gas, a running total.

Blob gas used above the target raises it, and blob gas used below the target lowers it, never below 0.

The base fee per blob gas grows exponentially with the excess:

```text
    base_fee_per_blob_gas  ~  MIN_BASE_FEE_PER_BLOB_GAS * e^(excess_blob_gas / baseFeeUpdateFraction)
```

`fake_exponential` approximates that exponential in integers, from its Taylor series.

Each block carries the excess forward, adds what its parent used and subtracts the target.

EIP-7918 adds a reserve price.

When a blob costs less than `BLOB_BASE_COST` units of execution gas, the target is not subtracted, so once the parent's excess plus its blob gas reaches the target, the excess does not fall.

The check against the target still comes first: when the parent's excess plus its blob gas is below the target, the excess is 0.

The target, the maximum and the update fraction can change at each fork, through the blob schedule of [EIP-7892](https://eips.ethereum.org/EIPS/eip-7892).

So they are fields of `BlobSchedule`, not constants.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#header-extension), Header extension, makes the excess blob gas and the blob gas used 64-bit unsigned integers.

Its `calc_excess_blob_gas`, like that of EIP-7918, returns a Python `int`, which has no upper bound.

So here they are `Nat`s, which do not overflow.

execution-specs computes with them in `U64` instead, which raises when a result reaches 2^64, such as the parent's excess plus its blob gas.

For a parent with at most `GAS_PER_BLOB * max` blob gas, the excess grows by at most `GAS_PER_BLOB * (max - target)` per block.

In every fork of execution-specs at `2c0c8e7`, from Cancun to Bogota, `max - target` is at most 7.

So the excess grows by less than 2^20 per block, and neither it nor the parent's excess plus its blob gas reaches 2^64 within 2^44 blocks.

The executable sources are `taylor_exponential` in [`utils/numeric.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/utils/numeric.py#L177) of execution-specs at `2c0c8e7`, and the functions of its `vm/gas.py` linked below.
-/

@[expose] public section

namespace EthLib.Fees.BlobBaseFee

/-- `GAS_PER_BLOB`: the blob gas of one blob.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters), Parameters. -/
def GAS_PER_BLOB : Nat := 2 ^ 17

/-- `MIN_BASE_FEE_PER_BLOB_GAS`: the base fee per blob gas when the excess is 0.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters), Parameters. -/
def MIN_BASE_FEE_PER_BLOB_GAS : Nat := 1

/-- `BLOB_BASE_COST`: the execution gas whose price is the reserve price of a blob.

[EIP-7918](https://eips.ethereum.org/EIPS/eip-7918#parameters), Parameters. -/
def BLOB_BASE_COST : Nat := 2 ^ 13

/-- `BlobSchedule`: the blob parameters of one fork, one entry of the `blobSchedule` of [EIP-7840](https://eips.ethereum.org/EIPS/eip-7840).

[EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#blob-base-fee-computations), Blob base fee computations.

The formulas divide by `max` and by `baseFeeUpdateFraction`, and subtract `target` from `max`.

So the type asks for both divisors above 0 and for `target <= max`, which the schedule of every fork meets.

Outside these bounds execution-specs raises when a formula reaches such a division or subtraction.

For a schedule written out in numbers, `decide` proves the three bounds. -/
structure BlobSchedule where
  /-- `target`: the blobs per block that the fee aims for. -/
  target : Nat
  /-- `max`: the most blobs a block may carry. -/
  max : Nat
  /-- `baseFeeUpdateFraction`: the excess that multiplies the fee by about e. -/
  baseFeeUpdateFraction : Nat
  /-- The target is at most the maximum, so the subtraction `max - target` never truncates. -/
  target_le_max : target ≤ max := by decide
  /-- The maximum is positive, so the reserve price rule never divides by 0. -/
  max_pos : 0 < max := by decide
  /-- The update fraction is positive, so `fake_exponential` never divides by 0. -/
  baseFeeUpdateFraction_pos : 0 < baseFeeUpdateFraction := by decide
  deriving Repr, DecidableEq

/-- The loop of `fake_exponential`, from step `i`, run at most `fuel` times.

Each step adds the accumulator to the output, then turns the accumulator into the next Taylor term:

```text
    numerator_accum  <-  numerator_accum * numerator // (denominator * i)
```

The specification runs the loop while the accumulator is positive.

The accumulator can grow before it shrinks, so it cannot be the measure that decreases.

The recursion counts down `fuel` instead.

The kernel unfolds such a definition directly, so `decide +kernel` checks every known answer.

`fakeExponentialFuel` is enough steps for the accumulator to reach 0, so the loop always stops on its own first. -/
def fakeExponentialLoop (numerator denominator : Nat) : Nat → Nat → Nat → Nat → Nat
  -- Out of fuel: unreachable when the fuel is at least `fakeExponentialFuel`.
  | 0, _, _, output => output
  | fuel + 1, i, numeratorAccum, output =>
    -- `while numerator_accum > 0`
    if numeratorAccum = 0 then
      output
    else
      fakeExponentialLoop numerator denominator fuel (i + 1)
        (numeratorAccum * numerator / (denominator * i)) (output + numeratorAccum)

/-- A bound on the steps of `fake_exponential`: `2 * numerator + factor * denominator + 2 * numerator^2 + 1`.

From step `2 * numerator` on, each step at least halves the accumulator.

By then the accumulator is at most `factor * denominator * numerator^(2 * numerator)`.

That is below `2^(factor * denominator + 2 * numerator^2)`, so that many more halvings reach 0. -/
def fakeExponentialFuel (factor numerator denominator : Nat) : Nat :=
  2 * numerator + (factor * denominator + 2 * numerator * numerator) + 1

/-- `fake_exponential`: an approximation of `factor * e^(numerator / denominator)`, from the Taylor series in integers.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#helpers), Helpers, `fake_exponential`.

`taylor_exponential` in execution-specs.

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

A denominator of 0 gives 0 here, where the specification raises at the last division. -/
def fakeExponential (factor numerator denominator : Nat) : Nat :=
  fakeExponentialLoop numerator denominator (fakeExponentialFuel factor numerator denominator) 1
    (factor * denominator) 0 / denominator

/-- `get_base_fee_per_blob_gas`: the base fee per blob gas for a given excess blob gas.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#gas-accounting), Gas accounting, with the update fraction of the schedule, as in [EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#blob-base-fee-computations), Blob base fee computations.

`calculate_blob_gas_price` in [`forks/cancun/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/cancun/vm/gas.py#L434) of execution-specs at `2c0c8e7`.

Every later fork at that commit has the same function, with its own update fraction. -/
def getBaseFeePerBlobGas (schedule : BlobSchedule) (excessBlobGas : Nat) : Nat :=
  fakeExponential MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas schedule.baseFeeUpdateFraction

namespace Cancun

/-- `calc_excess_blob_gas` before EIP-7918: the parent's excess plus its blob gas, minus the target, at least 0.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#header-extension), Header extension, with the target of the schedule, as in [EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#blob-base-fee-computations), Blob base fee computations.

`calculate_excess_blob_gas` in [`forks/cancun/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/cancun/vm/gas.py#L381) of execution-specs at `2c0c8e7`.

Prague computes it the same way, with its own target.

For a parent without the blob gas fields, as before Cancun, both count as 0. -/
def calcExcessBlobGas (schedule : BlobSchedule) (parentExcessBlobGas parentBlobGasUsed : Nat) : Nat :=
  let targetBlobGas := GAS_PER_BLOB * schedule.target
  if parentExcessBlobGas + parentBlobGasUsed < targetBlobGas then
    0
  else
    parentExcessBlobGas + parentBlobGasUsed - targetBlobGas

end Cancun

namespace Osaka

/-- `calc_excess_blob_gas` since EIP-7918: the same, except below the reserve price.

[EIP-7918](https://eips.ethereum.org/EIPS/eip-7918#functions), Functions.

`calculate_excess_blob_gas` in [`forks/osaka/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/osaka/vm/gas.py#L398) of execution-specs at `2c0c8e7`.

Every later fork at that commit has the same function, BPO2 included.

The reserve price of a blob is the price of `BLOB_BASE_COST` units of execution gas, at the parent's base fee per gas.

When one blob, at the parent's base fee per blob gas, costs less than that, the target is not subtracted.

Instead the excess grows by the parent's blob gas times `max - target`, divided by `max`, rounded down.

The parent's base fee per blob gas is computed with this block's schedule, as EIP-7918 requires in the first block after a fork.

The check against the target comes first.

So when the parent's excess plus its blob gas is below this block's target, the excess is 0 whatever the prices.

For a parent without the blob gas fields, all three count as 0. -/
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

end EthLib.Fees.BlobBaseFee
