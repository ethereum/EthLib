module

public import EthLib.Base.ChainConfig

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

open EthLib.Base

/-- The blob gas of one blob.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters). -/
def GAS_PER_BLOB : Nat := 2 ^ 17

/-- The fee at an excess of 0.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters). -/
def MIN_BASE_FEE_PER_BLOB_GAS : Nat := 1

/-- The execution gas that prices the reserve.

Source: [EIP-7918](https://eips.ethereum.org/EIPS/eip-7918#parameters). -/
def BLOB_BASE_COST : Nat := 2 ^ 13

-- The blob parameters are chain configuration, so their type lives in `Base`.
export EthLib.Base (BlobSchedule)

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

/-- The mainnet blob schedule of a fork, from Dencun on.

- Dencun: target 3, max 6, update fraction 3338477, from [EIP-4844][eip-4844].
- Pectra: target 6, max 9, update fraction 5007716, from [EIP-7691][eip-7691].
- BPO1: target 10, max 15, update fraction 8346193, from [EIP-8134][eip-8134].
- BPO2: target 14, max 21, update fraction 11684671, from [EIP-8135][eip-8135].

Fusaka keeps the values of Pectra, and the forks after BPO2 keep those of BPO2.

No EIP gives BPO3, BPO4 or BPO5 other values yet.

[EIP-7892][eip-7892] makes the schedule chain configuration, so a chain can set others.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#parameters
[eip-7691]: https://eips.ethereum.org/EIPS/eip-7691#parameters
[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration
[eip-8134]: https://eips.ethereum.org/EIPS/eip-8134#bpo1-parameters
[eip-8135]: https://eips.ethereum.org/EIPS/eip-8135#bpo2-parameters -/
def blobSchedule (fork : Fork) : Since .dencun fork BlobSchedule := fun _ =>
  if fork ≥ .bpo2 then { target := 14, max := 21, baseFeeUpdateFraction := 11684671 }
  else if fork ≥ .bpo1 then { target := 10, max := 15, baseFeeUpdateFraction := 8346193 }
  else if fork ≥ .pectra then { target := 6, max := 9, baseFeeUpdateFraction := 5007716 }
  else { target := 3, max := 6, baseFeeUpdateFraction := 3338477 }

/-- The blob schedule of a block at `fork` on a chain, from Dencun on.

It is the last blob schedule that the chain sets itself and that the block has reached.

Without one, it is the schedule of the fork.

The header check reads it for the excess blob gas.

The blob gas limit of a block and the price of its blob gas still read the fork's schedule.

[EIP-7892][eip-7892] links each schedule of the configuration to an activation.

[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration -/
def chainBlobSchedule (config : ChainConfig) (fork : Fork) (number timestamp : Nat) :
    Since .dencun fork BlobSchedule := fun h =>
  (config.blobScheduleAt number timestamp).getD (blobSchedule fork h)

/-- The excess blob gas of a block at `fork`, from its parent's excess, blob gas and base fee.

Before Fusaka, it is the parent's excess plus its blob gas, minus the target, and at least 0.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#header-extension).

From Fusaka, [EIP-7918](https://eips.ethereum.org/EIPS/eip-7918#functions) adds a reserve price.

- Below it, a blob costs less than `2^13` units of execution gas.
- The excess then grows by `parentBlobGasUsed * (max - target) // max`.
- Below the target, the excess is 0 whatever the prices.
- The parent's blob base fee uses this block's schedule.

A parent without the blob gas fields counts all three as 0. -/
def calcExcessBlobGas (fork : Fork) (schedule : BlobSchedule)
    (parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat) : Nat :=
  let targetBlobGas := GAS_PER_BLOB * schedule.target
  if parentExcessBlobGas + parentBlobGasUsed < targetBlobGas then
    0
  else if fork ≥ .fusaka ∧ BLOB_BASE_COST * parentBaseFeePerGas >
      GAS_PER_BLOB * getBaseFeePerBlobGas schedule parentExcessBlobGas then
    parentExcessBlobGas + parentBlobGasUsed * (schedule.max - schedule.target) / schedule.max
  else
    parentExcessBlobGas + parentBlobGasUsed - targetBlobGas

end EthLib.Execution.Fees.BlobBaseFee
