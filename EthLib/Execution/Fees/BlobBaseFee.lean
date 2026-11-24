module

public import EthLib.Base.ChainConfig

/-!
# `Fees.BlobBaseFee`

The base fee per blob gas of EIP-4844, with the reserve price of EIP-7918.

Sources: <https://eips.ethereum.org/EIPS/eip-4844> and <https://eips.ethereum.org/EIPS/eip-7918>.

Blobs pay in blob gas, which has a fee market of its own.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

open EthLib.Base

/-- The fee at an excess of 0.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters). -/
def MIN_BASE_FEE_PER_BLOB_GAS : Nat := 1

/-- The execution gas that prices the reserve.

Source: [EIP-7918](https://eips.ethereum.org/EIPS/eip-7918#parameters). -/
def BLOB_BASE_COST : Nat := 2 ^ 13

-- The blob parameters are chain configuration, so they live in `Base` with the gas of a blob.
export EthLib.Base (BlobSchedule GAS_PER_BLOB)

/-- The loop of the exponential of EIP-4844, from step `i`, run at most `fuel` times.

The accumulator can grow before it shrinks, so the recursion counts down `fuel`.

With the fuel below, the loop always stops on its own first. -/
def fakeExponentialLoop (numerator denominator : Nat) : Nat → Nat → Nat → Nat → Nat
  -- Out of fuel: unreachable with the fuel below.
  | 0, _, _, output => output
  | fuel + 1, i, numeratorAccum, output =>
    -- The sum stops at the first term `a_i = 0`.
    if numeratorAccum = 0 then
      output
    else
      -- The call carries the three updates of the loop body, from the old `i` and accumulator.
      --
      -- The next step is `i + 1`.
      fakeExponentialLoop numerator denominator fuel (i + 1)
        -- `a_(i+1) = floor(a_i * n / (d * i))`, for the numerator `n` and the denominator `d`.
        (numeratorAccum * numerator / (denominator * i))
        -- The sum gains `a_i`, the term before the update.
        (output + numeratorAccum)

/-- Enough steps for the loop of the exponential to stop.

- From step `2 * numerator` on, each step at least halves the accumulator.
- By then the accumulator is below `2^(factor * denominator + 2 * numerator^2)`.
- So that many more steps reach 0. -/
def fakeExponentialFuel (factor numerator denominator : Nat) : Nat :=
  2 * numerator + (factor * denominator + 2 * numerator * numerator) + 1

/-- `factor * e^(numerator / denominator)`, from the Taylor series in integers.

Source: the fake exponential of [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#helpers).

A denominator of 0 gives 0, where the EIP divides by 0. -/
def fakeExponential (factor numerator denominator : Nat) : Nat :=
  -- The loop runs with enough fuel to stop on a zero term, as the loop of the EIP does.
  fakeExponentialLoop numerator denominator (fakeExponentialFuel factor numerator denominator)
    -- The first step is `i = 1`.
    1
    -- `a_1 = factor * d`.
    (factor * denominator)
    -- The sum starts at 0.
    0
    -- The result is the sum divided by `d`, rounded down.
    / denominator

/-- The base fee per blob gas at a given excess.

It grows exponentially with the excess, as the Rationale of EIP-4844 says.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#gas-accounting), Gas accounting. -/
def getBaseFeePerBlobGas (schedule : BlobSchedule) (excessBlobGas : Nat) : Nat :=
  -- It approximates `MIN_BASE_FEE_PER_BLOB_GAS * e^(x / F)` in integers.
  --
  -- Here `x` is the excess, and `F` the update fraction.
  --
  -- The EIP's `BLOB_BASE_FEE_UPDATE_FRACTION` is the update fraction of the schedule.
  --
  -- EIP-7691 and the BPO forks change that fraction, and EIP-7892 makes it configuration.
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
  -- From BPO2 on, the values of EIP-8135.
  if fork ≥ .bpo2 then { target := 14, max := 21, baseFeeUpdateFraction := 11684671 }
  -- From BPO1, the values of EIP-8134.
  else if fork ≥ .bpo1 then { target := 10, max := 15, baseFeeUpdateFraction := 8346193 }
  -- From Pectra, through Fusaka, the values of EIP-7691.
  else if fork ≥ .pectra then { target := 6, max := 9, baseFeeUpdateFraction := 5007716 }
  -- At Dencun, the values of EIP-4844.
  else { target := 3, max := 6, baseFeeUpdateFraction := 3338477 }

/-- The blob schedule of a block at `fork` on a chain, from Dencun on.

The header check reads it for the excess blob gas.

The block environment holds it, for the blob gas limit, the blob gas price and BLOBBASEFEE.

[EIP-7892][eip-7892] links each schedule of the configuration to an activation.

[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration -/
def chainBlobSchedule (config : ChainConfig) (fork : Fork) (number timestamp : Nat) :
    Since .dencun fork BlobSchedule := fun h =>
  -- The schedule is the last one that the chain sets itself and that the block has reached.
  --
  -- Without one, it is the schedule of the fork.
  (config.blobScheduleAt number timestamp).getD (blobSchedule fork h)

/-- The excess blob gas of a block at `fork`, from its parent's excess, blob gas and base fee.

Each header carries it: the blob gas used above the target so far.

The steps are those of the excess blob gas of [EIP-7918][eip-7918], at every fork from Dencun.

Before Fusaka, the reserve price branch is skipped, as in [EIP-4844][eip-4844].

A parent without the blob gas fields counts all three as 0.

EthLib computes these steps in naturals, where a 64-bit computation fails on an overflow.

The header extension of EIP-4844 stores the excess in 64 bits.

The header check compares the result with the 64-bit excess of the header.

So a result of `2^64` or more makes the header invalid, as that failure would.

A block that is built or simulated takes the result only below `2^64`, and fails otherwise.

With the blob schedules of the forks so far, the excess grows by less than 2^20 per block.

So it cannot reach 2^64 within 2^44 blocks.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#header-extension
[eip-7918]: https://eips.ethereum.org/EIPS/eip-7918#functions -/
def calcExcessBlobGas (fork : Fork) (schedule : BlobSchedule)
    (parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat) : Nat :=
  -- The schedule is the one of this block, as EIP-7918 asks, at every step.
  --
  -- The target blob gas `T = GAS_PER_BLOB * target`, below `2^64` by the schedule's bound.
  let targetBlobGas := GAS_PER_BLOB * schedule.target.toNat
  -- With the parent's excess `e` and blob gas used `u`, the excess is 0 when `e + u < T`.
  --
  -- The sum `e + u` can pass `2^64` while the result stays below.
  --
  -- SOUNDNESS.md records it.
  --
  -- No chain with the schedules of the EIPs reaches it.
  if parentExcessBlobGas + parentBlobGasUsed < targetBlobGas then
    0
  -- From Fusaka, the reserve price of EIP-7918 binds when `BLOB_BASE_COST * f > GAS_PER_BLOB * b`.
  --
  -- Here `f` is the base fee of the parent, and `b` its base fee per blob gas.
  --
  -- That base fee per blob gas reads the parent's excess with this block's fraction.
  else if fork ≥ .fusaka ∧ BLOB_BASE_COST * parentBaseFeePerGas >
      GAS_PER_BLOB * getBaseFeePerBlobGas schedule parentExcessBlobGas then
    -- The excess is then `e + floor(u * (max - target) / max)`.
    --
    -- Here `max` and `target` are those of the blob schedule.
    --
    -- The schedule has `target ≤ max`, so `max - target` never truncates.
    --
    -- The product `u * (max - target)` can pass `2^64` while the result stays below.
    --
    -- SOUNDNESS.md records it.
    --
    -- No chain with the schedules of the EIPs reaches it.
    parentExcessBlobGas +
      parentBlobGasUsed * (schedule.max.toNat - schedule.target.toNat) / schedule.max.toNat
  else
    -- Otherwise the excess is `e + u - T`.
    parentExcessBlobGas + parentBlobGasUsed - targetBlobGas

end EthLib.Execution.Fees.BlobBaseFee
