module

/-!
# `Fees.BaseFee`

The base fee per gas of a block, the rule of [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559).

A transaction pays the base fee for every unit of gas it uses, and the base fee is burned.

Each block sets its base fee from its parent's, so the fee follows demand for gas.

Each step of the base fee check of the EIP is stated on the line that computes it.

Every fork after London keeps this rule and its two constants.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BaseFee

/-- The gas limit of a block over its gas target.

[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification), Specification.

The target is the gas limit over this, rounded down.

So an odd gas limit lets a block use `2 * target + 1`. -/
def ELASTICITY_MULTIPLIER : Nat := 2

/-- The base fee moves by one eighth of the scaled distance.

[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification), Specification.

For a parent between empty and twice its target, a change is at most `max(floor(f / 8), 1)`.

Here `f` is the parent's base fee. -/
def BASE_FEE_MAX_CHANGE_DENOMINATOR : Nat := 8

/-- The base fee per gas of a block, from the gas limit, gas used and base fee of its parent.

Source: the base fee check of the block validation in [EIP-1559][eip-1559].

Two validity rules of the EIP are not here:

- The gas limit of the new block must be close to the parent's, and at least 5000.
- A block must not use more gas than its gas limit.

The first London block has no parent with a base fee, and takes an initial base fee instead.

That case is not here either.

[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
-/
def calculateBaseFeePerGas (parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) : Nat :=
  -- The gas target of the parent, `t = floor(l / ELASTICITY_MULTIPLIER)` for its gas limit `l`.
  --
  -- The EIP checks the gas limit of the new block before the base fee.
  --
  -- That check accepts no gas limit when the parent's is below 4997.
  --
  -- So in the EIP, a target of 0 never reaches the divisions below.
  --
  -- Here a target of 0 and `x / 0 = 0` make a parent above it give its base fee plus 1.
  let parentGasTarget := parentGasLimit / ELASTICITY_MULTIPLIER
  -- With the parent's gas used `u` and base fee `f`, the base fee is `f` when `u = t`.
  --
  -- The fork block branch before it, for the first London block, is not here.
  if parentGasUsed = parentGasTarget then
    parentBaseFeePerGas
  -- When `u > t`, the base fee rises.
  else if parentGasUsed > parentGasTarget then
    -- The excess `u - t`.
    let gasUsedDelta := parentGasUsed - parentGasTarget
    -- The rise is `max(floor(floor(f * (u - t) / t) / 8), 1)`, in three steps.
    --
    -- The first is `f * (u - t)`.
    let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
    -- Then its quotient by `t`, rounded down.
    let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
    -- Then its quotient by `BASE_FEE_MAX_CHANGE_DENOMINATOR = 8`, at least 1.
    --
    -- The bound raises the fee by at least 1, even when one eighth rounds down to 0.
    --
    -- A rise is at most `max(floor(f / 8), 1)` if the parent used at most twice its target.
    --
    -- An odd gas limit lets the parent use one more unit of gas than twice its target.
    --
    -- The rise can then exceed `max(floor(f / 8), 1)`.
    --
    -- It is at most `max(floor((f + floor(f / t)) / 8), 1)`.
    let baseFeePerGasDelta := max (targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1
    -- The base fee is `f` plus the rise.
    parentBaseFeePerGas + baseFeePerGasDelta
  -- When `u < t`, the base fee falls.
  else
    -- The shortfall `t - u`.
    let gasUsedDelta := parentGasTarget - parentGasUsed
    -- The fall is `floor(floor(f * (t - u) / t) / 8)`, in three steps.
    --
    -- The first is `f * (t - u)`.
    let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
    -- Then its quotient by `t`, rounded down.
    let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
    -- Then its quotient by `BASE_FEE_MAX_CHANGE_DENOMINATOR = 8`, rounded down.
    let baseFeePerGasDelta := targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR
    -- The base fee is `f` minus the fall.
    --
    -- The fall is at most `floor(f / 8)`, for the parent's base fee `f`.
    --
    -- So this subtraction never truncates.
    parentBaseFeePerGas - baseFeePerGasDelta

end EthLib.Execution.Fees.BaseFee
