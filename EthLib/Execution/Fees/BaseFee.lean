module

/-!
# `Fees.BaseFee`

The base fee per gas of a block, the rule of [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559).

A transaction pays the base fee for every unit of gas it uses, and the base fee is burned.

Each block sets its base fee from its parent's, so the fee follows demand for gas.

The parent's gas target is half its gas limit, rounded down.

A parent that used more gas than its target raises the fee, and one that used less never raises it.

The fee moves by one eighth of the scaled distance `base_fee * |used - target| // target`.

Above the target, it rises by at least 1:

```text
    target = parent_gas_limit // 2

    used = target:  base_fee
    used > target:  base_fee + max(base_fee * (used - target) // target // 8, 1)
    used < target:  base_fee - base_fee * (target - used) // target // 8
```

So a fall is at most `base_fee // 8`.

A rise is at most `max(base_fee // 8, 1)` if the parent used at most twice its target.

An odd gas limit lets the parent use one more unit of gas than twice its target.

The rise can then exceed `max(base_fee // 8, 1)`.

It is at most `max((base_fee + base_fee // target) // 8, 1)`.

Every fork after London keeps this rule and its two constants.

Two validity rules of EIP-1559 are not here.

The gas limit of the new block must be close to the parent's, and at least 5000.

A block must not use more gas than its gas limit.

The first London block has no parent with a base fee, and takes an initial base fee instead.

That case is not here either.
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

For a parent between empty and twice its target, a change is then at most `max(fee // 8, 1)`. -/
def BASE_FEE_MAX_CHANGE_DENOMINATOR : Nat := 8

/-- The base fee per gas of a block, from the gas limit, gas used and base fee of its parent.

Source: the base fee check in `validate_block` of [EIP-1559][eip-1559].

The `max` with 1 raises the fee by at least 1 above the target.

It does so even when one eighth of the scaled distance rounds down to 0.

The same function of EIP-1559 also checks the gas limit of the new block first.

It accepts a gas limit only if it is less than `parent_gas_limit // 1024` away from the parent's.

It also requires a gas limit of at least 5000.

So it accepts no gas limit when the parent's is below 4997.

A target of 0 then never reaches the division.

Here a target of 0 and `x / 0 = 0` make a parent above it give `base_fee + 1`.

[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
-/
def calculateBaseFeePerGas (parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) : Nat :=
  let parentGasTarget := parentGasLimit / ELASTICITY_MULTIPLIER
  if parentGasUsed = parentGasTarget then
    parentBaseFeePerGas
  else if parentGasUsed > parentGasTarget then
    let gasUsedDelta := parentGasUsed - parentGasTarget
    let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
    let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
    let baseFeePerGasDelta := max (targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1
    parentBaseFeePerGas + baseFeePerGasDelta
  else
    let gasUsedDelta := parentGasTarget - parentGasUsed
    let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
    let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
    let baseFeePerGasDelta := targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR
    -- The fall is at most `parentBaseFeePerGas / 8`, so this subtraction never truncates.
    parentBaseFeePerGas - baseFeePerGasDelta

end EthLib.Execution.Fees.BaseFee
