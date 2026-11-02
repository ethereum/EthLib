module

/-!
# `Fees.BaseFee`

The base fee per gas of a block, the rule of [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559).

A transaction pays the base fee for every unit of gas it uses, and the base fee is burned.

Each block sets its base fee from its parent's, so the fee follows demand for gas.

The parent's gas target is half its gas limit, rounded down.

A parent that used more gas than its target raises the fee, and one that used less never raises it.

The fee moves by one eighth of the scaled distance `base_fee * |used - target| // target`, and rises by at least 1 above the target:

```text
    target = parent_gas_limit // 2

    used = target:   base_fee
    used > target:   base_fee + max(base_fee * (used - target) // target // 8, 1)
    used < target:   base_fee - base_fee * (target - used) // target // 8
```

So a fall is at most `base_fee // 8`.

A rise is at most `max(base_fee // 8, 1)` if the parent used at most twice its target.

An odd gas limit lets the parent use one more unit of gas than twice its target.

The rise can then exceed `max(base_fee // 8, 1)`, and is at most `max((base_fee + base_fee // target) // 8, 1)`.

The executable source is `calculate_base_fee_per_gas`, in [`forks/london/fork.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/london/fork.py#L226) of execution-specs at `2c0c8e7`.

Every later fork at that commit has the same function, BPO2 included.

`ELASTICITY_MULTIPLIER`, `BASE_FEE_MAX_CHANGE_DENOMINATOR` and `check_gas_limit` are the same there too.

Two validity rules of execution-specs are not here.

`calculate_base_fee_per_gas` checks the new block's gas limit with `check_gas_limit`, before its three branches.

`validate_header` rejects a block that used more gas than its gas limit.

The first London block has no parent with a base fee, and takes `INITIAL_BASE_FEE` instead.

That case is not here either.
-/

@[expose] public section

namespace EthLib.Fees.BaseFee

/-- `ELASTICITY_MULTIPLIER`: the gas limit of a block over its gas target.

EIP-1559, Specification.

The target is the gas limit over this, rounded down.

So an odd gas limit lets a block use `2 * target + 1`. -/
def ELASTICITY_MULTIPLIER : Nat := 2

/-- `BASE_FEE_MAX_CHANGE_DENOMINATOR`: the base fee moves by one eighth of the scaled distance.

EIP-1559, Specification.

For a parent between empty and twice its target, a change is then at most the larger of one eighth of the fee and 1. -/
def BASE_FEE_MAX_CHANGE_DENOMINATOR : Nat := 8

/-- `calculate_base_fee_per_gas`: the base fee per gas of a block, from its parent's gas limit, gas used and base fee.

EIP-1559, Specification, the base fee check in `validate_block`.

The `max` with 1 raises the fee by at least 1 above the target, even when one eighth of the scaled distance rounds down to 0.

In execution-specs, the function also takes the new block's gas limit, `block_gas_limit`, and only passes it to `check_gas_limit`.

That check runs before the three branches.

It accepts a gas limit only if it is less than `parent_gas_limit // 1024` away from the parent's, and at least 5000.

It accepts no gas limit when the parent's is below 4997.

So a target of 0 never reaches the division by the target there.

Here a target of 0 and `x / 0 = 0` make a parent above it give `base_fee + 1`. -/
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

end EthLib.Fees.BaseFee
