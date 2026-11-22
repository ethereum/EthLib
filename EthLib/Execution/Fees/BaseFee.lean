module

/-!
# `Fees.BaseFee`

The base fee per gas of a block, the rule of [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559).

A transaction pays the base fee for every unit of gas it uses, and the base fee is burned.

Each block sets its base fee from its parent's, so the fee follows demand for gas.

Each line of the base fee check of the EIP is marked on the line that computes it.

A fall is at most `base_fee // 8`.

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

[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
-/
def calculateBaseFeePerGas (parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) : Nat :=
  -- `parent_gas_target = self.parent(block).gas_limit // ELASTICITY_MULTIPLIER`.
  --
  -- The EIP checks the gas limit of the new block before the base fee.
  --
  -- That check accepts no gas limit when the parent's is below 4997.
  --
  -- So in the EIP, a target of 0 never reaches the divisions below.
  --
  -- Here a target of 0 and `x / 0 = 0` make a parent above it give `base_fee + 1`.
  let parentGasTarget := parentGasLimit / ELASTICITY_MULTIPLIER
  -- `elif parent_gas_used == parent_gas_target:`
  --
  -- `expected_base_fee_per_gas = parent_base_fee_per_gas`.
  --
  -- The fork block branch before it is not here, as the header says.
  if parentGasUsed = parentGasTarget then
    parentBaseFeePerGas
  -- `elif parent_gas_used > parent_gas_target:`
  else if parentGasUsed > parentGasTarget then
    -- `gas_used_delta = parent_gas_used - parent_gas_target`.
    let gasUsedDelta := parentGasUsed - parentGasTarget
    -- `base_fee_per_gas_delta = max(... // BASE_FEE_MAX_CHANGE_DENOMINATOR, 1)`, in three steps.
    --
    -- The first is `parent_base_fee_per_gas * gas_used_delta`.
    let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
    -- Then `// parent_gas_target`.
    let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
    -- Then `max(... // BASE_FEE_MAX_CHANGE_DENOMINATOR, 1)`.
    --
    -- The `max` raises the fee by at least 1, even when one eighth rounds down to 0.
    let baseFeePerGasDelta := max (targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1
    -- `expected_base_fee_per_gas = parent_base_fee_per_gas + base_fee_per_gas_delta`.
    parentBaseFeePerGas + baseFeePerGasDelta
  -- `else:`
  else
    -- `gas_used_delta = parent_gas_target - parent_gas_used`.
    let gasUsedDelta := parentGasTarget - parentGasUsed
    -- `base_fee_per_gas_delta = ... // BASE_FEE_MAX_CHANGE_DENOMINATOR`, in three steps.
    --
    -- The first is `parent_base_fee_per_gas * gas_used_delta`.
    let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
    -- Then `// parent_gas_target`.
    let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
    -- Then `// BASE_FEE_MAX_CHANGE_DENOMINATOR`.
    let baseFeePerGasDelta := targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR
    -- `expected_base_fee_per_gas = parent_base_fee_per_gas - base_fee_per_gas_delta`.
    --
    -- The fall is at most `parent_base_fee_per_gas // 8`, so this subtraction never truncates.
    parentBaseFeePerGas - baseFeePerGasDelta

end EthLib.Execution.Fees.BaseFee
