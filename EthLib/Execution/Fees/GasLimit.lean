module

public import EthLib.Base.Fork
public import EthLib.Execution.Fees.BaseFee

/-!
# `Fees.GasLimit`

The rule that bounds the gas limit of a block by the gas limit of its parent.

The gas limit moves by less than a 1024th of the parent's gas limit, and it is at least 5000.

So a producer can raise or lower it only slowly, block after block.

At the first London block, the rule reads the parent's gas limit times the elasticity multiplier.

So the gas target after London can match the gas limit before it.

Section 4.4.4 of the Yellow Paper, Shanghai version, states the rule: [`Paper.tex`][yp].

[EIP-1559][eip-1559] doubles the parent's gas limit at the fork block in the same way.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
-/

@[expose] public section

namespace EthLib.Execution.Fees.GasLimit

/-- The gas limit moves by less than the parent's gas limit over this. -/
def LIMIT_ADJUSTMENT_FACTOR : Nat := 1024

/-- The smallest gas limit of a block. -/
def LIMIT_MINIMUM : Nat := 5000

/-- Whether a gas limit may follow the gas limit of the parent.

The subtraction never stops at 0, since a 1024th of a gas limit is at most the gas limit. -/
def checkGasLimit (gasLimit parentGasLimit : Nat) : Bool :=
  let maxAdjustmentDelta := parentGasLimit / LIMIT_ADJUSTMENT_FACTOR
  decide (gasLimit < parentGasLimit + maxAdjustmentDelta) &&
    decide (parentGasLimit - maxAdjustmentDelta < gasLimit) &&
    decide (LIMIT_MINIMUM ≤ gasLimit)

open EthLib.Base in
/-- The gas limit that the rule reads, for a parent at `parentFork` and a child at `fork`.

At the first London block, the parent is before London, and its gas limit is doubled.

Elsewhere it is the parent's gas limit. -/
def parentGasLimitForCheck (parentFork fork : Fork) (parentGasLimit : Nat) : Nat :=
  if parentFork < .london ∧ .london ≤ fork then
    parentGasLimit * BaseFee.ELASTICITY_MULTIPLIER
  else
    parentGasLimit

open EthLib.Base in
/-- Whether a gas limit at `fork` may follow the gas limit of a parent at `parentFork`.

The header checks from Paris on have a parent from London on, so they use the plain rule. -/
def checkGasLimitAcross (parentFork fork : Fork) (gasLimit parentGasLimit : Nat) : Bool :=
  checkGasLimit gasLimit (parentGasLimitForCheck parentFork fork parentGasLimit)

end EthLib.Execution.Fees.GasLimit
