module

/-!
# `Fees.GasLimit`

The rule that bounds the gas limit of a block by the gas limit of its parent.

The gas limit moves by less than a 1024th of the parent's gas limit, and it is at least 5000.

So a producer can raise or lower it only slowly, block after block.

At the first London block, the Yellow Paper doubles the parent's gas limit before the rule.

That case is not here, and the rule holds as written from the next block on.

Section 4.4.4 of the Yellow Paper, Shanghai version, states it: [`Paper.tex`][yp].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
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

end EthLib.Execution.Fees.GasLimit
