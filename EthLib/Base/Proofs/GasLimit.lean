module

public import EthLib.Base.GasLimit

/-!
# Proofs: the gas limit toward a target

The gas limit toward a target stays within one step of the parent's limit.

A target within that step is the gas limit itself.
-/

@[expose] public section

namespace EthLib.Base

/-- The gas limit toward a target is within one step of the parent's limit.

The step is a 1024th of the parent's limit, minus one. -/
theorem gasLimitToward_bounds (parentGasLimit target : Nat) :
    parentGasLimit - (parentGasLimit / 1024 - 1) ≤ gasLimitToward parentGasLimit target ∧
      gasLimitToward parentGasLimit target ≤ parentGasLimit + (parentGasLimit / 1024 - 1) := by
  unfold gasLimitToward
  dsimp only
  split
  · omega
  · split <;> omega

/-- A target within one step of the parent's limit is the gas limit itself. -/
theorem gasLimitToward_of_le_of_le {parentGasLimit target : Nat}
    (low : parentGasLimit - (parentGasLimit / 1024 - 1) ≤ target)
    (high : target ≤ parentGasLimit + (parentGasLimit / 1024 - 1)) :
    gasLimitToward parentGasLimit target = target := by
  unfold gasLimitToward
  dsimp only
  split
  · omega
  · split <;> omega

end EthLib.Base
