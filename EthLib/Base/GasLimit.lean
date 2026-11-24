module

/-!
# `Base.GasLimit`

The gas limit that a block takes when it moves from its parent's toward a target.

Consensus checks a builder's bid with it, and Engine builds a payload with it.

So it sits below both.
-/

@[expose] public section

namespace EthLib.Base

/-- The gas limit that moves from a parent's limit toward a target, by at most one step.

The payload build of this library follows this step, and a bid of Gloas must follow it. -/
def gasLimitToward (parentGasLimit target : Nat) : Nat :=
  -- A block may change the gas limit by less than a 1024th of the parent's.
  --
  -- So the step is a 1024th of the parent's limit, minus one, and 0 for a limit below 2048.
  let step := parentGasLimit / 1024 - 1
  -- A target below the parent's limit minus the step gives that lower bound.
  --
  -- It is the lowest limit that one block allows.
  if target < parentGasLimit - step then parentGasLimit - step
  -- A target above the parent's limit plus the step gives that upper bound.
  --
  -- It is the highest limit that one block allows.
  else if parentGasLimit + step < target then parentGasLimit + step
  -- Any other target, within one step, is the gas limit itself.
  else target

end EthLib.Base
