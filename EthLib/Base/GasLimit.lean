module

/-!
# `Base.GasLimit`

The gas limit that a block takes when it moves from its parent's toward a target.

Both layers use it, so it sits below them.
-/

@[expose] public section

namespace EthLib.Base

/-- The gas limit that moves from a parent's limit toward a target, by at most one step.

A block may change the gas limit by less than a 1024th of the parent's.

So the step is a 1024th of the parent's limit, minus one, and 0 for a limit below 2048.

A target below the parent's limit minus the step gives that lower bound.

A target above the parent's limit plus the step gives that upper bound.

Any other target is the gas limit itself.

The payload build of this library follows this step, and a bid of Gloas must follow it. -/
def gasLimitToward (parentGasLimit target : Nat) : Nat :=
  -- The largest change that keeps below a 1024th of the parent's limit.
  let step := parentGasLimit / 1024 - 1
  -- A target too far below stops at the lowest limit that one block allows.
  if target < parentGasLimit - step then parentGasLimit - step
  -- A target too far above stops at the highest limit that one block allows.
  else if parentGasLimit + step < target then parentGasLimit + step
  -- A target within one step is reached.
  else target

end EthLib.Base
