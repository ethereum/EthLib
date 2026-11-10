module

/-!
# `Base.GasLimit`

The gas limit that a block takes when it moves from its parent's toward a target.

A block may change the gas limit by less than a 1024th of the parent's.

So one block moves it by at most that 1024th minus one, and stops at the target if it is closer.

A builder of the execution layer follows this step, and a bid of Gloas must follow it too.

Both layers share the step, so it sits below them.
-/

@[expose] public section

namespace EthLib.Base

/-- The gas limit that moves from a parent's limit toward a target, by at most one step.

The step is a 1024th of the parent's limit, minus one, and 0 for a limit below 2048.

A target below the parent's limit minus the step gives that lower bound.

A target above the parent's limit plus the step gives that upper bound.

Any other target is the gas limit itself. -/
def gasLimitToward (parentGasLimit target : Nat) : Nat :=
  let step := parentGasLimit / 1024 - 1
  if target < parentGasLimit - step then parentGasLimit - step
  else if parentGasLimit + step < target then parentGasLimit + step
  else target

end EthLib.Base
