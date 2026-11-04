module

/-!
# `Ecrecover.Errors`

The one failure of the ECRECOVER precompile.

A rejected signature is not a failure: the call succeeds with an empty output.

Only a lack of gas fails the call, and it consumes all the gas given.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ecrecover

/-- Every way an ECRECOVER call can fail. -/
inductive EcrecoverError where
  /-- The gas given was below the price.

  `charge_gas` raises `OutOfGasError` in `forks/bpo2/vm/gas.py`. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EcrecoverError.code : EcrecoverError → UInt32
  | .outOfGas .. => 1

end EthLib.Execution.Evm.Precompiles.Ecrecover
