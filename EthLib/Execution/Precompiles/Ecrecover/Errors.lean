module

/-!
# `Ecrecover.Errors`

The one failure of the ECRECOVER precompile.

A rejected signature is not a failure: the call succeeds with an empty output.

Only a lack of gas fails the call, and it consumes all the gas given.
-/

@[expose] public section

namespace EthLib.Execution.Precompiles.Ecrecover

/-- Every way an ECRECOVER call can fail. -/
inductive EcrecoverError where
  /-- The gas given was below the price.

  `charge_gas` raises `OutOfGasError` in `forks/bpo2/vm/gas.py`. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- Human-readable description of the failure. -/
def EcrecoverError.message : EcrecoverError → String
  | .outOfGas cost gas => s!"out of gas: price {cost}, gas {gas}"

end EthLib.Execution.Precompiles.Ecrecover
