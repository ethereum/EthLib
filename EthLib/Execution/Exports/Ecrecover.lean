module

public import EthLib.Execution.Precompiles.Ecrecover.Core

/-!
# `Exports.Ecrecover`

C-ABI exports for the ECRECOVER precompile, callable from the Python C extension.

- The input is the call data, as `ByteArray`, and the gas, as `UInt64`.
- The output is a `ByteArray`: the padded address, or empty.
- Running out of gas is an `IO` error, which Python raises.
-/

public section

namespace EthLib.Execution.Precompiles.Ecrecover.Exports

/-- The gas of a call. -/
@[export eth_ecrecover_const_gas]
def constGas (_ : Unit) : UInt64 := UInt64.ofNat GAS_ECRECOVER

/-- Run the precompile on the call data with the gas given.

EVM gas is a 64-bit integer, so the gas crosses the boundary as `UInt64`. -/
@[export eth_ecrecover]
def ecrecoverExport (data : ByteArray) (gas : UInt64) : IO ByteArray :=
  match ecrecover data gas.toNat with
  -- Success passes straight through, an empty output included.
  | .ok out => pure out
  -- A lack of gas becomes the user error the Python bindings expect.
  | .error e => throw (IO.userError e.message)

end EthLib.Execution.Precompiles.Ecrecover.Exports
