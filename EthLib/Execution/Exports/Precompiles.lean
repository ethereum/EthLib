module

public import EthLib.Execution.Evm.Precompiles.Table

/-!
# `Exports.Precompiles`

A C-ABI export that runs any of the 18 precompiles, callable from the Python C extension.

- The address and the gas are `UInt64`, and the call data is a `ByteArray`.
- A failed call, or an address with no precompile, is an `IO` error, which Python raises.
-/

public section

namespace EthLib.Execution.Evm.Precompiles.Exports

open EthLib.Execution.Evm.Precompiles

/-- Run the precompile at the address on the call data, with the gas given.

The error message is the error of the precompile, as Lean prints it. -/
@[export eth_precompile_run]
def runExport (address : UInt64) (data : ByteArray) (gas : UInt64) : IO ByteArray :=
  match run address.toNat data gas.toNat with
  | some (.ok out) => pure out
  | some (.error e) => throw (IO.userError (reprStr e))
  | none => throw (IO.userError s!"no precompile at address {address}")

end EthLib.Execution.Evm.Precompiles.Exports
