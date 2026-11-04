module

public import EthLib.Base.Exports
public import EthLib.Execution.Evm.Precompiles.Table

/-!
# `Exports.Precompiles`

A C-ABI export that runs any of the 18 precompiles, callable from the Python C extension.

- The address and the gas are `UInt64`, and the call data is a `ByteArray`.
- A failed call, or an address with no precompile, comes back as an error code and a message.
-/

public section

namespace EthLib.Execution.Evm.Precompiles.Exports

open EthLib.Exports (Result)

open EthLib.Execution.Evm.Precompiles

/-- Run the precompile at the address on the call data, with the gas given.

The code of a failed call names the precompile, and the message is its error, as Lean prints it.

An address with no precompile has code 0, which no error of a precompile has. -/
@[export eth_precompile_run]
def runExport (address : UInt64) (data : ByteArray) (gas : UInt64) : Result ByteArray :=
  match run address.toNat data gas.toNat with
  | some result => result.mapError fun e => (e.code, reprStr e)
  | none => .error (0, s!"no precompile at address {address}")

end EthLib.Execution.Evm.Precompiles.Exports
