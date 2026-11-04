module

public import EthLib.Base.Exports
public import EthLib.Execution.Evm.Precompiles.Ecrecover.Core

/-!
# `Exports.Ecrecover`

C-ABI exports for the ECRECOVER precompile, callable from the Python C extension.

- The input is the call data, as `ByteArray`, and the gas, as `UInt64`.
- The output is a `ByteArray`: the padded address, or empty.
- A call with too little gas fails, and returns the code and the message of its error.
-/

public section

namespace EthLib.Execution.Evm.Precompiles.Ecrecover.Exports

open EthLib.Exports (Result)

/-- The gas of a call. -/
@[export eth_ecrecover_const_gas]
def constGas (_ : Unit) : UInt64 := UInt64.ofNat GAS_ECRECOVER

/-- Run the precompile on the call data with the gas given.

EVM gas is a 64-bit integer, so the gas crosses the boundary as `UInt64`. -/
@[export eth_ecrecover]
def ecrecoverExport (data : ByteArray) (gas : UInt64) : Result ByteArray :=
  -- An empty output is a success, and only a lack of gas is an error.
  (ecrecover data gas.toNat).mapError fun e => (e.code, e.message)

end EthLib.Execution.Evm.Precompiles.Ecrecover.Exports
