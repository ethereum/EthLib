module

public import EthLib.Execution.Evm.Precompiles.Identity

/-!
# `Exports.Identity`

C-ABI exports for the IDENTITY precompile, callable from the Python C extension.

- The inputs are the call data, as `ByteArray`, and the gas, as `UInt64`.
- The outputs are a `ByteArray` and a `UInt64` price.
- A lack of gas is an `IO` error, which Python raises.
-/

public section

namespace EthLib.Execution.Evm.Precompiles.Identity.Exports

/-- Run the precompile on the call data with the gas given.

Execution-specs counts gas in an unbounded `Uint`, and the specification takes a `Nat`.

The C interface of the bindings takes the gas as `UInt64`, so a caller can pass any gas below 2^64.

`UInt64.toNat` keeps every such value, so the specification sees the exact gas. -/
@[export eth_identity]
def identityExport (data : ByteArray) (gas : UInt64) : IO ByteArray :=
  match identity data gas.toNat with
  | .ok out => pure out
  -- A lack of gas becomes the user error that the Python bindings expect.
  | .error e => throw (IO.userError e.message)

/-- The gas that the precompile charges for the call data.

Call data from Python is shorter than 2^63 bytes.

For call data shorter than 2^64 bytes, `toNat_ofNat_gasCost` in the proofs library shows that the conversion to `UInt64` keeps the price. -/
@[export eth_identity_gas_cost]
def gasCostExport (data : ByteArray) : UInt64 :=
  UInt64.ofNat (gasCost data.size)

end EthLib.Execution.Evm.Precompiles.Identity.Exports
