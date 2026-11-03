module

public import EthLib.Execution.Evm.Precompiles.Sha256

/-!
# `Exports.Sha256`

C-ABI exports for the SHA-256 precompile, callable from the Python C extension.

- Inputs are `ByteArray` or `UInt64`.
- Outputs are `ByteArray` or `UInt64`.
- Running out of gas is an `IO` error, which Python raises.

The symbols carry `precompile` in their names, because `eth_sha256` is the bare hash of the cryptography exports.
-/

public section

namespace EthLib.Execution.Evm.Precompiles.Sha256.Exports

open EthLib.Execution.Evm.Precompiles.Sha256

/-! ## Sizes

The Python C extension reads every size through these at module-init time, so the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_sha256_precompile_const_output_bytes]
def constOutputBytes (_ : Unit) : UInt64 :=
  UInt64.ofNat OUTPUT_BYTES

/-! ## Operations -/

/-- Run the precompile on the call data with the gas given.

EVM gas is a 64-bit integer, so the gas crosses the boundary as `UInt64`. -/
@[export eth_sha256_precompile]
def sha256Export (data : ByteArray) (gas : UInt64) : IO ByteArray :=
  match sha256 data gas.toNat with
  | .ok out => pure out
  | .error e => throw (IO.userError e.message)

/-- The gas the precompile charges for the call data.

Call data from Python is shorter than 2^63 bytes, so the price is below 2^64.

`gasCost_lt_two_pow_64` in the proofs library shows this, so the conversion to `UInt64` drops nothing. -/
@[export eth_sha256_precompile_gas_cost]
def gasCostExport (data : ByteArray) : UInt64 :=
  UInt64.ofNat (gasCost data.size)

end EthLib.Execution.Evm.Precompiles.Sha256.Exports
