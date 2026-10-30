module

public import EthLib.Precompiles.Modexp.Constants
public import EthLib.Precompiles.Modexp.Errors
public import EthLib.Precompiles.Modexp.Core

/-!
# `Exports.Modexp`

C-ABI exports for the MODEXP precompile, callable from the Python C extension.

- Inputs are `ByteArray` or `UInt64`.
- Outputs are `ByteArray` or `UInt64`.
- Failures are `IO` errors, which Python raises.
-/

public section

namespace EthLib.Precompiles.Modexp.Exports

open EthLib.Precompiles.Modexp
open EthLib.Precompiles.Modexp.Constants

/-- Run a fallible MODEXP computation down to `IO`.

The C-ABI layer turns an `IO` error into a Python exception. -/
def runModexp {α : Type} (act : Except ModexpError α) : IO α :=
  match act with
  -- Success passes straight through.
  | .ok a => pure a
  -- Failure becomes the user error the Python bindings expect.
  | .error e => throw (IO.userError e.message)

/-! ## Sizes

The Python C extension reads every size through these at module-init time, so the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_modexp_const_length_header_bytes]
def constLengthHeaderBytes (_ : Unit) : UInt64 :=
  UInt64.ofNat LENGTH_HEADER_BYTES

@[export eth_modexp_const_max_length_bytes]
def constMaxLengthBytes (_ : Unit) : UInt64 :=
  UInt64.ofNat MAX_LENGTH_BYTES

/-! ## Operations -/

/-- Run the precompile on the call data with the gas given.

EVM gas is a 64-bit integer, so the gas crosses the boundary as `UInt64`. -/
@[export eth_modexp]
def modexpExport (data : ByteArray) (gas : UInt64) : IO ByteArray :=
  runModexp (modexp data gas.toNat)

/-- The gas the precompile charges for the call data.

The price is at most 528449536 once the lengths are in bounds.

A proof in the proofs library shows this, so the conversion to `UInt64` drops nothing. -/
@[export eth_modexp_gas_cost]
def gasCostExport (data : ByteArray) : IO UInt64 :=
  runModexp ((chargedGas data).map UInt64.ofNat)

end EthLib.Precompiles.Modexp.Exports
