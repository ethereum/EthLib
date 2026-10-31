import EthLib.Precompiles.Ripemd160

/-!
# `Exports.Ripemd160`

C-ABI exports for the RIPEMD-160 precompile, callable from the Python C extension.

- Input and output are `ByteArray`.
- The precompile never fails, so no export returns an `IO` error.
-/

namespace EthLib.Precompiles.Ripemd160.Exports

/-! ## Sizes

The Python C extension reads every size through these at module-init time, so the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_ripemd160_const_output_bytes]
def constOutputBytes (_ : Unit) : UInt64 :=
  UInt64.ofNat OUTPUT_BYTES

/-! ## Operations -/

/-- The output of the precompile on the call data: the digest, left-padded to 32 bytes. -/
@[export eth_ripemd160]
def ripemd160Export (data : ByteArray) : ByteArray :=
  ripemd160 data

end EthLib.Precompiles.Ripemd160.Exports
