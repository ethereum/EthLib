import EthLib.Cryptography.Bls.Constants
import EthLib.Cryptography.Bls.Signatures
import EthLib.Cryptography.Bls.Errors

/-!
# `Exports.Bls`

C-ABI exports for the BLS spec functions, callable from the Python C extension.

Same conventions as the KZG exports: inputs are `ByteArray` or `Array ByteArray`, and booleans come back as `UInt8`.
-/

namespace EthLib.Cryptography.Bls.Exports

open EthLib.Cryptography.Bls.Constants
open EthLib.Cryptography.Bls.Signatures

/-- Run a fallible BLS computation down to `IO`.

A `BlsError` becomes the `IO.userError` that the C extension surfaces to callers. -/
def runBls {α : Type} (act : Except BlsError α) : IO α :=
  match act with
  | .ok a    => pure a
  | .error e => throw (IO.userError e.message)

/-! ## Sizes

The Python C extension reads every size through these at module-init time, so the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_bls_const_bytes_per_pubkey]
def constBytesPerPubkey (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_PUBKEY

@[export eth_bls_const_bytes_per_signature]
def constBytesPerSignature (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_SIGNATURE

/-! ## Operations -/

@[export eth_bls_aggregate_pubkeys]
def ethAggregatePubkeysExport
    (pubkeys : Array ByteArray) : IO ByteArray :=
  runBls (ethAggregatePubkeys pubkeys)

@[export eth_bls_fast_aggregate_verify]
def ethFastAggregateVerifyExport
    (pubkeys : Array ByteArray) (msg : ByteArray) (sig : ByteArray)
    : IO UInt8 := do
  return if ethFastAggregateVerify pubkeys msg sig then 1 else 0

end EthLib.Cryptography.Bls.Exports
