module

public import EthLib.Cryptography.Bls.Constants
public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Bls.Errors

/-!
# `Exports.Bls`

C-ABI exports for the BLS spec functions, callable from the Python C extension.

Same conventions as the KZG exports: inputs are `ByteArray` or `Array ByteArray`, and booleans come back as `UInt8`.
-/

public section

namespace EthLib.Cryptography.Bls.Exports

open EthLib.Cryptography.Bls.Constants
open EthLib.Cryptography.Bls
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

/-! ## Draft operations

Secret keys arrive as 32 big-endian bytes.

EthLib makes no constant-time claim, so these exports can leak a secret key through timing. -/

/-- A Lean `Bool` as the `UInt8` that the C extension reads. -/
def ofBool (b : Bool) : UInt8 := if b then 1 else 0

@[export eth_bls_sign]
def signExport (sk msg : ByteArray) : IO ByteArray := do
  let sk ← runBls (SecretKey.fromBytes sk)
  let sig ← runBls (sign sk msg)
  return ⟨sig.toArray⟩

@[export eth_bls_verify]
def verifyExport (pk msg sig : ByteArray) : IO UInt8 :=
  return ofBool (verify pk msg sig)

@[export eth_bls_aggregate]
def aggregateExport (sigs : Array ByteArray) : IO ByteArray := do
  let sig ← runBls (aggregate sigs)
  return ⟨sig.toArray⟩

@[export eth_bls_aggregate_verify]
def aggregateVerifyExport (pks msgs : Array ByteArray) (sig : ByteArray) : IO UInt8 :=
  return ofBool (aggregateVerify pks msgs sig)

/-- The draft's `FastAggregateVerify`, without the Ethereum rule for an empty key list. -/
@[export eth_bls_fast_aggregate_verify_core]
def fastAggregateVerifyExport (pks : Array ByteArray) (msg sig : ByteArray) : IO UInt8 :=
  return ofBool (fastAggregateVerify pks msg sig)

@[export eth_bls_pop_prove]
def popProveExport (sk : ByteArray) : IO ByteArray := do
  let sk ← runBls (SecretKey.fromBytes sk)
  let proof ← runBls (popProve sk)
  return ⟨proof.toArray⟩

@[export eth_bls_pop_verify]
def popVerifyExport (pk proof : ByteArray) : IO UInt8 :=
  return ofBool (popVerify pk proof)

end EthLib.Cryptography.Bls.Exports
