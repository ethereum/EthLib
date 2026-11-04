module

public import EthLib.Cryptography.Bls.Constants
public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Bls.KeyGen
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

/-- A secret key from input keying material and key information, as 32 big-endian bytes. -/
@[export eth_bls_key_gen]
def keyGenExport (ikm keyInfo : ByteArray) : IO ByteArray := do
  let sk ← runBls (keyGen ikm keyInfo)
  return Fr.toBytesBE sk.val

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

/-! ## Hash to curve

These exports let a client check the hash to `G2` against RFC 9380. -/

/-- The uniform bytes of RFC 9380 §5.3.1. -/
@[export eth_bls_expand_message_xmd]
def expandMessageXmdExport (msg dst : ByteArray) (len : UInt64) : IO ByteArray :=
  runBls (HashToCurve.expandMessageXmd msg dst len.toNat)

/-- The hash of a message to `G2`, as the affine `x.c0 ‖ x.c1 ‖ y.c0 ‖ y.c1`, 48 bytes each.

The point at infinity has no affine form, so it is an error. -/
@[export eth_bls_hash_to_g2]
def hashToG2Export (msg dst : ByteArray) : IO ByteArray := do
  let p ← runBls (HashToCurve.hashToG2 msg dst)
  if p.isInfinity then runBls (.error .pointAtInfinity)
  let (x, y) := p.toAffine
  return x.c0.toBytesBE ++ x.c1.toBytesBE ++ y.c0.toBytesBE ++ y.c1.toBytesBE

end EthLib.Cryptography.Bls.Exports
