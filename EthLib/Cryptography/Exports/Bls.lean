module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Bls.Constants
public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Bls.KeyGen
public import EthLib.Cryptography.Bls.Errors

/-!
# `Exports.Bls`

C-ABI exports for the BLS spec functions, callable from the Python C extension.

Inputs are `ByteArray` or `Array ByteArray`, and a boolean comes back as `UInt8`.

A public key or a signature is read here into its fixed-size type, before the operation runs.

An operation returns its value, or the code and the message of its error.
-/

public section

namespace EthLib.Cryptography.Bls.Exports

open EthLib.Exports (Result)
open EthLib.Base (packBytes)

open EthLib.Cryptography.Bls.Constants
open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.Signatures

/-- Run a fallible BLS computation, with its error as a code and a message. -/
def runBls {α : Type} (act : Except BlsError α) : Result α :=
  act.mapError fun e => (e.code, e.message)

/-! ## Sizes

The Python C extension reads every size through these at module-init time, so the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_bls_const_bytes_per_pubkey]
def constBytesPerPubkey (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_PUBKEY

@[export eth_bls_const_bytes_per_signature]
def constBytesPerSignature (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_SIGNATURE

/-! ## Reading keys and signatures -/

/-- A Lean `Bool` as the `UInt8` that the C extension reads. -/
def ofBool (b : Bool) : UInt8 := if b then 1 else 0

/-- Bytes of an exact size, as a vector of that size. -/
def exactBytes? (n : Nat) (bytes : ByteArray) : Option (Vector UInt8 n) :=
  if h : bytes.size = n then some ⟨bytes.data, h⟩ else none

/-- A public key of 48 bytes.

It fails with the size of any other input. -/
def readPubkey (bytes : ByteArray) : Except BlsError BLSPubkey :=
  match exactBytes? 48 bytes with
  | some pk => .ok pk
  | none => .error (.badPubkeySize bytes.size)

/-- A signature of 96 bytes.

It fails on any other size, as the decoding of a `G2` point does. -/
def readSignature (bytes : ByteArray) : Except BlsError BLSSignature :=
  match exactBytes? 96 bytes with
  | some sig => .ok sig
  | none => .error .invalidG2Point

/-- A check of public keys and a signature.

It runs only when each key has 48 bytes and the signature 96.

It is `0` on an input of another size, as no key or signature of that size verifies. -/
def checkSized (pks : Array ByteArray) (sig : ByteArray)
    (check : Array BLSPubkey → BLSSignature → Bool) : UInt8 :=
  match pks.mapM (exactBytes? 48), exactBytes? 96 sig with
  | some pks, some sig => ofBool (check pks sig)
  | _, _ => 0

/-! ## Operations -/

/-- The aggregate of public keys, as 48 bytes.

It reads every key before it sums any.

So a key of the wrong size is reported before an earlier key that fails validation. -/
@[export eth_bls_aggregate_pubkeys]
def ethAggregatePubkeysExport
    (pubkeys : Array ByteArray) : Result ByteArray := do
  let pubkeys ← runBls (pubkeys.mapM readPubkey)
  let pk ← runBls (ethAggregatePubkeys pubkeys)
  return packBytes pk

@[export eth_bls_fast_aggregate_verify]
def ethFastAggregateVerifyExport
    (pubkeys : Array ByteArray) (msg : ByteArray) (sig : ByteArray)
    : Result UInt8 := do
  return checkSized pubkeys sig (ethFastAggregateVerify · msg ·)

/-! ## Draft operations

Secret keys arrive as 32 big-endian bytes.

EthLib makes no constant-time claim, so these exports can leak a secret key through timing. -/

/-- A secret key from input keying material and key information, as 32 big-endian bytes. -/
@[export eth_bls_key_gen]
def keyGenExport (ikm keyInfo : ByteArray) : Result ByteArray := do
  let sk ← runBls (keyGen ikm keyInfo)
  return Fr.toBytesBE sk.val

@[export eth_bls_sign]
def signExport (sk msg : ByteArray) : Result ByteArray := do
  let sk ← runBls (SecretKey.fromBytes sk)
  let sig ← runBls (sign sk msg)
  return ⟨sig.toArray⟩

@[export eth_bls_verify]
def verifyExport (pk msg sig : ByteArray) : Result UInt8 :=
  return match exactBytes? 48 pk, exactBytes? 96 sig with
    | some pk, some sig => ofBool (verify pk msg sig)
    | _, _ => 0

@[export eth_bls_aggregate]
def aggregateExport (sigs : Array ByteArray) : Result ByteArray := do
  let sigs ← runBls (sigs.mapM readSignature)
  let sig ← runBls (aggregate sigs)
  return ⟨sig.toArray⟩

@[export eth_bls_aggregate_verify]
def aggregateVerifyExport (pks msgs : Array ByteArray) (sig : ByteArray) : Result UInt8 :=
  return checkSized pks sig (aggregateVerify · msgs ·)

/-- The draft's `FastAggregateVerify`, without the Ethereum rule for an empty key list. -/
@[export eth_bls_fast_aggregate_verify_core]
def fastAggregateVerifyExport (pks : Array ByteArray) (msg sig : ByteArray) : Result UInt8 :=
  return checkSized pks sig (fastAggregateVerify · msg ·)

@[export eth_bls_pop_prove]
def popProveExport (sk : ByteArray) : Result ByteArray := do
  let sk ← runBls (SecretKey.fromBytes sk)
  let proof ← runBls (popProve sk)
  return ⟨proof.toArray⟩

@[export eth_bls_pop_verify]
def popVerifyExport (pk proof : ByteArray) : Result UInt8 :=
  return match exactBytes? 48 pk, exactBytes? 96 proof with
    | some pk, some proof => ofBool (popVerify pk proof)
    | _, _ => 0

/-! ## Point decoding

These exports let a client check the decoding of compressed points against published cases.

A point is accepted when it decompresses to a point on the curve in the subgroup of order `r`.

The point at infinity is accepted in its one canonical encoding. -/

/-- A compressed `G1` point, decoded, checked in the subgroup, and compressed again. -/
@[export eth_bls_decode_g1]
def decodeG1Export (bytes : ByteArray) : Result ByteArray := do
  let p ← runBls (G1.uncompress bytes)
  if !G1.inSubgroup p then runBls (.error .notInSubgroup)
  return G1.compress p

/-- A compressed `G2` point, decoded, checked in the subgroup, and compressed again. -/
@[export eth_bls_decode_g2]
def decodeG2Export (bytes : ByteArray) : Result ByteArray := do
  let p ← runBls (G2.uncompress bytes)
  if !G2.inSubgroup p then runBls (.error .notInSubgroup)
  return G2.compress p

/-! ## Hash to curve

These exports let a client check the hash to `G2` against RFC 9380. -/

/-- The uniform bytes of RFC 9380 §5.3.1. -/
@[export eth_bls_expand_message_xmd]
def expandMessageXmdExport (msg dst : ByteArray) (len : UInt64) : Result ByteArray :=
  runBls (HashToCurve.expandMessageXmd msg dst len.toNat)

/-- The hash of a message to `G2`, as the affine `x.c0 ‖ x.c1 ‖ y.c0 ‖ y.c1`, 48 bytes each.

The point at infinity has no affine form, so it is an error. -/
@[export eth_bls_hash_to_g2]
def hashToG2Export (msg dst : ByteArray) : Result ByteArray := do
  let p ← runBls (HashToCurve.hashToG2 (F := Fp) msg dst)
  if p.isInfinity then runBls (.error .pointAtInfinity)
  let (x, y) := p.toAffine
  return x.c0.toBytesBE ++ x.c1.toBytesBE ++ y.c0.toBytesBE ++ y.c1.toBytesBE

/-! ## Pairing

This export lets a client compare the pairing with a published value. -/

/-- The 576 bytes of an element of `Fp12`: its 12 coefficients in `Fp`, 48 bytes each.

They follow the order of the fields, from `c0.c0.c0` to `c1.c2.c1`. -/
def fp12Bytes (f : Fp12) : ByteArray :=
  [f.c0.c0, f.c0.c1, f.c0.c2, f.c1.c0, f.c1.c1, f.c1.c2].foldl
    (fun acc (a : Fp2) => acc ++ a.c0.toBytesBE ++ a.c1.toBytesBE) ByteArray.empty

/-- The pairing `e(P, Q)` of a compressed `G1` point and a compressed `G2` point.

Both points must lie in their subgroups of order `r`.

A point at infinity gives the identity, as in the pairing check. -/
@[export eth_bls_pairing]
def pairingExport (p q : ByteArray) : Result ByteArray := do
  let P ← runBls (G1.uncompress p)
  let Q ← runBls (G2.uncompress q)
  if !G1.inSubgroup P || !G2.inSubgroup Q then runBls (.error .notInSubgroup)
  return fp12Bytes (pairing P Q)

end EthLib.Cryptography.Bls.Exports
