module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Ecdsa.Encoding
public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Secp256k1.Sign
public import EthLib.Cryptography.Secp256k1.Ecdh
public import EthLib.Cryptography.Secp256k1.Address

/-!
# `Exports.Secp256k1`

C-ABI exports for secp256k1, callable from the Python C extension.

A public key is either SEC 1 encoding, and a hash is 32 bytes.

A signature is `r || s`, two big-endian integers of 32 bytes each.

Booleans come back as `UInt8`.

An operation returns its value, or the code and the message of its error.
-/

public section

namespace EthLib.Cryptography.Secp256k1.Exports

open EthLib.Exports (Result ExportError toResult)
open EthLib.Cryptography.Ecdsa (SIGNATURE_LEN)

/-- The length of a hash. -/
def HASH_LEN : Nat := 32

/-- An error reaches Python with its code and its own message. -/
instance : ExportError Secp256k1Error where
  code := Secp256k1Error.code
  message := Secp256k1Error.message

/-- A 32-byte hash, or an error for any other length. -/
def readHash (bytes : ByteArray) : Except Secp256k1Error (Vector UInt8 32) :=
  Base.exactBytes HASH_LEN bytes .badHashSize

/-- A 32-byte big-endian private key below `n`, or the error for its size or its value.

A larger value is rejected rather than reduced, so each key has one encoding. -/
def readPrivateKey {ε : Type} (bytes : ByteArray) (badSize : Nat → ε) (tooLarge : ε) :
    Except ε Fn :=
  if bytes.size = 32 then
    match Fn.ofBytes? bytes.data.toList with
    | some d => .ok d
    | none => .error tooLarge
  else .error (badSize bytes.size)

/-! ## Sizes

The Python C extension reads every size through these at module-init time.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_secp256k1_const_hash_len]
def constHashLen (_ : Unit) : UInt64 := UInt64.ofNat HASH_LEN

@[export eth_secp256k1_const_signature_len]
def constSignatureLen (_ : Unit) : UInt64 := UInt64.ofNat SIGNATURE_LEN

/-! ## Operations -/

/-- ECDSA verification of a signature on a hash, under an encoded public key. -/
@[export eth_secp256k1_verify]
def verifyExport (publicKey hash signature : ByteArray) : Result UInt8 := toResult none do
  let q ← Point.decode publicKey
  let h ← readHash hash
  let (r, s) ← Cryptography.Ecdsa.read signature .badSignatureSize
  return if Ecdsa.verify q h r s then 1 else 0

/-- The low-s rule of EIP-2, on the `s` of a signature. -/
@[export eth_secp256k1_is_low_s]
def isLowSExport (signature : ByteArray) : Result UInt8 := toResult (ε := Secp256k1Error) none do
  let (_, s) ← Cryptography.Ecdsa.read signature .badSignatureSize
  return if Ecdsa.isLowS s then 1 else 0

/-- The public key that signed a hash, from the signature and a recovery id of `0` or `1`.

It comes back in the 65-byte uncompressed encoding. -/
@[export eth_secp256k1_recover]
def recoverExport (hash signature : ByteArray) (recoveryId : UInt8) : Result ByteArray :=
  toResult none do
    let h ← readHash hash
    let (r, s) ← Cryptography.Ecdsa.read signature .badSignatureSize
    if hid : recoveryId.toNat < 2 then
      let q ← Ecdsa.recover h r s ⟨recoveryId.toNat, hid⟩
      return q.encodeUncompressed
    else throw (.badRecoveryId recoveryId)

/-- The signature of a hash by SEC 1 v2 §4.1.3 and RFC 6979, with the low `s` of EIP-2.

It comes back as `r || s || v`: 65 bytes, with the recovery id `v` as `0` or `1`.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3). -/
@[export eth_secp256k1_sign]
def signExport (privateKey hash : ByteArray) : Result ByteArray := toResult none do
  let d ← readPrivateKey privateKey .badPrivateKeySize .privateKeyTooLarge
  let h ← readHash hash
  let (r, s, odd) ← Ecdsa.sign d h
  return Base.packBytes (Cryptography.Ecdsa.toRecoverableBytes r.val s.val odd)

/-- The ECDH shared secret of SEC 1 v2 §3.3.1: the 32-byte `x` of `d Q`.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3). -/
@[export eth_secp256k1_ecdh]
def ecdhExport (privateKey publicKey : ByteArray) : Result ByteArray := toResult none do
  let d ← readPrivateKey privateKey .badPrivateKeySize .privateKeyTooLarge
  let q ← Point.decode publicKey
  let secret ← ecdh d q
  return ⟨secret.toArray⟩

/-- The 20-byte Ethereum address of a private key.

It is the last 20 bytes of the Keccak-256 hash of the 64 bytes of `d G`.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3). -/
@[export eth_secp256k1_address]
def addressExport (privateKey : ByteArray) : Result ByteArray :=
  toResult (ε := Secp256k1Error) none do
    let d ← readPrivateKey privateKey .badPrivateKeySize .privateKeyTooLarge
    match addressOfPrivateKey d with
    | some a => return ⟨a.toArray⟩
    -- Only the key 0 gives the point at infinity.
    | none => throw .zeroPrivateKey

end EthLib.Cryptography.Secp256k1.Exports
