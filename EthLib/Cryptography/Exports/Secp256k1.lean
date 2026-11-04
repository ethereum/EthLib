module

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
-/

public section

namespace EthLib.Cryptography.Secp256k1.Exports

/-- The length of a hash. -/
def HASH_LEN : Nat := 32

/-- The length of a signature: `r` then `s`, 32 bytes each. -/
def SIGNATURE_LEN : Nat := 64

/-- Run a fallible computation down to `IO`.

The C extension turns the error into a Python exception. -/
def runSecp256k1 {α : Type} (act : Except Secp256k1Error α) : IO α :=
  match act with
  | .ok a => pure a
  | .error e => throw (IO.userError e.message)

/-- A 32-byte hash, or an error for any other length. -/
def readHash (bytes : ByteArray) : IO (Vector UInt8 32) :=
  if h : bytes.size = 32 then pure ⟨bytes.data, h⟩
  else throw (IO.userError s!"bad hash size: {bytes.size}, expected {HASH_LEN}")

/-- A 32-byte big-endian private key below `n`, or an error.

A larger value is rejected rather than reduced, so each key has one encoding. -/
def readPrivateKey (bytes : ByteArray) : IO Fn :=
  if bytes.size = 32 then
    let d := ofBytesBE bytes.data.toList
    if h : d < Fn.modulus then pure ⟨d, h⟩
    else throw (IO.userError "bad private key: not below the group order n")
  else throw (IO.userError s!"bad private key size: {bytes.size}, expected 32")

/-- The integers `r` and `s` of a 64-byte signature, or an error for any other length. -/
def readSignature (bytes : ByteArray) : IO (Nat × Nat) :=
  if bytes.size = SIGNATURE_LEN then
    pure (ofBytesBE (bytes.data.toList.take 32), ofBytesBE (bytes.data.toList.drop 32))
  else throw (IO.userError s!"bad signature size: {bytes.size}, expected {SIGNATURE_LEN}")

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
def verifyExport (publicKey hash signature : ByteArray) : IO UInt8 := do
  let q ← runSecp256k1 (Point.decode publicKey)
  let h ← readHash hash
  let (r, s) ← readSignature signature
  return if Ecdsa.verify q h r s then 1 else 0

/-- The low-s rule of EIP-2, on the `s` of a signature. -/
@[export eth_secp256k1_is_low_s]
def isLowSExport (signature : ByteArray) : IO UInt8 := do
  let (_, s) ← readSignature signature
  return if Ecdsa.isLowS s then 1 else 0

/-- The public key that signed a hash, recovered from the signature and a recovery id of `0` or `1`.

It comes back in the 65-byte uncompressed encoding. -/
@[export eth_secp256k1_recover]
def recoverExport (hash signature : ByteArray) (recoveryId : UInt8) : IO ByteArray := do
  let h ← readHash hash
  let (r, s) ← readSignature signature
  if hid : recoveryId.toNat < 2 then
    let q ← runSecp256k1 (Ecdsa.recover h r s ⟨recoveryId.toNat, hid⟩)
    return q.encodeUncompressed
  else throw (IO.userError s!"bad recovery id: {recoveryId}, expected 0 or 1")

/-- The signature of a hash by SEC 1 v2 §4.1.3 and RFC 6979, with the low `s` of EIP-2.

It comes back as `r || s || v`: 65 bytes, with the recovery id `v` as `0` or `1`.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3). -/
@[export eth_secp256k1_sign]
def signExport (privateKey hash : ByteArray) : IO ByteArray := do
  let d ← readPrivateKey privateKey
  let h ← readHash hash
  let (r, s, odd) ← runSecp256k1 (Ecdsa.sign d h)
  return ⟨(toBytesBE 32 r.val ++ toBytesBE 32 s.val ++ [if odd then 1 else 0]).toArray⟩

/-- The ECDH shared secret of SEC 1 v2 §3.3.1: the 32-byte `x` of `d Q`.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3). -/
@[export eth_secp256k1_ecdh]
def ecdhExport (privateKey publicKey : ByteArray) : IO ByteArray := do
  let d ← readPrivateKey privateKey
  let q ← runSecp256k1 (Point.decode publicKey)
  let secret ← runSecp256k1 (ecdh d q)
  return ⟨secret.toArray⟩

/-- The 20-byte Ethereum address of a private key.

It is the last 20 bytes of the Keccak-256 hash of the 64 bytes of `d G`.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3). -/
@[export eth_secp256k1_address]
def addressExport (privateKey : ByteArray) : IO ByteArray := do
  let d ← readPrivateKey privateKey
  match addressOfPrivateKey d with
  | some a => return ⟨a.toArray⟩
  | none => throw (IO.userError "zero private key: d G is the point at infinity")

end EthLib.Cryptography.Secp256k1.Exports
