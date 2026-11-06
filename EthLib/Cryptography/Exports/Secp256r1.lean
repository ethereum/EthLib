module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Secp256r1.Errors
public import EthLib.Cryptography.Secp256k1.Encoding

/-!
# `Exports.Secp256r1`

C-ABI exports for secp256r1, callable from the Python C extension.

A hash is 32 bytes.

A public key is `x || y`, and a signature is `r || s`, with 32 bytes for each field.

Each field is a big-endian integer.

An operation returns its value, or the code and the message of its error.
-/

public section

namespace EthLib.Cryptography.Secp256r1.Exports

open EthLib.Exports (Result)


/-- The length of a public key: `x` then `y`, 32 bytes each. -/
def PUBLIC_KEY_LEN : Nat := 64

/-- The length of a hash. -/
def HASH_LEN : Nat := 32

/-- The length of a signature: `r` then `s`, 32 bytes each. -/
def SIGNATURE_LEN : Nat := 64

/-- Run a fallible computation, with its error as a code and a message. -/
def runSecp256r1 {α : Type} (act : Except Secp256r1Error α) : Result α :=
  act.mapError fun e => (e.code, e.message)

/-- A coordinate below `p`, or an error. -/
def readCoordinate (bytes : List UInt8) : Except Secp256r1Error Fp :=
  let v := Base.bytesToNat bytes
  if h : v < Fp.modulus then .ok ⟨v, h⟩ else .error .coordinateTooLarge

/-- The affine point of a 64-byte public key, or an error for any other length. -/
def readPublicKey (bytes : ByteArray) : Except Secp256r1Error Point := do
  if bytes.size = PUBLIC_KEY_LEN then
    let x ← readCoordinate (bytes.data.toList.take 32)
    let y ← readCoordinate (bytes.data.toList.drop 32)
    pure (.affine x y)
  else throw (.badPublicKeySize bytes.size)

/-- The integer of a 32-byte hash, or an error for any other length. -/
def readHash (bytes : ByteArray) : Except Secp256r1Error Nat :=
  if bytes.size = HASH_LEN then .ok (Base.bytesToNat bytes.data.toList)
  else .error (.badHashSize bytes.size)

/-- The integers `r` and `s` of a 64-byte signature, or an error for any other length. -/
def readSignature (bytes : ByteArray) : Except Secp256r1Error (Nat × Nat) :=
  if bytes.size = SIGNATURE_LEN then
    .ok (Base.bytesToNat (bytes.data.toList.take 32), Base.bytesToNat (bytes.data.toList.drop 32))
  else .error (.badSignatureSize bytes.size)

/-! ## Sizes

The Python C extension reads every size through these at module-init time. -/

@[export eth_secp256r1_const_public_key_len]
def constPublicKeyLen (_ : Unit) : UInt64 := UInt64.ofNat PUBLIC_KEY_LEN

@[export eth_secp256r1_const_hash_len]
def constHashLen (_ : Unit) : UInt64 := UInt64.ofNat HASH_LEN

@[export eth_secp256r1_const_signature_len]
def constSignatureLen (_ : Unit) : UInt64 := UInt64.ofNat SIGNATURE_LEN

/-! ## Operations -/

/-- ECDSA verification of a signature on a hash, under a public key. -/
@[export eth_secp256r1_verify]
def verifyExport (publicKey hash signature : ByteArray) : Result UInt8 := runSecp256r1 do
  let q ← readPublicKey publicKey
  let e ← readHash hash
  let (r, s) ← readSignature signature
  return if verify q e r s then 1 else 0

end EthLib.Cryptography.Secp256r1.Exports
