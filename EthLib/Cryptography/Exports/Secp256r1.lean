module

public import EthLib.Base.Exports
public import EthLib.Base.ByteOrder
public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Secp256r1.Errors
public import EthLib.Cryptography.Secp256r1.Encoding
public import EthLib.Cryptography.Ecdsa.Encoding

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

open EthLib.Exports (Result ExportError toResult)
open EthLib.Cryptography.Ecdsa (SIGNATURE_LEN)


/-- The length of a public key: `x` then `y`, 32 bytes each. -/
def PUBLIC_KEY_LEN : Nat := 64

/-- The length of a hash. -/
def HASH_LEN : Nat := 32

/-- An error reaches Python with its code and its own message. -/
instance : ExportError Secp256r1Error where
  code := Secp256r1Error.code
  message := Secp256r1Error.message

/-- 32 bytes as a coordinate below `p`, by SEC 1 v2 §2.3.6, or an error. -/
def readCoordinate (bytes : ByteArray) : Except Secp256r1Error Fp :=
  match Sec1.fieldOfBytes? sec1 bytes with
  | some x => .ok x
  -- The integer of the 32 bytes is `p` or more.
  | none => .error (.coordinateTooLarge (Base.ByteOrder.ofBE bytes.data.toList))

/-- The affine point of a 64-byte public key, or an error for any other length. -/
def readPublicKey (bytes : ByteArray) : Except Secp256r1Error Point := do
  if bytes.size = PUBLIC_KEY_LEN then
    let x ← readCoordinate (bytes.extract 0 32)
    let y ← readCoordinate (bytes.extract 32 PUBLIC_KEY_LEN)
    pure (.affine x y)
  else throw (.badPublicKeySize bytes.size)

/-- The integer of a 32-byte hash, or an error for any other length. -/
def readHash (bytes : ByteArray) : Except Secp256r1Error Nat :=
  if bytes.size = HASH_LEN then .ok (Base.ByteOrder.ofBE bytes.data.toList)
  else .error (.badHashSize bytes.size)

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
def verifyExport (publicKey hash signature : ByteArray) : Result UInt8 := toResult none do
  let q ← readPublicKey publicKey
  let e ← readHash hash
  let (r, s) ← Cryptography.Ecdsa.read signature .badSignatureSize
  return if verify q e r s then 1 else 0

end EthLib.Cryptography.Secp256r1.Exports
