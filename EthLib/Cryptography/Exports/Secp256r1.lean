module

public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Secp256k1.Encoding

/-!
# `Exports.Secp256r1`

C-ABI exports for secp256r1, callable from the Python C extension.

A hash is 32 bytes.

A public key is `x || y`, and a signature is `r || s`, with 32 bytes for each field.

Each field is a big-endian integer.
-/

public section

namespace EthLib.Cryptography.Secp256r1.Exports

open EthLib.Cryptography.Secp256k1 (ofBytesBE)

/-- The length of a public key: `x` then `y`, 32 bytes each. -/
def PUBLIC_KEY_LEN : Nat := 64

/-- The length of a hash. -/
def HASH_LEN : Nat := 32

/-- The length of a signature: `r` then `s`, 32 bytes each. -/
def SIGNATURE_LEN : Nat := 64

/-- A coordinate below `p`, or an error. -/
def readCoordinate (bytes : List UInt8) : IO Fp :=
  let v := ofBytesBE bytes
  if h : v < Fp.modulus then pure ⟨v, h⟩
  else throw (IO.userError "bad public key: a coordinate is not below p")

/-- The affine point of a 64-byte public key, or an error for any other length. -/
def readPublicKey (bytes : ByteArray) : IO Point := do
  if bytes.size = PUBLIC_KEY_LEN then
    let x ← readCoordinate (bytes.data.toList.take 32)
    let y ← readCoordinate (bytes.data.toList.drop 32)
    pure (.affine x y)
  else throw (IO.userError s!"bad public key size: {bytes.size}, expected {PUBLIC_KEY_LEN}")

/-- The integer of a 32-byte hash, or an error for any other length. -/
def readHash (bytes : ByteArray) : IO Nat :=
  if bytes.size = HASH_LEN then pure (ofBytesBE bytes.data.toList)
  else throw (IO.userError s!"bad hash size: {bytes.size}, expected {HASH_LEN}")

/-- The integers `r` and `s` of a 64-byte signature, or an error for any other length. -/
def readSignature (bytes : ByteArray) : IO (Nat × Nat) :=
  if bytes.size = SIGNATURE_LEN then
    pure (ofBytesBE (bytes.data.toList.take 32), ofBytesBE (bytes.data.toList.drop 32))
  else throw (IO.userError s!"bad signature size: {bytes.size}, expected {SIGNATURE_LEN}")

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
def verifyExport (publicKey hash signature : ByteArray) : IO UInt8 := do
  let q ← readPublicKey publicKey
  let e ← readHash hash
  let (r, s) ← readSignature signature
  return if verify q e r s then 1 else 0

end EthLib.Cryptography.Secp256r1.Exports
