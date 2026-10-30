import EthLib.Cryptography.Secp256k1.Ecdsa

/-!
# `Exports.Secp256k1`

C-ABI exports for secp256k1, callable from the Python C extension.

A public key is either SEC 1 encoding, a hash is 32 bytes, and a signature is 64 bytes.

```text
    signature   [ r: 32 | s: 32 ]          big-endian integers
```

Booleans come back as `UInt8`.
-/

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

end EthLib.Cryptography.Secp256k1.Exports
