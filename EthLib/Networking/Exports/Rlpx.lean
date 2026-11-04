module

public import EthLib.Base.Exports
public import EthLib.Networking.Rlpx.Ecies

/-!
# `Exports.Rlpx`

C-ABI exports for RLPx, callable from the Python C extension.

A private key is 32 big-endian bytes, below the order `n`.

A public key is either SEC 1 encoding.

A key or an iv that the export rejects has code 0, apart from the codes of ECIES.
-/

public section

namespace EthLib.Networking.Rlpx.Exports

open EthLib.Exports (Result)

open EthLib.Cryptography.Secp256k1

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def eciesMessage : Ecies.EciesError → String
  | .tooShort size => s!"ciphertext has {size} bytes, fewer than {Ecies.OVERHEAD}"
  | .invalidEphemeralKey e => s!"bad ephemeral public key: {e.message}"
  | .keyAgreement e => s!"key agreement failed: {e.message}"
  | .keyDerivation _ => "key derivation failed"
  | .tagMismatch => "tag does not match"

/-- Run a fallible computation, with its error as a code and a message. -/
def runEcies {α : Type} (act : Except Ecies.EciesError α) : Result α :=
  act.mapError fun e => (e.code, eciesMessage e)

/-- A private key of 32 big-endian bytes, or an error unless it is below `n`. -/
def readPrivateKey (bytes : ByteArray) : Result Fn :=
  if bytes.size = 32 then
    let k := ofBytesBE bytes.data.toList
    if h : k < Fn.modulus then pure ⟨k, h⟩
    else throw (0, "private key is not below n")
  else throw (0, s!"bad private key size: {bytes.size}, expected 32")

/-- An encoded public key, or an error. -/
def readPublicKey (bytes : ByteArray) : Result Point :=
  match Point.decode bytes with
  | .ok p => pure p
  | .error e => throw (0, e.message)

/-- A 16-byte initialization vector, or an error for any other length. -/
def readIv (bytes : ByteArray) : Result (Vector UInt8 16) :=
  if h : bytes.size = 16 then pure ⟨bytes.data, h⟩
  else throw (0, s!"bad iv size: {bytes.size}, expected 16")

/-! ## ECIES -/

/-- The ECIES ciphertext of a message to a public key, with the given ephemeral key and iv. -/
@[export eth_rlpx_ecies_encrypt]
def eciesEncryptExport (recipient ephemeral iv sharedMac message : ByteArray) :
    Result ByteArray := do
  let q ← readPublicKey recipient
  let r ← readPrivateKey ephemeral
  let iv ← readIv iv
  runEcies (Ecies.encrypt q r iv sharedMac message)

/-- The message of an ECIES ciphertext, under a private key. -/
@[export eth_rlpx_ecies_decrypt]
def eciesDecryptExport (key sharedMac ciphertext : ByteArray) : Result ByteArray := do
  let k ← readPrivateKey key
  runEcies (Ecies.decrypt k sharedMac ciphertext)

end EthLib.Networking.Rlpx.Exports
