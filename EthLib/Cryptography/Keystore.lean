module

public import EthLib.Base.Unicode
public import EthLib.Cryptography.Aes.Ctr
public import EthLib.Cryptography.Hash.Pbkdf2
public import EthLib.Cryptography.Hash.Scrypt
public import Lean.Data.Json

/-!
# ERC-2335 keystore decryption

The three steps are key derivation, password verification and secret decryption.

[ERC-2335][erc] specifies the supported functions and the password preparation.

Unicode normalization uses the pinned Unicode 16.0.0 tables.

Metadata does not authenticate a secret or prove that it is a BLS private key.

The caller must bound KDF memory and time before reading an untrusted keystore (SOUNDNESS.md D1).

[erc]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2335.md#specification
-/

@[expose] public section

namespace EthLib.Cryptography.Keystore

open Lean (Json)

/-- A failure in reading a keystore, deriving its key or verifying its password. -/
inductive KeystoreError where
  /-- The input was not JSON. -/
  | invalidJson (reason : String)
  /-- A required field was absent or had the wrong form. -/
  | invalidField (field reason : String)
  /-- The version was not 4. -/
  | unsupportedVersion (version : Nat)
  /-- A module named a function that ERC-2335 does not support. -/
  | unsupportedFunction (step function : String)
  /-- The derived key had fewer than the 32 bytes that password verification reads. -/
  | shortKey (length : Nat)
  /-- PBKDF2 rejected its parameters. -/
  | pbkdf2 (error : Hash.Pbkdf2.Pbkdf2Error)
  /-- scrypt rejected its parameters. -/
  | scrypt (error : Hash.Scrypt.ScryptError)
  /-- The checksum did not match, so the password was not verified. -/
  | checksumMismatch
  deriving Repr

/-- Stable error codes, one per constructor. -/
def KeystoreError.code : KeystoreError → UInt32
  | .invalidJson _ => 1
  | .invalidField _ _ => 2
  | .unsupportedVersion _ => 3
  | .unsupportedFunction _ _ => 4
  | .shortKey _ => 5
  | .pbkdf2 _ => 6
  | .scrypt _ => 7
  | .checksumMismatch => 8

/-- The parameters of an ERC-2335 key derivation module. -/
inductive Kdf where
  /-- PBKDF2-HMAC-SHA-256, with iteration count, output length and salt. -/
  | pbkdf2 (iterations length : Nat) (salt : ByteArray)
  /-- scrypt, with cost, block size, parallelization, output length and salt. -/
  | scrypt (n r p length : Nat) (salt : ByteArray)

/-- The cryptographic fields read by decryption; the IV and checksum have fixed sizes. -/
structure Store where
  kdf : Kdf
  checksum : Vector UInt8 32
  iv : Aes.Block
  message : ByteArray

/-- C0, C1 and Delete, the codes removed by ERC-2335, "Password requirements". -/
def isControl (c : Char) : Bool :=
  c.toNat ≤ 0x1F || (0x7F ≤ c.toNat && c.toNat ≤ 0x9F)

/-- Normalize, strip controls and encode in UTF-8, in that order ("Password requirements"). -/
def passwordBytes (password : String) : ByteArray :=
  (String.ofList ((Base.Unicode.nfkd password).toList.filter (!isControl ·))).toUTF8

/-- A JSON field, with its name retained in any error. -/
def field (what : String) (value : Json) (name : String) : Except KeystoreError Json :=
  (value.getObjVal? name).mapError fun reason => .invalidField s!"{what}.{name}" reason

/-- A JSON string, without interpreting its contents. -/
def string (what : String) (value : Json) : Except KeystoreError String :=
  value.getStr?.mapError fun reason => .invalidField what reason

/-- A nonnegative JSON integer. -/
def number (what : String) (value : Json) : Except KeystoreError Nat :=
  value.getNat?.mapError fun reason => .invalidField what reason

/-- Require an object, including for a module whose parameters are empty. -/
def object (what : String) (value : Json) : Except KeystoreError Unit :=
  value.getObj?.map (fun _ => ()) |>.mapError fun reason => .invalidField what reason

/-- A hexadecimal digit, allowing uppercase and lowercase. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The pairs of digits of an ERC-2335 hex string, without a prefix. -/
def hexBytes (what : String) : List Char → Except KeystoreError (List UInt8)
  | [] => .ok []
  | a :: b :: rest => do
    let some hi := hexDigit a | throw (.invalidField what "not a hex digit")
    let some lo := hexDigit b | throw (.invalidField what "not a hex digit")
    return UInt8.ofNat (16 * hi + lo) :: (← hexBytes what rest)
  | [_] => .error (.invalidField what "odd number of hex digits")

/-- A byte string in the hex form used by ERC-2335. -/
def bytes (what : String) (value : Json) : Except KeystoreError ByteArray := do
  return ⟨(← hexBytes what (← string what value).toList).toArray⟩

/-- A byte string of the size its cryptographic step requires. -/
def fixed (what : String) (size : Nat) (value : Json) :
    Except KeystoreError (Vector UInt8 size) := do
  let data ← bytes what value
  if h : data.data.size = size then return ⟨data.data, h⟩
  else throw (.invalidField what s!"expected {size} bytes")

/-- The function, parameters and message that every ERC-2335 module requires ("Modules"). -/
def moduleFields (what : String) (value : Json) :
    Except KeystoreError (String × Json × Json) := do
  let name ← string s!"{what}.function" (← field what value "function")
  let params ← field what value "params"
  object s!"{what}.params" params
  let message ← field what value "message"
  let _ ← string s!"{what}.message" message
  return (name, params, message)

/-- Read the selected key derivation, including PBKDF2's required `hmac-sha256` PRF. -/
def readKdf (value : Json) : Except KeystoreError Kdf := do
  let (name, params, _) ← moduleFields "kdf" value
  let length ← number "kdf.dklen" (← field "kdf.params" params "dklen")
  if length < 32 then throw (.shortKey length)
  let salt ← bytes "kdf.salt" (← field "kdf.params" params "salt")
  if name = "pbkdf2" then
    let prf ← string "kdf.prf" (← field "kdf.params" params "prf")
    if prf ≠ "hmac-sha256" then throw (.unsupportedFunction "kdf.prf" prf)
    return .pbkdf2 (← number "kdf.c" (← field "kdf.params" params "c")) length salt
  else if name = "scrypt" then
    return .scrypt (← number "kdf.n" (← field "kdf.params" params "n"))
      (← number "kdf.r" (← field "kdf.params" params "r"))
      (← number "kdf.p" (← field "kdf.params" params "p")) length salt
  else throw (.unsupportedFunction "kdf" name)

/-- Read the version, required metadata and supported cryptographic modules ("JSON schema"). -/
def readStore (value : Json) : Except KeystoreError Store := do
  let version ← number "version" (← field "keystore" value "version")
  if version ≠ 4 then throw (.unsupportedVersion version)
  let _ ← string "path" (← field "keystore" value "path")
  let _ ← string "uuid" (← field "keystore" value "uuid")
  for name in ["description", "pubkey"] do
    if let .ok metadata := value.getObjVal? name then
      let _ ← string name metadata
  let crypto ← field "keystore" value "crypto"
  let kdf ← readKdf (← field "crypto" crypto "kdf")
  let (checksumFunction, _, checksum) ← moduleFields "checksum" (← field "crypto" crypto "checksum")
  if checksumFunction ≠ "sha256" then throw (.unsupportedFunction "checksum" checksumFunction)
  let checksum ← fixed "checksum.message" 32 checksum
  let (cipherFunction, params, message) ← moduleFields "cipher" (← field "crypto" crypto "cipher")
  if cipherFunction ≠ "aes-128-ctr" then throw (.unsupportedFunction "cipher" cipherFunction)
  return ⟨kdf, checksum, ← fixed "cipher.iv" 16 (← field "cipher.params" params "iv"),
    ← bytes "cipher.message" message⟩

/-- Derive the intermediate key ("Decryption key").

A valid RFC parameter can still exceed machine resources; the caller must bound it first.
-/
def deriveKey (password : String) (kdf : Kdf) : Except KeystoreError ByteArray :=
  let password := passwordBytes password
  match kdf with
  | .pbkdf2 iterations length salt =>
    if length < 32 then .error (.shortKey length)
    else (Hash.Pbkdf2.pbkdf2 password salt iterations length).mapError .pbkdf2
  | .scrypt n r p length salt =>
    if length < 32 then .error (.shortKey length)
    else (Hash.Scrypt.scrypt password salt n r p length).mapError .scrypt

/-- SHA-256 of key bytes 16 through 31 followed by the ciphertext ("Password verification"). -/
def passwordChecksum (key message : ByteArray) : ByteArray :=
  Hash.Sha256.hash (key.extract 16 32 ++ message)

/-- Verify the checksum before AES-128-CTR decryption ("Secret decryption").

A longer key is truncated to its first 16 bytes for AES.
-/
def decryptWithKey (store : Store) (key : ByteArray) : Except KeystoreError ByteArray := do
  if h : 32 ≤ key.size then
    if passwordChecksum key store.message != ⟨store.checksum.toArray⟩ then
      throw .checksumMismatch
    let aesKey : Aes.Key .aes128 := Vector.ofFn fun i => key[i.val]'(by
      change i.val < key.data.size
      change 32 ≤ key.data.size at h
      have hi : i.val < 16 := by simpa [Aes.KeySize.Nk] using i.isLt
      omega)
    return Aes.ctr (Aes.ciph .aes128 aesKey) 128 store.iv store.message
  else throw (.shortKey key.size)

/-- Decrypt a parsed keystore with its prepared password. -/
def decryptStore (store : Store) (password : String) : Except KeystoreError ByteArray := do
  decryptWithKey store (← deriveKey password store.kdf)

/-- Decrypt an ERC-2335 keystore value, or report the step that failed.

The decrypted octets are returned without assuming a key length or authenticating metadata.
-/
def decrypt (value : Json) (password : String) : Except KeystoreError ByteArray := do
  decryptStore (← readStore value) password

end EthLib.Cryptography.Keystore
