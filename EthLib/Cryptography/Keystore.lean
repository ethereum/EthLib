module

public import EthLib.Base.Hex
public import EthLib.Base.Unicode
public import EthLib.Cryptography.Aes.Ctr
public import EthLib.Cryptography.Bls.KeyPath
public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Hash.Pbkdf2
public import EthLib.Cryptography.Hash.Scrypt
public import Lean.Data.Json

/-!
# ERC-2335 keystores

Decryption has three steps: key derivation, password verification and secret decryption.

Encryption runs the same steps forward, with the salt, the IV and the UUID as inputs.

[ERC-2335][erc] specifies the supported functions and the password preparation.

Unicode normalization uses the pinned Unicode 16.0.0 tables.

Metadata does not authenticate a secret or prove that it is a BLS private key.

The reader still checks its form: an ERC-2334 path, an RFC 4122 UUID and a 48-byte public key.

ERC-2335 allows a path of any depth, but ERC-2334 requires at least four indices, and wins here.

The public key is 48 bytes of hex with no marker, as in the vectors of ERC-2335.

A separate check compares the public key with that of the decrypted secret.

Decryption takes bounds on the memory and work of key derivation, set by the caller.

They are checked before any derivation step runs, since a keystore may request any cost.

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
  /-- The modeled memory or work of key derivation exceeds the caller's limits; both are given. -/
  | limitExceeded (memory work : Nat)
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
  | .limitExceeded _ _ => 9

/-- The parameters of an ERC-2335 key derivation module. -/
inductive Kdf where
  /-- PBKDF2-HMAC-SHA-256, with iteration count, output length and salt. -/
  | pbkdf2 (iterations length : Nat) (salt : ByteArray)
  /-- scrypt, with cost, block size, parallelization, output length and salt. -/
  | scrypt (n r p length : Nat) (salt : ByteArray)

/-- A model of the memory of a key derivation, in bytes of its buffers.

PBKDF2 holds its whole 32-byte output blocks, and the key cut from them.

scrypt holds `N` blocks of `128 * r` bytes in ROMix, four buffers of `p` blocks, and its output.

Those buffers are the expanded password, the mixed blocks, and two copies that hashing makes.

It counts payload bytes only: no object headers, pointers or temporary blocks of ROMix.

No theorem relates it to the memory that the code uses.
-/
def Kdf.memory : Kdf → Nat
  | .pbkdf2 _ length _ => (length + 31) / 32 * 32 + length
  | .scrypt n r p length _ => 128 * r * n + 4 * (128 * r * p) + (length + 31) / 32 * 32 + length

/-- The SHA-256 compressions that hash a message of `n` bytes, padding included (FIPS 180-4). -/
def shaBlocks (n : Nat) : Nat :=
  (n + 9 + 63) / 64

/-- The SHA-256 compressions of one HMAC call (RFC 2104), from the key and message sizes.

A key longer than a block is hashed first; the inner and outer hashes each start with a block.
-/
def hmacBlocks (key message : Nat) : Nat :=
  (if key > 64 then shaBlocks key else 0) + shaBlocks (64 + message) + shaBlocks (64 + 32)

/-- The SHA-256 compressions of PBKDF2-HMAC-SHA-256 (RFC 8018, section 5.2).

Each 32-byte block of output makes one HMAC call on the salt and the block index.

It then makes one HMAC call on the previous 32-byte value for each further iteration.
-/
def pbkdf2Blocks (password salt iterations length : Nat) : Nat :=
  (length + 31) / 32 * (hmacBlocks password (salt + 4) + (iterations - 1) * hmacBlocks password 32)

/-- A model of the work of a key derivation with a password of the given size.

It counts calls of a function on one 64-byte block: the SHA-256 compression and the Salsa20/8 core.

It is a count, not a time: the other steps of BlockMix and ROMix weigh more when `r` is small.

scrypt makes `2 * r` Salsa20/8 calls per BlockMix, and `2 * N` BlockMix calls per block.

It also runs PBKDF2 once to expand the password into `p` blocks, and once on them for its output.
-/
def Kdf.work (password : Nat) : Kdf → Nat
  | .pbkdf2 iterations length salt => pbkdf2Blocks password salt.size iterations length
  | .scrypt n r p length salt =>
    4 * n * r * p + pbkdf2Blocks password salt.size 1 (128 * r * p) +
      pbkdf2Blocks password (128 * r * p) 1 length

/-- The largest key derivation that a caller accepts from a keystore. -/
structure KdfLimits where
  /-- The largest memory, in bytes. -/
  memory : Nat
  /-- The largest work, in SHA-256 compressions and Salsa20/8 cores. -/
  work : Nat

/-- Whether a key derivation with a password of the given size stays within the limits. -/
def KdfLimits.admits (limits : KdfLimits) (password : Nat) (kdf : Kdf) : Bool :=
  kdf.memory ≤ limits.memory && kdf.work password ≤ limits.work

/-- The metadata of a keystore, which ERC-2335 neither encrypts nor authenticates. -/
structure Metadata where
  /-- The ERC-2334 path of the key, none for the empty string. -/
  path : Option Bls.KeyPath.Path
  /-- The 16 bytes of the UUID. -/
  uuid : Vector UInt8 16
  /-- The public key of the secret, which the file may leave out. -/
  pubkey : Option Bls.BLSPubkey
  /-- A description, which the file may leave out. -/
  description : Option String
  deriving DecidableEq, Repr

/-- The fields read by decryption, then the metadata; the IV and checksum have fixed sizes. -/
structure Store where
  kdf : Kdf
  checksum : Vector UInt8 32
  iv : Aes.Block
  message : ByteArray
  metadata : Metadata

/-- C0, C1 and Delete, the codes removed by ERC-2335, "Password requirements". -/
def isControl (c : Char) : Bool :=
  -- C0 is `0x00` to `0x1F`, Delete is `0x7F`, and C1 is `0x80` to `0x9F`, all inclusive.
  c.toNat ≤ 0x1F || (0x7F ≤ c.toNat && c.toNat ≤ 0x9F)

/-- Normalize, strip controls and encode in UTF-8, in that order ("Password requirements"). -/
def passwordBytes (password : String) : ByteArray :=
  -- The NFKD form first, then the control codes stripped, then UTF-8.
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

/-- A byte string in the hex form used by ERC-2335, in either letter case and with no prefix. -/
def bytes (what : String) (value : Json) : Except KeystoreError ByteArray := do
  let digits := (← string what value).toList
  if digits.length % 2 = 1 then throw (.invalidField what "odd number of hex digits")
  let some data := Base.hexBytes? digits | throw (.invalidField what "not a hex digit")
  return data

/-- A byte string of the size its cryptographic step requires. -/
def fixed (what : String) (size : Nat) (value : Json) :
    Except KeystoreError (Vector UInt8 size) := do
  Base.exactBytes size (← bytes what value) fun _ => .invalidField what s!"expected {size} bytes"

/-- A field that the keystore may leave out, read when it is present. -/
def optionalField {α : Type} (value : Json) (name : String)
    (read : Json → Except KeystoreError α) : Except KeystoreError (Option α) :=
  match value.getObjVal? name with
  | .ok present => some <$> read present
  | .error _ => .ok none

/-- The path of the key: none for the empty string, or an ERC-2334 path ("Path"). -/
def readPath (value : Json) : Except KeystoreError (Option Bls.KeyPath.Path) := do
  let text ← string "path" value
  if text = "" then return none
  match Bls.KeyPath.parsePath text with
  | .ok path => return some path
  | .error error => throw (.invalidField "path" error.message)

/-- The positions of the four hyphens in the text form of a UUID, RFC 4122 §3. -/
def uuidHyphens : List Nat := [8, 13, 18, 23]

/-- A UUID in the text form of RFC 4122 §3: hex digit groups of 8, 4, 4, 4 and 12, with hyphens.

The digits may be in either letter case, as the RFC allows on input.

The version bits are not checked, since ERC-2335 asks only for a random UUID.
-/
def readUuid (value : Json) : Except KeystoreError (Vector UInt8 16) := do
  let chars := (← string "uuid" value).toList
  unless chars.length = 36 && uuidHyphens.all (chars[·]? == some '-') do
    throw (.invalidField "uuid" "not the 8-4-4-4-12 form of RFC 4122")
  -- The 32 digits around the hyphens; a hyphen elsewhere is not a hex digit.
  let digits := chars.take 8 ++ (chars.drop 9).take 4 ++ (chars.drop 14).take 4 ++
    (chars.drop 19).take 4 ++ chars.drop 24
  let some data := Base.hexBytes? digits | throw (.invalidField "uuid" "not a hex digit")
  Base.exactBytes 16 data fun _ => .invalidField "uuid" "expected 16 bytes"

/-- The metadata of a keystore ("JSON schema"): its path, UUID, public key and description. -/
def readMetadata (value : Json) : Except KeystoreError Metadata := do
  let path ← readPath (← field "keystore" value "path")
  let uuid ← readUuid (← field "keystore" value "uuid")
  let description ← optionalField value "description" (string "description")
  let pubkey ← optionalField value "pubkey" (fixed "pubkey" 48)
  return ⟨path, uuid, pubkey, description⟩

/-- The function, parameters and message that every ERC-2335 module requires ("Modules"). -/
def moduleFields (what : String) (value : Json) :
    Except KeystoreError (String × Json × Json) := do
  -- Modules: each has a `function`, its `params`, and a `message`.
  let name ← string s!"{what}.function" (← field what value "function")
  let params ← field what value "params"
  object s!"{what}.params" params
  let message ← field what value "message"
  let _ ← string s!"{what}.message" message
  return (name, params, message)

/-- Read the selected key derivation, including PBKDF2's required `hmac-sha256` PRF.

An unsupported function is reported before any of its parameters is read.
-/
def readKdf (value : Json) : Except KeystoreError Kdf := do
  let (name, params, _) ← moduleFields "kdf" value
  let param (what name : String) := do number what (← field "kdf.params" params name)
  -- The output length and salt, which both functions take.
  let common : Except KeystoreError (Nat × ByteArray) := do
    let length ← param "kdf.dklen" "dklen"
    -- Not in ERC-2335's tables: `dklen` below 32 leaves no `decryption_key[16:32]` (step 0).
    if length < 32 then throw (.shortKey length)
    return (length, ← bytes "kdf.salt" (← field "kdf.params" params "salt"))
  -- Decryption key, KDF table: `"pbkdf2"` has `"c"`, `"dklen"`, `"prf": "hmac-sha256"`, `"salt"`.
  if name = "pbkdf2" then
    let (length, salt) ← common
    let prf ← string "kdf.prf" (← field "kdf.params" params "prf")
    if prf ≠ "hmac-sha256" then throw (.unsupportedFunction "kdf.prf" prf)
    return .pbkdf2 (← param "kdf.c" "c") length salt
  -- `"scrypt"` has `"dklen"`, `"n"`, `"p"`, `"r"` and `"salt"`.
  else if name = "scrypt" then
    let (length, salt) ← common
    return .scrypt (← param "kdf.n" "n") (← param "kdf.r" "r") (← param "kdf.p" "p") length salt
  else throw (.unsupportedFunction "kdf" name)

/-- Read the version, metadata and supported cryptographic modules ("JSON schema"). -/
def readStore (value : Json) : Except KeystoreError Store := do
  -- Version: the `version` is set to `4`.
  let version ← number "version" (← field "keystore" value "version")
  if version ≠ 4 then throw (.unsupportedVersion version)
  let metadata ← readMetadata value
  let crypto ← field "keystore" value "crypto"
  let kdf ← readKdf (← field "crypto" crypto "kdf")
  -- Password verification, hash table: `"sha256"`, which lists no `params`.
  --
  -- Any `params` given are read as an object, then ignored.
  let (checksumFunction, _, checksum) ← moduleFields "checksum" (← field "crypto" crypto "checksum")
  if checksumFunction ≠ "sha256" then throw (.unsupportedFunction "checksum" checksumFunction)
  let checksum ← fixed "checksum.message" 32 checksum
  -- Secret decryption, cipher table: `"aes-128-ctr"`, with the param `"iv"`.
  let (cipherFunction, params, message) ← moduleFields "cipher" (← field "crypto" crypto "cipher")
  if cipherFunction ≠ "aes-128-ctr" then throw (.unsupportedFunction "cipher" cipherFunction)
  return ⟨kdf, checksum, ← fixed "cipher.iv" 16 (← field "cipher.params" params "iv"),
    ← bytes "cipher.message" message, metadata⟩

/-- Derive the intermediate key from the prepared password ("Decryption key").

This runs the derivation at any cost, so decryption checks the caller's limits first.
-/
def deriveKey (password : ByteArray) (kdf : Kdf) : Except KeystoreError ByteArray :=
  match kdf with
  | .pbkdf2 iterations length salt =>
    if length < 32 then .error (.shortKey length)
    else (Hash.Pbkdf2.pbkdf2 password salt iterations length).mapError .pbkdf2
  | .scrypt n r p length salt =>
    if length < 32 then .error (.shortKey length)
    else (Hash.Scrypt.scrypt password salt n r p length).mapError .scrypt

/-- SHA-256 of key bytes 16 through 31 followed by the ciphertext ("Password verification"). -/
def passwordChecksum (key message : ByteArray) : Vector UInt8 32 :=
  -- Steps 0 and 1: `DK_slice = decryption_key[16:32]`, `pre_image = DK_slice | cipher_message`.
  --
  -- Step 2: `checksum = SHA256(pre_image)`.
  Hash.Sha256.hash32 (key.extract 16 32 ++ message)

/-- The AES-128 key: the first 16 bytes of a derived key of 32 bytes or more. -/
def aesKey (key : ByteArray) (h : 32 ≤ key.size) : Aes.Key .aes128 :=
  Vector.ofFn fun i => key[i.val]'(by
    change i.val < key.data.size
    change 32 ≤ key.data.size at h
    have hi : i.val < 16 := by simpa [Aes.KeySize.Nk] using i.isLt
    omega)

/-- Verify the checksum before AES-128-CTR decryption ("Secret decryption").

A longer key is truncated to its first 16 bytes for AES.
-/
def decryptWithKey (store : Store) (key : ByteArray) : Except KeystoreError ByteArray := do
  if h : 32 ≤ key.size then
    -- Password verification, steps 3 and 4: `valid_password = checksum == checksum_message`.
    if passwordChecksum key store.message != store.checksum then
      throw .checksumMismatch
    -- Secret decryption: AES-128-CTR under the first 16 bytes of `decryption_key`.
    --
    -- Departure: ERC-2335 cites RFC 3686, but its `iv` is the whole 16-byte first counter block.
    --
    -- So this runs SP 800-38A §6.5, with the increment of Appendix B.1 over `m = 128` bits.
    return Aes.ctr (Aes.ciph .aes128 (aesKey key h)) 128 store.iv store.message
  else throw (.shortKey key.size)

/-- Prepare the password, check the caller's limits, then decrypt a parsed keystore. -/
def decryptStore (limits : KdfLimits) (store : Store) (password : String) :
    Except KeystoreError ByteArray := do
  -- Password requirements: NFKD, control codes stripped, UTF-8.
  let password := passwordBytes password
  -- Not in ERC-2335: the caller's bounds on the cost of the KDF, checked before it runs.
  unless limits.admits password.size store.kdf do
    throw (.limitExceeded store.kdf.memory (store.kdf.work password.size))
  -- Decryption key, then password verification and secret decryption.
  decryptWithKey store (← deriveKey password store.kdf)

/-- Decrypt an ERC-2335 keystore value, or report the step that failed.

The decrypted octets are returned without assuming a key length or authenticating metadata.
-/
def decrypt (limits : KdfLimits) (value : Json) (password : String) :
    Except KeystoreError ByteArray := do
  decryptStore limits (← readStore value) password

/-! ## Writing a keystore -/

/-- Bytes as lowercase hex digits with no prefix, as ERC-2335 writes them. -/
def hexText (data : List UInt8) : String :=
  String.ofList (data.flatMap Base.byteHexDigits)

/-- A UUID in the text form of RFC 4122 §3, with lowercase digits. -/
def uuidText (uuid : Vector UInt8 16) : String :=
  let group (start count : Nat) := hexText ((uuid.toList.drop start).take count)
  group 0 4 ++ "-" ++ group 4 2 ++ "-" ++ group 6 2 ++ "-" ++ group 8 2 ++ "-" ++ group 10 6

/-- A module of ERC-2335: its function, its parameters and its message ("Modules"). -/
def moduleJson (function : String) (params : List (String × Json)) (message : String) : Json :=
  Json.mkObj [("function", .str function), ("params", Json.mkObj params),
    ("message", .str message)]

/-- The key derivation module, with an empty message ("Modules"). -/
def Kdf.toJson : Kdf → Json
  | .pbkdf2 iterations length salt =>
    moduleJson "pbkdf2" [("dklen", Lean.toJson length), ("c", Lean.toJson iterations),
      ("prf", .str "hmac-sha256"), ("salt", .str (hexText salt.toList))] ""
  | .scrypt n r p length salt =>
    moduleJson "scrypt" [("dklen", Lean.toJson length), ("n", Lean.toJson n),
      ("p", Lean.toJson p), ("r", Lean.toJson r), ("salt", .str (hexText salt.toList))] ""

/-- The metadata fields of a keystore, with the version ("JSON schema").

A path that is not known is the empty string.

A missing public key or description is left out.
-/
def Metadata.fields (metadata : Metadata) : List (String × Json) :=
  metadata.description.toList.map (fun text => ("description", .str text)) ++
    metadata.pubkey.toList.map (fun pubkey => ("pubkey", .str (hexText pubkey.toList))) ++
    [("path", .str (metadata.path.elim "" Bls.KeyPath.Path.toString)),
      ("uuid", .str (uuidText metadata.uuid)), ("version", Lean.toJson (4 : Nat))]

/-- Write an ERC-2335 keystore that holds a secret under a password.

The salt is part of the key derivation, and the IV and the UUID are inputs.

So writing is a function, and every random value comes from the caller.

The key is derived from the prepared password, then the secret is encrypted with AES-128-CTR.

The checksum is SHA-256 of key bytes 16 through 31 and the ciphertext, as decryption checks it.

It runs the key derivation at any cost, so the caller chooses its parameters.

ERC-2335 requires the public key when the secret is a private key, and the caller supplies it.
-/
def encrypt (kdf : Kdf) (iv : Aes.Block) (metadata : Metadata) (password : String)
    (secret : ByteArray) : Except KeystoreError Json := do
  -- Decryption key: the KDF of the prepared password.
  let key ← deriveKey (passwordBytes password) kdf
  if h : 32 ≤ key.size then
    -- Secret decryption, run forward: CTR mode is its own inverse.
    let message := Aes.ctr (Aes.ciph .aes128 (aesKey key h)) 128 iv secret
    -- The checksum module holds `SHA256(decryption_key[16:32] | cipher_message)`.
    return Json.mkObj ([("crypto", Json.mkObj [
      ("kdf", kdf.toJson),
      ("checksum", moduleJson "sha256" [] (hexText (passwordChecksum key message).toList)),
      ("cipher", moduleJson "aes-128-ctr" [("iv", .str (hexText iv.toList))]
        (hexText message.toList))])] ++ metadata.fields)
  else throw (.shortKey key.size)

/-- Whether the stored public key is that of the secret, read as a BLS secret key.

ERC-2335 requires the field when the secret is a private key, so a keystore without it fails.

A secret that is not a BLS secret key fails too.

[ERC-2335, PubKey][pubkey] defines the field.

[pubkey]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2335.md#pubkey
-/
def checkPubkey (secret : ByteArray) (metadata : Metadata) : Bool :=
  match metadata.pubkey, Bls.Signatures.SecretKey.fromBytes secret with
  | some pubkey, .ok key => pubkey == Bls.Signatures.skToPk key
  | _, _ => false

end EthLib.Cryptography.Keystore
