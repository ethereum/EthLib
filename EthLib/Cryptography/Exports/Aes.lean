module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Aes

/-!
# Exports: AES

The C exports of AES, CTR and GCM, for the Python bindings.

A key of 16 bytes selects AES-128, and a key of 32 bytes selects AES-256.

A key or a block of another size has code 0, since the export reads it before the specification.

A GCM failure returns the code and the message of its error.

Keys are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

public section

namespace EthLib.Cryptography.Aes.Exports

open EthLib.Cryptography.Aes
open EthLib.Exports (Result ExportError UnreadArgument rejectArgument toResult)

/-- A 16-byte block, or an error for any other length. -/
def readBlock (what : String) (bytes : ByteArray) : Result Block :=
  toResult none (Base.exactBytes 16 bytes fun size =>
    UnreadArgument.mk s!"bad {what} size: {size}, expected 16")

/-- A cipher under a 16-byte or 32-byte key, or an error for any other length. -/
def readCipher (cipher : (k : KeySize) → Key k → Block → Block) (key : ByteArray) :
    Result (Block → Block) :=
  if let some k := Base.exactBytes? 16 key then pure (cipher .aes128 k)
  else if let some k := Base.exactBytes? 32 key then pure (cipher .aes256 k)
  else rejectArgument none s!"bad key size: {key.size}, expected 16 or 32"

/-- An error reaches Python with its code, and its message names the error. -/
instance : ExportError Gcm.Error where
  code := Gcm.Error.code
  message := fun e => s!"{repr e}"

/-- The forward cipher `CIPH_K` of FIPS 197 §5 on one block. -/
@[export eth_aes_encrypt_block]
def encryptBlock (key block : ByteArray) : Result ByteArray := do
  let f ← readCipher ciph key
  return ⟨(f (← readBlock "block" block)).toArray⟩

/-- The inverse cipher `CIPH_K^-1` of FIPS 197 §5 on one block. -/
@[export eth_aes_decrypt_block]
def decryptBlock (key block : ByteArray) : Result ByteArray := do
  let f ← readCipher ciphInv key
  return ⟨(f (← readBlock "block" block)).toArray⟩

/-- CTR encryption or decryption of SP 800-38A §6.5, with the increment over the whole block. -/
@[export eth_aes_ctr]
def ctrExport (key initialCounter data : ByteArray) : Result ByteArray := do
  let f ← readCipher ciph key
  return ctr f 128 (← readBlock "counter" initialCounter) data

/-- GCM-AE of SP 800-38D §7.1: the ciphertext, then the tag of `tagLength` bytes. -/
@[export eth_aes_gcm_encrypt]
def gcmEncrypt (key iv plaintext aad : ByteArray) (tagLength : UInt64) : Result ByteArray := do
  let f ← readCipher ciph key
  let (c, t) ← toResult none (Gcm.encrypt f tagLength.toNat iv plaintext aad)
  return c ++ t

/-- GCM-AD of SP 800-38D §7.2: the plaintext, or an error when the tag does not match.

The tag length belongs to the key, so the caller gives it, and a tag of another length fails. -/
@[export eth_aes_gcm_decrypt]
def gcmDecrypt (key iv ciphertext aad tag : ByteArray) (tagLength : UInt64) :
    Result ByteArray := do
  let f ← readCipher ciph key
  toResult none (Gcm.decrypt f tagLength.toNat iv ciphertext aad tag)

end EthLib.Cryptography.Aes.Exports
