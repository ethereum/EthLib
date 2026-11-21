module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Hash.Pbkdf2
public import EthLib.Cryptography.Hash.Scrypt

/-!
# Exports: PBKDF2 and scrypt

The password derivations and the RFC 7914 steps, for the Python bindings.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

open EthLib.Exports (Result ExportError toResult)

/-- An error reaches Python with its code, and its message names the error. -/
instance : ExportError Pbkdf2.Pbkdf2Error where
  code := Pbkdf2.Pbkdf2Error.code
  message := fun e => s!"{repr e}"

/-- An error reaches Python with its code, and its message names the error. -/
instance : ExportError Scrypt.ScryptError where
  code := Scrypt.ScryptError.code
  message := fun e => s!"{repr e}"

/-- The output size of HMAC-SHA-256 in PBKDF2, in bytes. -/
@[export eth_pbkdf2_const_hash_len]
def pbkdf2HashLen (_ : Unit) : UInt64 := Pbkdf2.HASH_LEN.toUInt64

/-- The size of one Salsa20/8 input, in bytes. -/
@[export eth_scrypt_const_salsa_block_size]
def scryptSalsaBlockSize (_ : Unit) : UInt64 := Scrypt.SALSA_BLOCK_SIZE.toUInt64

/-- The scrypt block size per unit of `r`, in bytes. -/
@[export eth_scrypt_const_block_size]
def scryptBlockSize (_ : Unit) : UInt64 := Scrypt.BLOCK_SIZE.toUInt64

/-- PBKDF2-HMAC-SHA-256 of RFC 8018 §5.2, with the output length in bytes. -/
@[export eth_pbkdf2_sha256]
def pbkdf2Sha256 (password salt : ByteArray) (iterations length : UInt64) :
    Result ByteArray :=
  toResult none (Pbkdf2.pbkdf2 password salt iterations.toNat length.toNat)

/-- The Salsa20/8 core of RFC 7914 §3. -/
@[export eth_salsa208]
def salsa208 (input : ByteArray) : Result ByteArray :=
  toResult none (Scrypt.salsa208 input)

/-- scryptBlockMix of RFC 7914 §4. -/
@[export eth_scrypt_block_mix]
def scryptBlockMix (input : ByteArray) (r : UInt64) : Result ByteArray :=
  toResult none (Scrypt.blockMix input r.toNat)

/-- scryptROMix of RFC 7914 §5. -/
@[export eth_scrypt_romix]
def scryptRomix (input : ByteArray) (n r : UInt64) : Result ByteArray :=
  toResult none (Scrypt.romix input n.toNat r.toNat)

/-- scrypt of RFC 7914 §6, with the output length in bytes. -/
@[export eth_scrypt]
def scrypt (password salt : ByteArray) (n r p length : UInt64) : Result ByteArray :=
  toResult none (Scrypt.scrypt password salt n.toNat r.toNat p.toNat length.toNat)

end EthLib.Cryptography.Hash.Exports
