module

public import EthLib.Cryptography.Hash.Hkdf
public import EthLib.Cryptography.Hash.ConcatKdf

/-!
# Exports: HMAC-SHA-256 and the key derivations

The C exports of HMAC-SHA-256, HKDF and the Concatenation KDF, for the Python bindings.

HMAC is total, so its export has no `IO` error path.

Each derivation can reject its input, and the C extension turns that error into an exception.

Keys and shared secrets are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

public section

namespace EthLib.Cryptography.Hash.Exports

/-- The 32-byte HMAC-SHA-256 tag of a message under a key, RFC 2104 §2. -/
@[export eth_hmac_sha256]
def hmacSha256 (key message : ByteArray) : ByteArray :=
  EthLib.Cryptography.Hash.Hmac.hmac key message

/-- HKDF-SHA-256 of RFC 5869 §2, with the output length in bytes. -/
@[export eth_hkdf_sha256]
def hkdfSha256 (salt ikm info : ByteArray) (length : UInt64) : IO ByteArray :=
  match EthLib.Cryptography.Hash.Hkdf.hkdf salt ikm info length.toNat with
  | .ok okm => pure okm
  | .error e => throw (IO.userError s!"{repr e}")

/-- The Concatenation KDF of SP 800-56C Rev. 2 §4.1 with SHA-256, the length in bytes. -/
@[export eth_concat_kdf_sha256]
def concatKdfSha256 (z fixedInfo : ByteArray) (length : UInt64) : IO ByteArray :=
  match EthLib.Cryptography.Hash.ConcatKdf.concatKdf z fixedInfo length.toNat with
  | .ok key => pure key
  | .error e => throw (IO.userError s!"{repr e}")

end EthLib.Cryptography.Hash.Exports
