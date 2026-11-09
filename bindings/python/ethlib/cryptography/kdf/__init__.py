"""Key derivation with SHA-256: HKDF, the Concatenation KDF, PBKDF2 and scrypt."""

from ethlib.cryptography._native import (
    PBKDF2_HASH_LEN,
    SALSA_BLOCK_SIZE,
    SCRYPT_BLOCK_SIZE,
    concat_kdf_sha256 as native_concat_kdf_sha256,
    hkdf_sha256 as native_hkdf_sha256,
    hmac_sha256 as native_hmac_sha256,
    pbkdf2_sha256 as native_pbkdf2_sha256,
    salsa208 as native_salsa208,
    scrypt as native_scrypt,
    scrypt_block_mix as native_scrypt_block_mix,
    scrypt_romix as native_scrypt_romix,
)
from ethlib.errors import ConcatKdfError, HkdfError, Pbkdf2Error, ScryptError

# The input keying material, the shared secret and the password are secret.
# EthLib makes no constant-time claim.


def hkdf_extract(salt: bytes, ikm: bytes) -> bytes:
    """
    HKDF-Extract of RFC 5869 §2.2: the 32-byte pseudorandom key `HMAC-SHA-256(salt, IKM)`.

    An empty salt gives the same key as 32 zero bytes, the RFC's default.

    A non-`bytes` argument raises `TypeError`.
    """
    return native_hmac_sha256(salt, ikm)


def hkdf(salt: bytes, ikm: bytes, info: bytes, length: int) -> bytes:
    """HKDF-SHA-256 of RFC 5869 §2: `length` bytes of output keying material."""
    return native_hkdf_sha256(salt, ikm, info, length)


def concat_kdf(z: bytes, fixed_info: bytes, length: int) -> bytes:
    """The Concatenation KDF of SP 800-56C Rev. 2 §4.1 with SHA-256: `length` bytes of key."""
    return native_concat_kdf_sha256(z, fixed_info, length)


def pbkdf2(password: bytes, salt: bytes, iterations: int, length: int) -> bytes:
    """PBKDF2-HMAC-SHA-256 of RFC 8018 §5.2: `length` bytes of key."""
    return native_pbkdf2_sha256(password, salt, iterations, length)


def salsa208(block: bytes) -> bytes:
    """The Salsa20/8 core of RFC 7914 §3 on one 64-byte input."""
    return native_salsa208(block)


def scrypt_block_mix(block: bytes, r: int) -> bytes:
    """The scryptBlockMix step of RFC 7914 §4 on a `128 * r`-byte input."""
    return native_scrypt_block_mix(block, r)


def scrypt_romix(block: bytes, n: int, r: int) -> bytes:
    """The scryptROMix step of RFC 7914 §5 with `n` table entries."""
    return native_scrypt_romix(block, n, r)


def scrypt(password: bytes, salt: bytes, n: int, r: int, p: int, length: int) -> bytes:
    """The scrypt derivation of RFC 7914 §6: `length` bytes of key."""
    return native_scrypt(password, salt, n, r, p, length)


__all__ = [
    "PBKDF2_HASH_LEN",
    "SALSA_BLOCK_SIZE",
    "SCRYPT_BLOCK_SIZE",
    "ConcatKdfError",
    "HkdfError",
    "Pbkdf2Error",
    "ScryptError",
    "concat_kdf",
    "hkdf",
    "hkdf_extract",
    "pbkdf2",
    "salsa208",
    "scrypt",
    "scrypt_block_mix",
    "scrypt_romix",
]
