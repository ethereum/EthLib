"""ERC-2335 keystore decryption and its Unicode password preparation."""

from ethlib.cryptography import _native
from ethlib.errors import KeystoreError

# Default memory bound of key derivation: 2^30 bytes, about four times the ERC-2335 scrypt example.
MAX_MEMORY = 2**30

# Default work bound of key derivation, in SHA-256 compressions and Salsa20/8 cores of 64 bytes.
# 2^24 is about twice the ERC-2335 scrypt example.
MAX_WORK = 2**24


def nfkd(text: str) -> str:
    """Normalize text with Unicode 16.0.0 NFKD."""
    return _native.keystore_nfkd(text)


def password_bytes(password: str) -> bytes:
    """Normalize a password, strip controls and encode UTF-8 as ERC-2335 requires."""
    return _native.keystore_password(password)


def decrypt(
    keystore: str, password: str, *, max_memory: int = MAX_MEMORY, max_work: int = MAX_WORK
) -> bytes:
    """Decrypt ERC-2335 JSON text within the given KDF bounds, or raise the failed step's error."""
    return _native.keystore_decrypt(keystore, password, max_memory, max_work)


__all__ = ["MAX_MEMORY", "MAX_WORK", "nfkd", "password_bytes", "decrypt", "KeystoreError"]
