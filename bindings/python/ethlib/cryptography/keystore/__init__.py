"""ERC-2335 keystore decryption and its Unicode password preparation."""

from typing import Final

from ethlib.cryptography import _native
from ethlib.errors import KeystoreError

MAX_MEMORY: Final = 2**30
"""Default memory bound of key derivation, in bytes: four times the ERC-2335 scrypt example."""

MAX_WORK: Final = 2**24
"""Default work bound of key derivation, in core calls: twice the ERC-2335 scrypt example."""


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
