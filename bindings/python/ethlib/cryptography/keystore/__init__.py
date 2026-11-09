"""ERC-2335 keystore decryption and its Unicode password preparation."""

from ethlib.cryptography import _native
from ethlib.errors import KeystoreError


def nfkd(text: str) -> str:
    """Normalize text with Unicode 16.0.0 NFKD."""
    return _native.keystore_nfkd(text)


def password_bytes(password: str) -> bytes:
    """Normalize a password, strip controls and encode UTF-8 as ERC-2335 requires."""
    return _native.keystore_password(password)


def decrypt(keystore: str, password: str) -> bytes:
    """Decrypt ERC-2335 JSON text, or raise the error of the step that failed."""
    return _native.keystore_decrypt(keystore, password)


__all__ = ["nfkd", "password_bytes", "decrypt", "KeystoreError"]
