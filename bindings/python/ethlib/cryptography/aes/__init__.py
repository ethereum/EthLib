"""AES with a 16-byte or 32-byte key, alone and in the CTR and GCM modes."""

from ...errors import AesError
from .._native import (
    aes_ctr,
    aes_decrypt_block,
    aes_encrypt_block,
    aes_gcm_decrypt,
    aes_gcm_encrypt,
)


def encrypt_block(key: bytes, block: bytes) -> bytes:
    """The forward cipher of FIPS 197 on one 16-byte block."""
    return aes_encrypt_block(key, block)


def decrypt_block(key: bytes, block: bytes) -> bytes:
    """The inverse cipher of FIPS 197 on one 16-byte block."""
    return aes_decrypt_block(key, block)


def ctr(key: bytes, initial_counter: bytes, data: bytes) -> bytes:
    """CTR mode of SP 800-38A, which both encrypts and decrypts."""
    return aes_ctr(key, initial_counter, data)


def gcm_encrypt(key: bytes, iv: bytes, plaintext: bytes, aad: bytes, tag_length: int = 16) -> bytes:
    """GCM authenticated encryption of SP 800-38D: the ciphertext, then the tag."""
    return aes_gcm_encrypt(key, iv, plaintext, aad, tag_length)


def gcm_decrypt(
    key: bytes, iv: bytes, ciphertext: bytes, aad: bytes, tag: bytes, tag_length: int = 16
) -> bytes:
    """GCM authenticated decryption of SP 800-38D, which raises `AesError` on a wrong tag."""
    return aes_gcm_decrypt(key, iv, ciphertext, aad, tag, tag_length)


__all__ = ["AesError", "encrypt_block", "decrypt_block", "ctr", "gcm_encrypt", "gcm_decrypt"]
