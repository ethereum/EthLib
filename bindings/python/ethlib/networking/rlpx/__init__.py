"""The RLPx transport of devp2p: ECIES encryption.

- A private key is 32 big-endian bytes, below the order of secp256k1.
- A public key is a SEC 1 encoding, compressed or uncompressed.

A rejected input raises RlpxError, a ValueError.
"""

from ...errors import RlpxError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def ecies_encrypt(
    recipient: bytes, ephemeral: bytes, iv: bytes, shared_mac: bytes, message: bytes
) -> bytes:
    """The ciphertext R || iv || c || d of a message to the public key `recipient`.

    The caller picks the ephemeral private key and the 16-byte iv, which must be random.
    The tag d also covers `shared_mac`, which is not part of the ciphertext.
    """
    return _native.rlpx_ecies_encrypt(recipient, ephemeral, iv, shared_mac, message)


def ecies_decrypt(key: bytes, shared_mac: bytes, ciphertext: bytes) -> bytes:
    """The message of a ciphertext under the private key `key`.

    A ciphertext whose tag does not match raises RlpxError.
    """
    return _native.rlpx_ecies_decrypt(key, shared_mac, ciphertext)


__all__ = ["ecies_encrypt", "ecies_decrypt", "RlpxError"]
