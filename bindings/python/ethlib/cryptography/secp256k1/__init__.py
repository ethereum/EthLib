"""secp256k1 ECDSA, as Ethereum uses it.

- A public key is either SEC 1 encoding: 33 bytes compressed, or 65 bytes uncompressed.
- A hash is 32 bytes.
- A signature is 64 bytes: r then s, each a 32-byte big-endian integer.

Arguments that are not bytes raise TypeError.
Inputs the spec rejects raise Secp256k1Error, a ValueError with the code of the Lean error.
"""

from ethlib.cryptography._native import (
    SECP256K1_HASH_LEN as HASH_LEN,
    SECP256K1_SIGNATURE_LEN as SIGNATURE_LEN,
    secp256k1_address,
    secp256k1_ecdh,
    secp256k1_is_low_s,
    secp256k1_recover,
    secp256k1_sign,
    secp256k1_verify,
)
from ethlib.errors import Secp256k1Error


def verify(public_key: bytes, msg_hash: bytes, signature: bytes) -> bool:
    """Whether the signature on the hash is valid under the public key, by SEC 1 v2 §4.1.4.

    It accepts a high s, as ECDSA does.
    """
    return secp256k1_verify(public_key, msg_hash, signature)


def is_low_s(signature: bytes) -> bool:
    """Whether s is at most n / 2, the rule EIP-2 sets for transactions."""
    return secp256k1_is_low_s(signature)


def recover(msg_hash: bytes, signature: bytes, recovery_id: int) -> bytes:
    """The public key that signed the hash, by SEC 1 v2 §4.1.6, as 65 uncompressed bytes.

    The recovery id is 0 or 1: the parity of the y of the signer's point R.
    A signature with no key for that id raises Secp256k1Error.
    """
    return secp256k1_recover(msg_hash, signature, recovery_id)


def sign(private_key: bytes, msg_hash: bytes) -> bytes:
    """The 65-byte signature `r || s || v` of a hash, by RFC 6979 with the low `s` of EIP-2."""
    return secp256k1_sign(private_key, msg_hash)


def ecdh(private_key: bytes, public_key: bytes) -> bytes:
    """The 32-byte ECDH shared secret of SEC 1 v2 §3.3.1, the `x` of `d Q`."""
    return secp256k1_ecdh(private_key, public_key)


def address(private_key: bytes) -> bytes:
    """The 20-byte Ethereum address of a private key."""
    return secp256k1_address(private_key)


__all__ = [
    "verify",
    "is_low_s",
    "recover",
    "sign",
    "ecdh",
    "address",
    "HASH_LEN",
    "SIGNATURE_LEN",
    "Secp256k1Error",
]
