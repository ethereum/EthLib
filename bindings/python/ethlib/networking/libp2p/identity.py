"""secp256k1 libp2p identities: the public-key protobuf and its identity-multihash peer ID."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import Libp2pIdentityError as Libp2pIdentityError


def public_key(secret: bytes) -> bytes:
    """The public-key protobuf of a 32-byte big-endian secret in [1, n), n the group order."""
    return _native.libp2p_public_key(secret)


def peer_id(key: bytes) -> bytes:
    """The peer ID of a canonical 37-byte secp256k1 public-key protobuf."""
    return _native.libp2p_peer_id(key)


def decode_peer_id(identifier: bytes) -> bytes:
    """The public-key protobuf that a binary secp256k1 peer ID names."""
    return _native.libp2p_decode_peer_id(identifier)


__all__ = ["Libp2pIdentityError", "decode_peer_id", "peer_id", "public_key"]
