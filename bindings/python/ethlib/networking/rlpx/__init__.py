"""The RLPx transport of devp2p: ECIES encryption and the handshake."""

from ...errors import RlpxError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

# The secrets of a session: aes-secret, mac-secret, and the egress and ingress MAC digests.
SECRETS_SIZE = 128


def ecies_encrypt(
    recipient: bytes, ephemeral: bytes, iv: bytes, shared_mac: bytes, message: bytes
) -> bytes:
    """The ciphertext R || iv || c || d of a message to a SEC 1 public key."""
    return _native.rlpx_ecies_encrypt(recipient, ephemeral, iv, shared_mac, message)


def ecies_decrypt(key: bytes, shared_mac: bytes, ciphertext: bytes) -> bytes:
    """The message of a ciphertext under a 32-byte private key."""
    return _native.rlpx_ecies_decrypt(key, shared_mac, ciphertext)


def make_auth(
    static_key: bytes,
    ephemeral_key: bytes,
    nonce: bytes,
    recipient: bytes,
    r: bytes,
    iv: bytes,
    padding: bytes,
) -> bytes:
    """The packet auth from the initiator to the recipient's SEC 1 public key."""
    return _native.rlpx_make_auth(static_key, ephemeral_key, nonce, recipient, r, iv, padding)


def respond(
    static_key: bytes,
    ephemeral_key: bytes,
    nonce: bytes,
    r: bytes,
    iv: bytes,
    padding: bytes,
    auth: bytes,
    probe: bytes,
) -> tuple[bytes, bytes]:
    """The recipient's packet ack and its secrets, with the MAC digests after `probe`."""
    out = _native.rlpx_respond(static_key, ephemeral_key, nonce, r, iv, padding, auth, probe)
    return out[:-SECRETS_SIZE], out[-SECRETS_SIZE:]


def recipient_secrets(
    static_key: bytes, ephemeral_key: bytes, nonce: bytes, auth: bytes, ack: bytes, probe: bytes
) -> bytes:
    """The recipient's secrets for an auth it received and an ack it sent."""
    return _native.rlpx_recipient_secrets(static_key, ephemeral_key, nonce, auth, ack, probe)


def finish(
    static_key: bytes, ephemeral_key: bytes, nonce: bytes, auth: bytes, ack: bytes, probe: bytes
) -> bytes:
    """The initiator's secrets for its auth and the ack it received."""
    return _native.rlpx_finish(static_key, ephemeral_key, nonce, auth, ack, probe)


__all__ = [
    "SECRETS_SIZE",
    "RlpxError",
    "ecies_encrypt",
    "ecies_decrypt",
    "make_auth",
    "respond",
    "recipient_secrets",
    "finish",
]
