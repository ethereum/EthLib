"""Noise XX and its authenticated Ethereum libp2p identity profile."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import NoiseError
from ethlib.networking.noise._types import (
    CipherState,
    Completion,
    HandshakeState,
    Identity,
    Libp2pState,
    Remote,
)


def initialize(
    initiator: bool, static_key: bytes, ephemeral_key: bytes, prologue: bytes
) -> HandshakeState:
    """The XX state of one side, with its X25519 private keys and the prologue."""
    return _native.noise_initialize(initiator, static_key, ephemeral_key, prologue)


def write_message(state: HandshakeState, payload: bytes) -> tuple[HandshakeState, bytes]:
    """The state after the next XX message, and that message carrying a payload."""
    return _native.noise_write_message(state, payload)


def read_message(state: HandshakeState, message: bytes) -> tuple[HandshakeState, bytes]:
    """The state after the next XX message, and the payload of that message."""
    return _native.noise_read_message(state, message)


def transport(state: HandshakeState) -> tuple[CipherState, CipherState, bytes]:
    """The send and receive ciphers and the handshake hash of a completed XX state."""
    return _native.noise_transport(state)


def cipher_encrypt(state: CipherState, aad: bytes, plaintext: bytes) -> tuple[CipherState, bytes]:
    """The cipher state after a plaintext, and its ciphertext and tag."""
    return _native.noise_cipher_encrypt(state, aad, plaintext)


def cipher_decrypt(state: CipherState, aad: bytes, ciphertext: bytes) -> tuple[CipherState, bytes]:
    """The cipher state after an authenticated ciphertext, and its plaintext."""
    return _native.noise_cipher_decrypt(state, aad, ciphertext)


def frame(message: bytes) -> bytes:
    """A message prefixed with its 16-bit big-endian length."""
    return _native.noise_frame(message)


def unframe(data: bytes) -> bytes:
    """The message of exactly one complete frame."""
    return _native.noise_unframe(data)


def libp2p_initialize(initiator: bool, static_key: bytes, ephemeral_key: bytes) -> Libp2pState:
    """The libp2p state of one side, with its X25519 private keys and the empty prologue."""
    return _native.noise_libp2p_initialize(initiator, static_key, ephemeral_key)


def libp2p_write(
    state: Libp2pState, identity_secret: bytes, extensions: bytes | None = None
) -> tuple[Libp2pState, bytes]:
    """The state after the next libp2p message, and that message, signed by a 32-byte secret."""
    return _native.noise_libp2p_write(state, identity_secret, extensions)


def libp2p_read(state: Libp2pState, message: bytes) -> Libp2pState:
    """The state after reading and authenticating the next libp2p message."""
    return _native.noise_libp2p_read(state, message)


def libp2p_complete(state: Libp2pState) -> Completion:
    """The authenticated remote, the transport ciphers and the hash after message 3."""
    return _native.noise_libp2p_complete(state)


__all__ = [
    "CipherState",
    "Completion",
    "HandshakeState",
    "Identity",
    "Libp2pState",
    "NoiseError",
    "Remote",
    "cipher_decrypt",
    "cipher_encrypt",
    "frame",
    "initialize",
    "libp2p_complete",
    "libp2p_initialize",
    "libp2p_read",
    "libp2p_write",
    "read_message",
    "transport",
    "unframe",
    "write_message",
]
