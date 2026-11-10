"""Noise XX published vectors, authenticated libp2p handshakes and malformed messages."""

import hashlib
import json
from pathlib import Path
from types import UnionType
from typing import TypeAlias, get_args, get_origin

import pytest
from py_ecc.secp256k1 import secp256k1 as reference

from ethlib.cryptography.x25519 import x25519_public_key
from ethlib.errors import NoiseError
from ethlib.networking.noise import (
    CipherState,
    Completion,
    HandshakeState,
    Identity,
    Libp2pState,
    Remote,
    cipher_decrypt,
    cipher_encrypt,
    frame,
    initialize,
    libp2p_complete,
    libp2p_initialize,
    libp2p_read,
    libp2p_write,
    read_message,
    transport,
    unframe,
    write_message,
)
from raising import raises

# The two final states of an authenticated handshake, and its three messages.
Exchange: TypeAlias = tuple[Libp2pState, Libp2pState, bytes, bytes, bytes]

# The published XX vector, pinned in tests/sources.toml.
VECTOR_FILE = Path(__file__).parent / "published_vector" / "noise_xx_vector.json"
VECTOR = json.loads(VECTOR_FILE.read_text())["vector"]
ERROR = "EthLib.Networking.Noise.NoiseError."
STATIC_I, EPHEMERAL_I = bytes(range(32)), bytes(range(32, 64))
STATIC_R, EPHEMERAL_R = bytes(range(64, 96)), bytes(range(96, 128))
IDENTITY_I, IDENTITY_R = (1).to_bytes(32, "big"), (2).to_bytes(32, "big")
EXT_I, EXT_R = b"\x12\x05yamux", b"\x0a\x02\x01\x02"
# The compressed public keys of the secrets 1 and 2: the generator G of SEC 2 §2.4.1, and 2G.
IDENTITY_KEY_I = bytes.fromhex("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
IDENTITY_KEY_R = bytes.fromhex("02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5")


def der_integers(signature: bytes) -> tuple[int, int]:
    """The r and s of a DER ECDSA signature, after checking its tags and lengths."""
    assert signature[0] == 0x30
    assert signature[1] + 2 == len(signature)
    assert signature[2] == 0x02
    r_size = signature[3]
    assert signature[4 + r_size] == 0x02
    s_size = signature[5 + r_size]
    assert 6 + r_size + s_size == len(signature)
    r = int.from_bytes(signature[4 : 4 + r_size], "big")
    s = int.from_bytes(signature[6 + r_size :], "big")
    return r, s


def conforms(value: object, alias: object) -> bool:
    """Whether a value has the shape of a type: a tuple, a union or an exact class."""
    if get_origin(alias) is tuple:
        args = get_args(alias)
        return (
            isinstance(value, tuple)
            and len(value) == len(args)
            and all(conforms(item, arg) for item, arg in zip(value, args, strict=True))
        )
    if isinstance(alias, UnionType):
        return any(conforms(value, arg) for arg in get_args(alias))
    return type(value) is alias


def raw_pair() -> tuple[HandshakeState, HandshakeState]:
    return (
        initialize(True, STATIC_I, EPHEMERAL_I, b""),
        initialize(False, STATIC_R, EPHEMERAL_R, b""),
    )


def libp2p_pair() -> tuple[Libp2pState, Libp2pState]:
    return (
        libp2p_initialize(True, STATIC_I, EPHEMERAL_I),
        libp2p_initialize(False, STATIC_R, EPHEMERAL_R),
    )


def test_published_noise_vector() -> None:
    def start(role: str, initiator: bool) -> HandshakeState:
        return initialize(
            initiator,
            bytes.fromhex(VECTOR[f"{role}_static"]),
            bytes.fromhex(VECTOR[f"{role}_ephemeral"]),
            bytes.fromhex(VECTOR[f"{role}_prologue"]),
        )

    initiator, responder = start("init", True), start("resp", False)
    for index, case in enumerate(VECTOR["messages"][:3]):
        payload = bytes.fromhex(case["payload"])
        if index % 2 == 0:
            initiator, message = write_message(initiator, payload)
            responder, received = read_message(responder, message)
        else:
            responder, message = write_message(responder, payload)
            initiator, received = read_message(initiator, message)
        assert message == bytes.fromhex(case["ciphertext"])
        assert received == payload
    send_i, receive_i, hash_i = transport(initiator)
    send_r, receive_r, hash_r = transport(responder)
    assert hash_i == hash_r == bytes.fromhex(VECTOR["handshake_hash"])
    assert send_i == receive_r
    assert send_r == receive_i
    for index, case in enumerate(VECTOR["messages"][3:]):
        payload = bytes.fromhex(case["payload"])
        if index % 2 == 0:
            send_r, ciphertext = cipher_encrypt(send_r, b"", payload)
            receive_i, received = cipher_decrypt(receive_i, b"", ciphertext)
        else:
            send_i, ciphertext = cipher_encrypt(send_i, b"", payload)
            receive_r, received = cipher_decrypt(receive_r, b"", ciphertext)
        assert ciphertext == bytes.fromhex(case["ciphertext"])
        assert received == payload


@pytest.fixture(scope="module")
def exchange() -> Exchange:
    initiator, responder = libp2p_pair()
    initiator, m1 = libp2p_write(initiator, IDENTITY_I, None)
    responder = libp2p_read(responder, m1)
    responder, m2 = libp2p_write(responder, IDENTITY_R, EXT_R)
    initiator = libp2p_read(initiator, m2)
    initiator, m3 = libp2p_write(initiator, IDENTITY_I, EXT_I)
    responder = libp2p_read(responder, m3)
    return initiator, responder, m1, m2, m3


def test_authenticated_exchange(exchange: Exchange) -> None:
    initiator, responder, *_ = exchange
    static_r, identity_r, send_i, receive_i, h_i = libp2p_complete(initiator)
    static_i, identity_i, send_r, receive_r, h_r = libp2p_complete(responder)
    assert h_i == h_r
    assert static_r == x25519_public_key(STATIC_R)
    assert static_i == x25519_public_key(STATIC_I)
    for secret, static, compressed, (key, peer_id, signature, _) in (
        (IDENTITY_I, static_i, IDENTITY_KEY_I, identity_i),
        (IDENTITY_R, static_r, IDENTITY_KEY_R, identity_r),
    ):
        x, y = reference.multiply(reference.G, int.from_bytes(secret, "big"))
        assert compressed == bytes([2 + y % 2]) + x.to_bytes(32, "big")
        assert key == b"\x08\x02\x12\x21" + compressed
        assert peer_id == b"\x00\x25" + key
        r, s = der_integers(signature)
        assert s <= reference.N // 2
        digest = hashlib.sha256(b"noise-libp2p-static-key:" + static).digest()
        signers = [reference.ecdsa_raw_recover(digest, (v, r, s)) for v in (27, 28)]
        assert (x, y) in signers
    assert identity_i[3] == EXT_I
    assert identity_r[3] == EXT_R
    assert send_i == receive_r
    assert send_r == receive_i
    send_i, ciphertext = cipher_encrypt(send_i, b"", b"initiator to responder")
    receive_r, plaintext = cipher_decrypt(receive_r, b"", ciphertext)
    assert plaintext == b"initiator to responder"
    send_r, ciphertext = cipher_encrypt(send_r, b"", b"responder to initiator")
    receive_i, plaintext = cipher_decrypt(receive_i, b"", ciphertext)
    assert plaintext == b"responder to initiator"


def responder_payload(exchange: Exchange) -> bytes:
    initiator, _ = raw_pair()
    initiator, _ = write_message(initiator, b"")
    _, payload = read_message(initiator, exchange[3])
    return payload


def send_modified_payload(payload: bytes, static: bytes = STATIC_R) -> None:
    initiator, responder = libp2p_pair()
    initiator, m1 = libp2p_write(initiator, IDENTITY_I, None)
    raw = initialize(False, static, EPHEMERAL_R, b"")
    raw, _ = read_message(raw, m1)
    _, message = write_message(raw, payload)
    libp2p_read(initiator, message)


def test_signature_binds_received_static(exchange: Exchange) -> None:
    payload = responder_payload(exchange)
    with raises(NoiseError, ERROR + "identity"):
        send_modified_payload(payload, bytes([0x71]) * 32)


@pytest.mark.parametrize("field", ["public_key", "signature"])
def test_identity_tampering(exchange: Exchange, field: str) -> None:
    payload = bytearray(responder_payload(exchange))
    if field == "public_key":
        payload[7] ^= 1
    else:
        # Flip bit 0 of the second byte of r: the DER stays strict and verification fails.
        signature_field = 2 + payload[1]
        start, size = signature_field + 2, payload[signature_field + 1]
        payload[start + 5] ^= 1
        der_integers(bytes(payload[start : start + size]))
    with raises(NoiseError, ERROR + "identity"):
        send_modified_payload(bytes(payload))


@pytest.mark.parametrize("encoding", ["redundant_zero", "high_s", "sighash_flag"])
def test_strict_signature_encoding(exchange: Exchange, encoding: str) -> None:
    payload = responder_payload(exchange)
    signature_field = 2 + payload[1]
    signature_size = payload[signature_field + 1]
    signature = payload[signature_field + 2 : signature_field + 2 + signature_size]
    if encoding == "redundant_zero":
        signature = bytes([0x30, signature[1] + 1, 0x02, signature[3] + 1, 0]) + signature[4:]
    elif encoding == "high_s":
        offset = 4 + signature[3]
        low_s = int.from_bytes(signature[offset + 2 :], "big")
        order = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
        high_s = (order - low_s).to_bytes(33, "big").lstrip(b"\x00")
        if high_s[0] & 0x80:
            high_s = b"\x00" + high_s
        integers = signature[2:offset] + bytes([2, len(high_s)]) + high_s
        signature = bytes([0x30, len(integers)]) + integers
    else:
        signature += b"\x01"
    altered = (
        payload[:signature_field]
        + bytes([0x12, len(signature)])
        + signature
        + payload[signature_field + 2 + signature_size :]
    )
    with raises(NoiseError, ERROR + "identity"):
        send_modified_payload(altered)


@pytest.mark.parametrize("payload", [b"\x00", b"\x0a\x80", b"\x0a\x05x", b"\x4c"])
def test_malformed_protobuf(payload: bytes) -> None:
    with raises(NoiseError, ERROR + "protobuf"):
        send_modified_payload(payload)


def test_unknown_fields_and_field_order(exchange: Exchange) -> None:
    payload = responder_payload(exchange)
    key_end = 2 + payload[1]
    key, rest = payload[:key_end], payload[key_end:]
    signature_end = 2 + rest[1]
    signature, extensions = rest[:signature_end], rest[signature_end:]
    unknown = b"\x48\x01\x51" + bytes(8) + b"\x5a\x01x\x65" + bytes(4)
    group = b"\x6b\x08\x01\x6c"
    send_modified_payload(unknown + extensions + signature + key + group)
    send_modified_payload(b"\x0a\x00" + payload)


def test_first_message_extensions() -> None:
    initiator, responder = libp2p_pair()
    with raises(NoiseError, ERROR + "firstMessageExtensions"):
        libp2p_write(initiator, IDENTITY_I, b"")
    raw, _ = raw_pair()
    _, message = write_message(raw, b"\x22\x00")
    with raises(NoiseError, ERROR + "firstMessageExtensions"):
        libp2p_read(responder, message)
    _, message = write_message(raw, b"\x48\x01")
    libp2p_read(responder, message)


def test_incomplete_and_wrong_order(exchange: Exchange) -> None:
    initiator, responder = libp2p_pair()
    with raises(NoiseError, ERROR + "wrongPhase"):
        libp2p_complete(initiator)
    with raises(NoiseError, ERROR + "wrongPhase"):
        libp2p_write(responder, IDENTITY_R, None)
    initiator, _ = libp2p_write(initiator, IDENTITY_I, None)
    initiator = libp2p_read(initiator, exchange[3])
    with raises(NoiseError, ERROR + "wrongPhase"):
        libp2p_complete(initiator)
    with raises(NoiseError, ERROR + "wrongPhase"):
        libp2p_read(initiator, exchange[3])


@pytest.mark.parametrize("secret", [0, reference.N, 2**256 - 1])
def test_invalid_identity_secret(secret: int) -> None:
    initiator, responder = libp2p_pair()
    _, m1 = libp2p_write(initiator, IDENTITY_I, None)
    responder = libp2p_read(responder, m1)
    with raises(NoiseError, ERROR + "identitySecret") as error:
        libp2p_write(responder, secret.to_bytes(32, "big"), None)
    assert error.value.code == 11


@pytest.mark.parametrize("secret", [0, reference.N, 2**256 - 1])
def test_identity_secret_checked_first(secret: int) -> None:
    initiator, responder = libp2p_pair()
    invalid = secret.to_bytes(32, "big")
    # Message 1 carries no signature, but the secret is checked before the phase and extensions.
    for state, extensions in ((initiator, None), (initiator, b""), (responder, None)):
        with raises(NoiseError, ERROR + "identitySecret") as error:
            libp2p_write(state, invalid, extensions)
        assert error.value.code == 11


def test_state_holds_authenticated_remote(exchange: Exchange) -> None:
    initiator, responder, *_ = exchange
    for state, static, secret in (
        (initiator, STATIC_R, IDENTITY_R),
        (responder, STATIC_I, IDENTITY_I),
    ):
        static_key, identity, *_ = libp2p_complete(state)
        assert state[1] == (static_key, identity[0], identity[2], identity[3])
        assert static_key == x25519_public_key(static)
        x, y = reference.multiply(reference.G, int.from_bytes(secret, "big"))
        assert identity[0] == b"\x08\x02\x12\x21" + bytes([2 + y % 2]) + x.to_bytes(32, "big")


@pytest.mark.parametrize("component", ["missing", "static", "public_key"])
def test_completion_needs_stored_remote(exchange: Exchange, component: str) -> None:
    handshake, remote = exchange[0]
    if component == "missing":
        remote = None
    elif component == "static":
        h = handshake
        handshake = (h[0], h[1], h[2], bytes(32), h[4], h[5], h[6], h[7], h[8], h[9])
    else:
        assert remote is not None
        static_key, public_key, signature, extensions = remote
        # The prefix 05 is not that of a compressed point, so the key protobuf does not decode.
        remote = (static_key, public_key[:4] + b"\x05" + public_key[5:], signature, extensions)
    with raises(NoiseError, ERROR + "savedRemote") as error:
        libp2p_complete((handshake, remote))
    assert error.value.code == 13


@pytest.mark.parametrize("length", [0, 1, 31, 32, 63, 79, 80, 95])
def test_truncated_second_message(exchange: Exchange, length: int) -> None:
    initiator, _ = libp2p_pair()
    initiator, _ = libp2p_write(initiator, IDENTITY_I, None)
    with raises(NoiseError, ERROR + "truncated"):
        libp2p_read(initiator, exchange[3][:length])


def test_cipher_failure_and_nonce() -> None:
    state: CipherState = (bytes(32), 0)
    next_state, ciphertext = cipher_encrypt(state, b"aad", b"message")
    with raises(
        NoiseError,
        ERROR
        + "cipher\n  (EthLib.Cryptography.ChaCha20Poly1305"
        + ".ChaCha20Poly1305Error.authenticationFailed)",
    ):
        cipher_decrypt(state, b"wrong aad", ciphertext)
    recovered, plaintext = cipher_decrypt(state, b"aad", ciphertext)
    assert recovered == next_state
    assert plaintext == b"message"
    final = (bytes(32), (1 << 64) - 2)
    reserved, ciphertext = cipher_encrypt(final, b"", b"last message")
    assert reserved[1] == (1 << 64) - 1
    assert cipher_decrypt(final, b"", ciphertext)[0] == reserved
    with raises(NoiseError, ERROR + "nonceExhausted"):
        cipher_encrypt(reserved, b"", b"")
    with raises(NoiseError, ERROR + "nonceExhausted"):
        cipher_decrypt(reserved, b"", ciphertext)


def test_transport_size_limit() -> None:
    with raises(NoiseError, ERROR + "messageTooLong"):
        cipher_encrypt((bytes(32), 0), b"", bytes(65520))
    with raises(NoiseError, ERROR + "messageTooLong"):
        cipher_decrypt((bytes(32), 0), b"", bytes(65536))
    with raises(NoiseError, ERROR + "messageTooLong"):
        cipher_encrypt((None, 0), b"", bytes(65536))


@pytest.mark.parametrize("size", [0, 1, 255, 256, 65535])
def test_framing(size: int) -> None:
    message = bytes(size)
    assert frame(message) == size.to_bytes(2, "big") + message
    assert unframe(frame(message)) == message


def test_bad_frames() -> None:
    with raises(NoiseError, ERROR + "messageTooLong"):
        frame(bytes(65536))
    with raises(NoiseError, ERROR + "truncated"):
        unframe(b"\x00")
    with raises(NoiseError, ERROR + "frameLength"):
        unframe(b"\x00\x02x")
    with raises(NoiseError, ERROR + "frameLength"):
        unframe(b"\x00\x00x")


def test_values_have_their_alias_types(exchange: Exchange) -> None:
    initiator, responder, *_ = exchange
    assert all(conforms(state, HandshakeState) for state in raw_pair())
    # The initiator writes messages 1 and 3, and the responder message 2.
    states = list(raw_pair())
    for index in range(3):
        writer, reader = index % 2, 1 - index % 2
        written = write_message(states[writer], b"")
        read = read_message(states[reader], written[1])
        assert conforms(written, tuple[HandshakeState, bytes])
        assert conforms(read, tuple[HandshakeState, bytes])
        states[writer], states[reader] = written[0], read[0]
    raw_i, raw_r = states
    send, receive, _ = transport(raw_i)
    assert conforms(transport(raw_i), tuple[CipherState, CipherState, bytes])
    sealed = cipher_encrypt(send, b"", b"x")
    assert conforms(sealed, tuple[CipherState, bytes])
    assert conforms(cipher_decrypt(transport(raw_r)[1], b"", sealed[1]), tuple[CipherState, bytes])
    assert conforms(receive, CipherState)
    for state in (*libp2p_pair(), initiator, responder):
        assert conforms(state, Libp2pState)
    for state in (initiator, responder):
        assert conforms(state[1], Remote)
        completion = libp2p_complete(state)
        assert conforms(completion, Completion)
        assert conforms(completion[1], Identity)
        assert conforms(completion[2], CipherState)
        assert conforms(completion[3], CipherState)
