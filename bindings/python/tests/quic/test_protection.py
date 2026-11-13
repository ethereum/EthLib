"""QUIC v1 packet protection from RFC 9001 Appendix A.2 to A.5."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography import aes
from ethlib.networking import quic
from raising import raises

AES: quic.CipherSuite = "TLS_AES_128_GCM_SHA256"
CHACHA: quic.CipherSuite = "TLS_CHACHA20_POLY1305_SHA256"
VECTORS = json.loads(Path(__file__).with_name("packet_vectors.json").read_text())


@pytest.mark.parametrize(("direction", "number", "offset"), [("client", 2, 18), ("server", 1, 18)])
def test_initial_packets(direction: str, number: int, offset: int) -> None:
    # RFC 9001 Appendix A.2 and A.3 fix the whole packet, not just its ciphertext prefix.
    client, server = quic.initial_secrets(bytes.fromhex("8394c8f03e515708"))
    secret = client if direction == "client" else server
    vector = VECTORS[direction]
    header = bytes.fromhex(vector["header"])
    if direction == "client":
        crypto = bytes.fromhex(vector["crypto_frame"])
        plaintext = crypto + bytes(vector["plaintext_length"] - len(crypto))
    else:
        plaintext = bytes.fromhex(vector["plaintext"])
    packet = bytes.fromhex(vector["packet"])
    assert quic.protect(AES, secret, number, offset, header, plaintext) == packet
    assert quic.unprotect(AES, secret, 0, offset, packet) == (header, plaintext)
    corrupted = packet[:-1] + bytes([packet[-1] ^ 1])
    with raises(
        quic.QuicProtectionError,
        "EthLib.Networking.Quic.Protection.Error.aes "
        "(EthLib.Cryptography.Aes.Gcm.Error.authentication)",
    ):
        quic.unprotect(AES, secret, 0, offset, corrupted)
    # RFC 9000 §17.2 requires authentication before reporting nonzero reserved bits.
    reserved_bit_changed = bytes([packet[0] ^ 4]) + packet[1:]
    with raises(
        quic.QuicProtectionError,
        "EthLib.Networking.Quic.Protection.Error.aes "
        "(EthLib.Cryptography.Aes.Gcm.Error.authentication)",
    ):
        quic.unprotect(AES, secret, 0, offset, reserved_bit_changed)


def test_chacha_short_packet() -> None:
    # RFC 9001 Appendix A.5 uses a three-byte truncated number and a one-byte PING frame.
    secret = bytes.fromhex("9ac312a7f877468ebe69422748ad00a15443f18203a07d6060f688f30f21632b")
    header = bytes.fromhex("4200bff4")
    packet = bytes.fromhex("4cfe4189655e5cd55c41f69080575d7999c25a5bfb")
    assert quic.protect(CHACHA, secret, 654360564, 1, header, b"\x01") == packet
    assert quic.unprotect(CHACHA, secret, 654360564, 1, packet) == (header, b"\x01")
    # RFC 9001 §5.5 warns that incorrect packet-number reconstruction can fail authentication.
    with raises(
        quic.QuicProtectionError,
        "EthLib.Networking.Quic.Protection.Error.chacha\n"
        "  (EthLib.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305Error.authenticationFailed)",
    ):
        quic.unprotect(CHACHA, secret, 0, 1, packet)


def test_retry_integrity() -> None:
    # RFC 9001 Appendix A.4 authenticates a Retry without carrying the original DCID on the wire.
    dcid = bytes.fromhex("8394c8f03e515708")
    retry = bytes.fromhex("ff000000010008f067a5502a4262b5746f6b656e")
    assert quic.retry_tag(dcid, retry).hex() == "04a265ba2eff4d829058fb3f0f2496ba"


@pytest.mark.parametrize("suite", [AES, CHACHA])
def test_sample_and_header_boundaries(suite: quic.CipherSuite) -> None:
    # RFC 9001 §5.4.2 requires three plaintext bytes for a one-byte encoded number.
    secret = bytes(32)
    with raises(quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.sample"):
        quic.protect(suite, secret, 0, 1, b"\x40\x00", bytes(2))
    packet = quic.protect(suite, secret, 0, 1, b"\x40\x00", bytes(3))
    assert quic.unprotect(suite, secret, 0, 1, packet) == (b"\x40\x00", bytes(3))
    with raises(quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.sample"):
        quic.unprotect(suite, secret, 0, 1, packet[:-1])
    # RFC 9000 §17.3.1 requires the fixed bit and zero reserved bits.
    for header in (b"\x00\x00", b"\x48\x00"):
        with raises(quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.header"):
            quic.protect(suite, secret, 0, 1, header, bytes(3))
    # The truncated number in the header must equal the low byte of the full number.
    with raises(quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.packetNumber"):
        quic.protect(suite, secret, 1, 1, b"\x40\x00", bytes(3))


def test_initial_requires_aes() -> None:
    # RFC 9001 §5 fixes AES-128-GCM for Initial, regardless of the negotiated TLS suite.
    secret = bytes(32)
    header = bytes.fromhex("c0000000010000001400")
    with raises(quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.header"):
        quic.protect(CHACHA, secret, 0, 9, header, bytes(3))
    packet = quic.protect(AES, secret, 0, 9, header, bytes(3))
    assert quic.unprotect(AES, secret, 0, 9, packet) == (header, bytes(3))
    # An Initial with three PADDING bytes, sealed by ChaCha20-Poly1305 under these keys.
    # It authenticates, and the suite check then rejects it.
    forbidden = bytes.fromhex("c700000001000000148005373807da97a14899e58ec96d558d14903ddc")
    with raises(quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.header") as info:
        quic.unprotect(CHACHA, secret, 0, 9, forbidden)
    assert info.value.code == 1
    # A bad tag still fails authentication before the suite check.
    corrupted = forbidden[:-1] + bytes([forbidden[-1] ^ 1])
    with raises(
        quic.QuicProtectionError,
        "EthLib.Networking.Quic.Protection.Error.chacha\n"
        "  (EthLib.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305Error.authenticationFailed)",
    ):
        quic.unprotect(CHACHA, secret, 0, 9, corrupted)


def test_reserved_bits_fail_after_authentication() -> None:
    # A short header with a reserved bit set, sealed directly (RFC 9001 §§5.3, 5.4.3).
    # Authentication succeeds, so the reserved bit is a connection error (RFC 9000 §17.3.1).
    key, iv, hp = quic.packet_keys(AES, bytes(32))
    header = b"\x48\x00"
    sealed = header + aes.gcm_encrypt(key, iv, bytes(3), header)
    mask = aes.encrypt_block(hp, sealed[5:21])
    packet = bytes([sealed[0] ^ (mask[0] & 0x1F), sealed[1] ^ mask[1]]) + sealed[2:]
    message = "EthLib.Networking.Quic.Protection.Error.reservedBits"
    with raises(quic.QuicProtectionError, message) as info:
        quic.unprotect(AES, bytes(32), 0, 1, packet)
    assert info.value.code == 8


def test_unknown_suite() -> None:
    suite: str = "TLS_AES_256_GCM"
    expected = (
        "expected TLS_AES_128_GCM_SHA256 or TLS_CHACHA20_POLY1305_SHA256, got TLS_AES_256_GCM"
    )
    with raises(quic.QuicProtectionError, expected) as info:
        # The runtime check of the suite is under test, so the call bypasses its type.
        quic.unprotect(suite, bytes(32), 0, 1, bytes(21))  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0


def test_number_out_of_range() -> None:
    with raises(
        quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.packetNumber"
    ) as info:
        quic.protect(AES, bytes(32), 2**62, 1, b"\x40\x00", bytes(3))
    assert info.value.code == 3


@pytest.mark.parametrize("offset", [0, 21])
def test_offset_outside_packet(offset: int) -> None:
    with raises(quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.header") as info:
        quic.unprotect(AES, bytes(32), 0, offset, bytes(21))
    assert info.value.code == 1


def test_retry_connection_id_bound() -> None:
    # RFC 9001 §5.8: the Original Destination Connection ID holds at most 160 bits.
    retry = bytes.fromhex("ff000000010008f067a5502a4262b5746f6b656e")
    assert len(quic.retry_tag(bytes(20), retry)) == 16
    with raises(
        quic.QuicProtectionError, "EthLib.Networking.Quic.Protection.Error.connectionId"
    ) as info:
        quic.retry_tag(bytes(21), retry)
    assert info.value.code == 7


def test_retry_tag_binds_original_connection_id() -> None:
    retry = bytes.fromhex("ff000000010008f067a5502a4262b5746f6b656e")
    tag = bytes.fromhex("04a265ba2eff4d829058fb3f0f2496ba")
    assert quic.retry_tag(bytes.fromhex("8394c8f03e515709"), retry) != tag
