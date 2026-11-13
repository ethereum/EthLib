"""QUIC v1 packet key derivation from RFC 9001 Appendix A.1 and A.5."""

import pytest

from ethlib.networking import quic
from raising import raises


def test_initial_keys() -> None:
    # RFC 9001 Appendix A.1 gives both directions for this destination connection ID.
    client, server = quic.initial_secrets(bytes.fromhex("8394c8f03e515708"))
    assert client.hex() == "c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea"
    assert server.hex() == "3c199828fd139efd216c155ad844cc81fb82fa8d7446fa7d78be803acdda951b"
    assert quic.packet_keys("TLS_AES_128_GCM_SHA256", client) == tuple(
        bytes.fromhex(value)
        for value in (
            "1f369613dd76d5467730efcbe3b1a22d",
            "fa044b2f42a3fd3b46fb255c",
            "9f50449e04a0e810283a1e9933adedd2",
        )
    )
    assert quic.packet_keys("TLS_AES_128_GCM_SHA256", server) == tuple(
        bytes.fromhex(value)
        for value in (
            "cf3a5331653c364c88f0f379b6067e37",
            "0ac1493ca1905853b0bba03e",
            "c206b8d9b9f0f37644430b490eeaa314",
        )
    )


def test_chacha_keys() -> None:
    # RFC 9001 Appendix A.5 gives these keys for its application traffic secret.
    secret = bytes.fromhex("9ac312a7f877468ebe69422748ad00a15443f18203a07d6060f688f30f21632b")
    assert quic.packet_keys("TLS_CHACHA20_POLY1305_SHA256", secret) == tuple(
        bytes.fromhex(value)
        for value in (
            "c6d98ff3441c3fe1b2182094f69caa2ed4b716b65488960a7a984979fb23e1c8",
            "e0459b3474bdd0e44a41c144",
            "25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4",
        )
    )


@pytest.mark.parametrize(
    ("label", "length", "expected"),
    [
        (b"client in", 32, "00200f746c73313320636c69656e7420696e00"),
        (b"server in", 32, "00200f746c7331332073657276657220696e00"),
        (b"quic key", 16, "00100e746c7331332071756963206b657900"),
        (b"quic iv", 12, "000c0d746c733133207175696320697600"),
        (b"quic hp", 16, "00100d746c733133207175696320687000"),
    ],
)
def test_labels(label: bytes, length: int, expected: str) -> None:
    assert quic.hkdf_label(label, b"", length) == bytes.fromhex(expected)


def test_label_bounds() -> None:
    # RFC 8446 §7.1 gives the field widths; RFC 5869 §2.3 limits SHA-256 to 8160 bytes.
    for label in (b"", b"x" * 250):
        with raises(
            quic.Tls13Error, f"EthLib.Cryptography.Hash.Tls13.Error.labelLength {len(label)}"
        ):
            quic.hkdf_label(label, b"", 32)
    with raises(quic.Tls13Error, "EthLib.Cryptography.Hash.Tls13.Error.contextLength 256"):
        quic.hkdf_label(b"x", bytes(256), 32)
    with raises(quic.Tls13Error, "EthLib.Cryptography.Hash.Tls13.Error.lengthOverflow 65536"):
        quic.hkdf_label(b"x", b"", 65536)
    assert len(quic.hkdf_label(b"x" * 249, bytes(255), 65535)) == 514
    assert quic.expand_label(bytes(32), b"x", b"", 0) == b""
    assert len(quic.expand_label(bytes(32), b"x", b"", 8160)) == 8160
    with raises(
        quic.Tls13Error,
        "EthLib.Cryptography.Hash.Tls13.Error.hkdf "
        "(EthLib.Cryptography.Hash.Hkdf.HkdfError.outputTooLong 8161)",
    ):
        quic.expand_label(bytes(32), b"x", b"", 8161)


def test_unknown_suite() -> None:
    with raises(quic.Tls13Error, "unsupported QUIC key derivation suite"):
        quic.packet_keys("unknown", bytes(32))


@pytest.mark.parametrize("size", [0, 31, 33])
def test_secret_length(size: int) -> None:
    with raises(quic.Tls13Error, f"expected 32 bytes, got {size}") as error:
        quic.packet_keys("TLS_AES_128_GCM_SHA256", bytes(size))
    assert error.value.code == 0
