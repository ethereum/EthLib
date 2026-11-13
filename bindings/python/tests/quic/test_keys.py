"""QUIC v1 Initial secrets and packet keys against RFC 9001 Appendix A.1 and A.5."""

import pytest

from ethlib.cryptography.kdf import hkdf_extract, tls13_expand_label
from ethlib.networking import quic
from raising import raises

# RFC 9001 Appendix A.1: the client's Destination Connection ID and the secrets it gives.
DCID = bytes.fromhex("8394c8f03e515708")
INITIAL_SALT = bytes.fromhex("38762cf7f55934b34d179ae6a4c80cadccbb7f0a")
INITIAL_SECRET = "7db5df06e7a69e432496adedb00851923595221596ae2ae9fb8115c1e9ed0a44"
CLIENT_SECRET = "c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea"
SERVER_SECRET = "3c199828fd139efd216c155ad844cc81fb82fa8d7446fa7d78be803acdda951b"

# RFC 9001 Appendix A.1 and A.5: a secret, its suite, then its key, IV and header-protection key.
PACKET_KEYS: list[tuple[str, quic.CipherSuite, tuple[str, str, str]]] = [
    (
        CLIENT_SECRET,
        "TLS_AES_128_GCM_SHA256",
        (
            "1f369613dd76d5467730efcbe3b1a22d",
            "fa044b2f42a3fd3b46fb255c",
            "9f50449e04a0e810283a1e9933adedd2",
        ),
    ),
    (
        SERVER_SECRET,
        "TLS_AES_128_GCM_SHA256",
        (
            "cf3a5331653c364c88f0f379b6067e37",
            "0ac1493ca1905853b0bba03e",
            "c206b8d9b9f0f37644430b490eeaa314",
        ),
    ),
    (
        "9ac312a7f877468ebe69422748ad00a15443f18203a07d6060f688f30f21632b",
        "TLS_CHACHA20_POLY1305_SHA256",
        (
            "c6d98ff3441c3fe1b2182094f69caa2ed4b716b65488960a7a984979fb23e1c8",
            "e0459b3474bdd0e44a41c144",
            "25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4",
        ),
    ),
]


def test_initial_secret() -> None:
    # The extraction step of RFC 9001 §5.2, which the Initial secrets expand.
    assert hkdf_extract(INITIAL_SALT, DCID) == bytes.fromhex(INITIAL_SECRET)


@pytest.mark.parametrize("dcid", [DCID, b"", bytes(20)])
def test_initial_secrets_compose(dcid: bytes) -> None:
    # RFC 9001 §5.2 expands the extracted secret with "client in" and "server in".
    # RFC 9000 §17.2 allows connection IDs of 0 to 20 bytes.
    initial = hkdf_extract(INITIAL_SALT, dcid)
    assert quic.initial_secrets(dcid) == (
        tls13_expand_label(initial, b"client in", b"", 32),
        tls13_expand_label(initial, b"server in", b"", 32),
    )


def test_initial_secrets() -> None:
    assert quic.initial_secrets(DCID) == (
        bytes.fromhex(CLIENT_SECRET),
        bytes.fromhex(SERVER_SECRET),
    )


@pytest.mark.parametrize(("secret", "suite", "keys"), PACKET_KEYS)
def test_packet_keys(secret: str, suite: quic.CipherSuite, keys: tuple[str, str, str]) -> None:
    expected = tuple(bytes.fromhex(key) for key in keys)
    assert quic.packet_keys(suite, bytes.fromhex(secret)) == expected


def test_unknown_suite() -> None:
    suite: str = "TLS_AES_256_GCM"
    expected = (
        "expected TLS_AES_128_GCM_SHA256 or TLS_CHACHA20_POLY1305_SHA256, got TLS_AES_256_GCM"
    )
    with raises(quic.Tls13Error, expected) as error:
        # The runtime check of the suite is under test, so the call bypasses its type.
        quic.packet_keys(suite, bytes(32))  # ty: ignore[invalid-argument-type]
    assert error.value.code == 0


@pytest.mark.parametrize("size", [0, 31, 33])
def test_secret_length(size: int) -> None:
    with raises(quic.Tls13Error, f"expected 32 bytes, got {size}") as error:
        quic.packet_keys("TLS_AES_128_GCM_SHA256", bytes(size))
    assert error.value.code == 0
