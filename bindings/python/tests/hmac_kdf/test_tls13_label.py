"""TLS 1.3 HkdfLabel and HKDF-Expand-Label against RFC 9001 Appendix A and RFC 8446 §7.1."""

from collections.abc import Callable

import pytest

from ethlib.cryptography.kdf import Tls13Error, tls13_expand_label, tls13_hkdf_label
from raising import raises

# RFC 9001 Appendix A.1 prints these HkdfLabel encodings, each with an empty context.
RFC_9001_LABELS = [
    (b"client in", 32, "00200f746c73313320636c69656e7420696e00"),
    (b"server in", 32, "00200f746c7331332073657276657220696e00"),
    (b"quic key", 16, "00100e746c7331332071756963206b657900"),
    (b"quic iv", 12, "000c0d746c733133207175696320697600"),
    (b"quic hp", 16, "00100d746c733133207175696320687000"),
]

# The ChaCha20-Poly1305 secret of RFC 9001 Appendix A.5 and its key-update secret.
RFC_9001_A5_SECRET = "9ac312a7f877468ebe69422748ad00a15443f18203a07d6060f688f30f21632b"
RFC_9001_A5_KU = "1223504755036d556342ee9361d253421a826c9ecdf3c7148684b36b714881f9"

# The error code of each rejected field, from the binding contract.
LABEL_LENGTH, CONTEXT_LENGTH, LENGTH_OVERFLOW, HKDF = 1, 2, 3, 4

PREFIX = "EthLib.Cryptography.Hash.Tls13.Error"


@pytest.mark.parametrize(("label", "length", "expected"), RFC_9001_LABELS)
def test_rfc_9001_labels(label: bytes, length: int, expected: str) -> None:
    assert tls13_hkdf_label(label, b"", length) == bytes.fromhex(expected)


def test_rfc_9001_key_update() -> None:
    secret = bytes.fromhex(RFC_9001_A5_SECRET)
    assert tls13_expand_label(secret, b"quic ku", b"", 32) == bytes.fromhex(RFC_9001_A5_KU)


def test_largest_fields() -> None:
    # RFC 8446 §7.1: a label of 255 bytes with its prefix, a context of 255 bytes, a uint16 length.
    encoded = tls13_hkdf_label(b"x" * 249, bytes(255), 65535)
    assert encoded == b"\xff\xff\xff" + b"tls13 " + b"x" * 249 + b"\xff" + bytes(255)


def test_output_lengths() -> None:
    # RFC 5869 §2.3 limits HKDF-SHA-256 output to 255 * 32 = 8160 bytes.
    assert tls13_expand_label(bytes(32), b"x", b"", 0) == b""
    assert len(tls13_expand_label(bytes(32), b"x", b"", 8160)) == 8160


@pytest.mark.parametrize(
    ("call", "message", "code"),
    [
        (lambda: tls13_hkdf_label(b"", b"", 32), f"{PREFIX}.labelLength 0", LABEL_LENGTH),
        (lambda: tls13_hkdf_label(b"x" * 250, b"", 32), f"{PREFIX}.labelLength 250", LABEL_LENGTH),
        (
            lambda: tls13_hkdf_label(b"x", bytes(256), 32),
            f"{PREFIX}.contextLength 256",
            CONTEXT_LENGTH,
        ),
        (
            lambda: tls13_hkdf_label(b"x", b"", 65536),
            f"{PREFIX}.lengthOverflow 65536",
            LENGTH_OVERFLOW,
        ),
        (
            lambda: tls13_expand_label(bytes(32), b"x", b"", 8161),
            f"{PREFIX}.hkdf (EthLib.Cryptography.Hash.Hkdf.HkdfError.outputTooLong 8161)",
            HKDF,
        ),
        (
            lambda: tls13_expand_label(bytes(32), b"", b"", 32),
            f"{PREFIX}.labelLength 0",
            LABEL_LENGTH,
        ),
        (lambda: tls13_expand_label(bytes(31), b"x", b"", 32), "expected 32 bytes, got 31", 0),
        (lambda: tls13_expand_label(bytes(33), b"x", b"", 32), "expected 32 bytes, got 33", 0),
    ],
)
def test_rejected(call: Callable[[], bytes], message: str, code: int) -> None:
    with raises(Tls13Error, message) as error:
        call()
    assert error.value.code == code
