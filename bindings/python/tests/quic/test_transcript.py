"""SHA-256 transcripts and CertificateVerify signed content of RFC 8446 §§4.4.1 and 4.4.3."""

import hashlib

import pytest

from ethlib.networking.quic import tls
from raising import raises

from .test_tls import CLIENT_HELLO, SERVER_FLIGHT, SERVER_HELLO, SERVER_TRANSCRIPT


def test_rfc8448_transcript() -> None:
    # Source: RFC 8448 §3; framing splits its flight into the original complete messages.
    messages = [CLIENT_HELLO, SERVER_HELLO]
    remaining = SERVER_FLIGHT
    while remaining:
        _, rest = tls.decode_message(32, remaining)
        messages.append(remaining[: len(remaining) - len(rest)])
        remaining = rest
    assert tls.transcript(messages) == (
        SERVER_TRANSCRIPT,
        hashlib.sha256(SERVER_TRANSCRIPT).digest(),
    )


def test_unknown_extensions_preserved_in_transcript() -> None:
    # RFC 8446 §§4.2 and 4.4.1: two unknown extension types retain their order and opaque data.
    encoded = bytes.fromhex("0800000c000aaaaa0002ff00bbbb0000")
    assert tls.transcript([encoded]) == (encoded, hashlib.sha256(encoded).digest())


# Source: RFC 8446 §4.1.3, the special ServerHello random identifies HelloRetryRequest.
RETRY_RANDOM = bytes.fromhex("cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c")
RETRY = bytes.fromhex("0200002e0303") + RETRY_RANDOM + bytes.fromhex("001301000006002b00020304")


def test_retry_transcript() -> None:
    # Source: RFC 8446 §4.4.1; hashlib independently computes Hash(ClientHello1).
    synthetic = bytes.fromhex("fe000020") + hashlib.sha256(CLIENT_HELLO).digest()
    expected = synthetic + RETRY + CLIENT_HELLO + SERVER_HELLO
    assert tls.transcript([CLIENT_HELLO, RETRY, CLIENT_HELLO, SERVER_HELLO]) == (
        expected,
        hashlib.sha256(expected).digest(),
    )


@pytest.mark.parametrize("messages", [[RETRY], [SERVER_HELLO, RETRY], [CLIENT_HELLO, RETRY, RETRY]])
def test_misplaced_retry(messages: list[bytes]) -> None:
    with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.retry"):
        tls.transcript(messages)


def test_transcript_requires_complete_separate_messages() -> None:
    with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.trailing"):
        tls.transcript([CLIENT_HELLO + SERVER_HELLO])
    with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.truncated"):
        tls.transcript([CLIENT_HELLO[:-1]])
    assert tls.transcript([]) == (b"", hashlib.sha256(b"").digest())


@pytest.mark.parametrize("server", [False, True])
def test_certificate_verify_signed_content(server: bool) -> None:
    # Source: RFC 8446 §4.4.3 prints the server bytes for this 32-byte transcript hash.
    context = (
        b"TLS 1.3, server CertificateVerify" if server else b"TLS 1.3, client CertificateVerify"
    )
    assert tls.certificate_verify_input(server, bytes([1]) * 32) == (
        b" " * 64 + context + b"\x00" + bytes([1]) * 32
    )
