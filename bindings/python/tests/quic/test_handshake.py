"""TLS handshake wire layouts of RFC 8446, with the RFC 8448 §3 trace."""

import pytest

from ethlib.networking.quic import tls
from raising import raises

from .test_tls import CLIENT_HELLO, SERVER_FLIGHT, SERVER_HELLO

# Source: RFC 8446 §§4.1.2, 4.1.3, 4.3.1, 4.3.2 and 4.4.2–4.4.4.
# These small layouts are derived by hand from the field widths and bounds.
# They pin wire syntax, with opaque certificate and signature bytes, rather than authentication.
VERSIONS: tls.Extension = {"kind": 43, "data": [2, 3, 4]}
SELECTED_VERSION: tls.Extension = {"kind": 43, "data": [3, 4]}
PARAMETERS: tls.Extension = {"kind": 57, "data": []}
SIGNATURES: tls.Extension = {"kind": 13, "data": [0, 2, 4, 3]}
SMALL_CLIENT: tls.ClientHello = {
    "random": bytes(32),
    "legacy_session_id": [],
    "cipher_suites": [0x1301],
    "extensions": [VERSIONS, PARAMETERS],
}
SMALL_SERVER: tls.ServerHello = {
    "random": bytes(32),
    "legacy_session_id_echo": [],
    "cipher_suite": 0x1301,
    "extensions": [SELECTED_VERSION],
}
MESSAGES: list[tuple[tls.Message, str]] = [
    (
        ("client_hello", SMALL_CLIENT),
        "010000360303" + "00" * 32 + "00000213010100000b002b000302030400390000",
    ),
    (
        ("server_hello", SMALL_SERVER),
        "0200002e0303" + "00" * 32 + "001301000006002b00020304",
    ),
    (("encrypted_extensions", []), "080000020000"),
    (
        ("certificate_request", {"context": [], "extensions": [SIGNATURES]}),
        "0d00000b000008000d000400020403",
    ),
    (("certificate", {"context": [], "entries": []}), "0b00000400000000"),
    (
        (
            "certificate",
            {"context": [], "entries": [{"data": [0xAA, 0xBB], "extensions": []}]},
        ),
        "0b00000b00000007000002aabb0000",
    ),
    (("certificate_verify", 0x0403, [0xAB]), "0f00000504030001ab"),
    (("finished", [0] * 32), "14000020" + "00" * 32),
]


@pytest.mark.parametrize(("message", "encoded"), MESSAGES)
def test_message_layout(message: tls.Message, encoded: str) -> None:
    data = bytes.fromhex(encoded)
    assert tls.encode_message(32, message) == data
    assert tls.decode_message(32, data + b"next") == (message, b"next")


@pytest.mark.parametrize(("message", "encoded"), MESSAGES)
def test_incomplete_envelope(message: tls.Message, encoded: str) -> None:
    # Every proper prefix lacks bytes promised by the outer handshake length.
    data = bytes.fromhex(encoded)
    for cut in range(len(data)):
        with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.truncated"):
            tls.decode_message(32, data[:cut])


@pytest.mark.parametrize(
    ("payload", "kind", "encoded"),
    [
        (("supported_versions", [0x0304, 0x7A7A]), 43, "0403047a7a"),
        (("selected_version", 0x0304), 43, "0304"),
        (("supported_groups", [0x001D, 0x0017, 0xAAAA]), 10, "0006001d0017aaaa"),
        (("signature_algorithms", [0x0403, 0x0804]), 13, "000404030804"),
        (("client_key_share", []), 51, "0000"),
        (
            ("client_key_share", [{"group": 0x001D, "key_exchange": [0xAB]}]),
            51,
            "0005001d0001ab",
        ),
        (("server_key_share", {"group": 0x0017, "key_exchange": [0xAB]}), 51, "00170001ab"),
        (("retry_key_share", 0x0017), 51, "0017"),
        (("alpn", [[108, 105, 98, 112, 50, 112], [0xFF]]), 16, "0009066c696270327001ff"),
        (("quic_transport_parameters", [1, 0]), 57, "0100"),
    ],
)
def test_extension_payload(payload: tls.Payload, kind: int, encoded: str) -> None:
    # Sources: RFC 8446 §§4.2.1, 4.2.3, 4.2.7, 4.2.8; RFC 7301 §3.1; RFC 9001 §8.2.
    extension: tls.Extension = {"kind": kind, "data": list(bytes.fromhex(encoded))}
    assert tls.encode_payload(payload) == extension
    assert tls.decode_payload(payload[0], extension) == payload


@pytest.mark.parametrize(
    "payload",
    [
        ("supported_versions", []),
        ("supported_versions", [0x0304] * 128),
        ("supported_groups", []),
        ("signature_algorithms", []),
        ("alpn", []),
        ("alpn", [[]]),
        ("alpn", [[0] * 256]),
        ("server_key_share", {"group": 0x0017, "key_exchange": []}),
        ("quic_transport_parameters", [0] * 65536),
    ],
)
def test_payload_length_rejected(payload: tls.Payload) -> None:
    with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.length"):
        tls.encode_payload(payload)


@pytest.mark.parametrize(
    ("form", "kind", "data", "error"),
    [
        ("supported_versions", 43, "03030400", "truncated"),
        ("supported_versions", 43, "00", "length"),
        ("supported_groups", 10, "000100", "length"),
        ("signature_algorithms", 13, "0003040300", "truncated"),
        ("selected_version", 43, "030400", "trailing"),
        ("selected_version", 10, "0304", "constant"),
        ("server_key_share", 51, "00170000", "length"),
        ("client_key_share", 51, "000100", "truncated"),
        ("alpn", 16, "00020000", "length"),
        ("alpn", 16, "0003016162", "truncated"),
    ],
)
def test_bad_payload(form: tls.PayloadForm, kind: int, data: str, error: str) -> None:
    with raises(tls.TlsHandshakeError, f"EthLib.Networking.Quic.Tls.Wire.Error.{error}"):
        tls.decode_payload(form, {"kind": kind, "data": list(bytes.fromhex(data))})


@pytest.mark.parametrize(
    ("encoded", "error"),
    [
        ("080000030000aa", "trailing"),
        ("080000030001aa", "length"),
        ("0800000a00080039000000390000", "duplicateExtension"),
        ("0b000009000000050000000000", "length"),
        ("ff000000", "messageType"),
        # A peer cannot send the transcript's synthetic message_hash (§4.4.1).
        ("fe000020" + "00" * 32, "messageType"),
        ("1400001f" + "00" * 31, "length"),
        ("14000021" + "00" * 33, "trailing"),
    ],
)
def test_bad_message(encoded: str, error: str) -> None:
    with raises(tls.TlsHandshakeError, f"EthLib.Networking.Quic.Tls.Wire.Error.{error}"):
        tls.decode_message(32, bytes.fromhex(encoded))


def test_legacy_constants() -> None:
    data = bytes.fromhex(MESSAGES[0][1])
    # RFC 8446 §4.1.2 fixes legacy_version to 0303 and compression to 01 00.
    for malformed in [data[:5] + b"\x04" + data[6:], data[:44] + b"\x01" + data[45:]]:
        with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.constant"):
            tls.decode_message(32, malformed)


def test_unknown_extensions_keep_their_order() -> None:
    extensions: list[tls.Extension] = [
        {"kind": 0xAAAA, "data": [0xFF, 0]},
        {"kind": 0xBBBB, "data": []},
    ]
    encoded = bytes.fromhex("0800000c000aaaaa0002ff00bbbb0000")
    message: tls.Message = ("encrypted_extensions", extensions)
    assert tls.encode_message(32, message) == encoded
    assert tls.decode_message(32, encoded) == (message, b"")


def test_duplicate_extension_encoding() -> None:
    with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.duplicateExtension"):
        tls.encode_message(32, ("encrypted_extensions", [PARAMETERS, PARAMETERS]))


def test_duplicate_extension_type_with_different_data() -> None:
    # RFC 8446 §4.2 forbids repeated extension types even when their data differs.
    extensions: list[tls.Extension] = [
        {"kind": 0xAAAA, "data": [0xAB]},
        {"kind": 0xAAAA, "data": [0xCD]},
    ]
    error = "EthLib.Networking.Quic.Tls.Wire.Error.duplicateExtension"
    with raises(tls.TlsHandshakeError, error):
        tls.encode_message(32, ("encrypted_extensions", extensions))
    encoded = bytes.fromhex("0800000c000aaaaa0001abaaaa0001cd")
    with raises(tls.TlsHandshakeError, error):
        tls.decode_message(32, encoded)


def test_caller_supplies_finished_hash_length() -> None:
    data = bytes.fromhex("14000030") + bytes(48)
    assert tls.encode_message(48, ("finished", [0] * 48)) == data
    assert tls.decode_message(48, data) == (("finished", [0] * 48), b"")
    with raises(tls.TlsHandshakeError, "EthLib.Networking.Quic.Tls.Wire.Error.length"):
        tls.encode_message(32, ("finished", [0] * 48))


def test_rfc8448_trace() -> None:
    # Source: RFC 8448 §3, the complete messages already pinned in test_tls.py.
    messages = [CLIENT_HELLO, SERVER_HELLO]
    remaining = SERVER_FLIGHT
    kinds = []
    while remaining:
        message, rest = tls.decode_message(32, remaining)
        encoded = remaining[: len(remaining) - len(rest)]
        assert tls.encode_message(32, message) == encoded
        messages.append(encoded)
        kinds.append(message[0])
        remaining = rest
    assert kinds == ["encrypted_extensions", "certificate", "certificate_verify", "finished"]
    for encoded in messages[:2]:
        message, rest = tls.decode_message(32, encoded)
        assert rest == b""
        assert tls.encode_message(32, message) == encoded


def test_hello_retry_request_layout() -> None:
    # Source: RFC 8446 §4.1.3 fixes the retry random and retains the ServerHello layout.
    random = bytes.fromhex("cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c")
    encoded = bytes.fromhex("0200002e0303") + random + bytes.fromhex("001301000006002b00020304")
    message: tls.Message = ("server_hello", {**SMALL_SERVER, "random": random})
    assert tls.encode_message(32, message) == encoded
    assert tls.decode_message(32, encoded) == (message, b"")
