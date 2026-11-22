"""TLS handshake wire layouts of RFC 9846, with the RFC 8448 §3 trace."""

import pytest

from ethlib.networking.quic import tls
from raising import raises

from .test_tls import CLIENT_HELLO, SERVER_FLIGHT, SERVER_HELLO

PREFIX = "EthLib.Networking.Quic.Tls.Wire.Error."

# The stable codes of the TLS codec errors, one for each Lean constructor.
CODES = {
    "truncated": 1,
    "length": 2,
    "trailing": 3,
    "constant": 4,
    "duplicateExtension": 5,
    "messageType": 6,
    "retry": 7,
    "legacyVersion": 8,
}

# Source: RFC 9846 §§4.2.2, 4.2.3, 4.4.1, 4.4.2 and 4.5.1–4.5.3.
# These small layouts are derived by hand from the field widths and bounds.
# They pin wire syntax, with opaque certificate and signature bytes, rather than authentication.
VERSIONS: tls.Extension = {"kind": 43, "data": bytes([2, 3, 4])}
SELECTED_VERSION: tls.Extension = {"kind": 43, "data": bytes([3, 4])}
PARAMETERS: tls.Extension = {"kind": 57, "data": b""}
SIGNATURES: tls.Extension = {"kind": 13, "data": bytes([0, 2, 4, 3])}
SMALL_CLIENT: tls.ClientHello = {
    "random": bytes(32),
    "legacy_session_id": b"",
    "cipher_suites": [0x1301],
    "extensions": [VERSIONS, PARAMETERS],
}
SMALL_SERVER: tls.ServerHello = {
    "random": bytes(32),
    "legacy_session_id_echo": b"",
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
    # RFC 9846 §4.2.2: the smallest extension block, a lone supported_versions of 7 bytes.
    (
        ("client_hello", {**SMALL_CLIENT, "extensions": [VERSIONS]}),
        "010000320303" + "00" * 32 + "000002130101000007002b0003020304",
    ),
    (("encrypted_extensions", []), "080000020000"),
    (
        ("certificate_request", {"context": b"", "extensions": [SIGNATURES]}),
        "0d00000b000008000d000400020403",
    ),
    # RFC 9846 §4.4.2: the extension block of a CertificateRequest may be empty.
    (("certificate_request", {"context": b"", "extensions": []}), "0d000003000000"),
    (("certificate", {"context": b"", "entries": []}), "0b00000400000000"),
    (
        (
            "certificate",
            {"context": b"", "entries": [{"data": bytes([0xAA, 0xBB]), "extensions": []}]},
        ),
        "0b00000b00000007000002aabb0000",
    ),
    (("certificate_verify", 0x0403, bytes([0xAB])), "0f00000504030001ab"),
    (("finished", bytes(32)), "14000020" + "00" * 32),
]


@pytest.mark.parametrize(("message", "encoded"), MESSAGES)
def test_message_layout(message: tls.Message, encoded: str) -> None:
    data = bytes.fromhex(encoded)
    assert tls.encode_message(32, message) == data
    assert tls.decode_message(32, data + b"next") == (message, b"next")


@pytest.mark.parametrize(("message", "encoded"), MESSAGES)
def test_incomplete_envelope(message: tls.Message, encoded: str) -> None:
    # Every proper prefix ends before the header or before the body length that the header states.
    data = bytes.fromhex(encoded)
    for cut in range(len(data)):
        # The type byte, the three-byte length, then the body: the error names the cut field.
        if cut == 0:
            needed, available = 1, 0
        elif cut < 4:
            needed, available = 3, cut - 1
        else:
            needed, available = len(data) - 4, cut - 4
        with raises(tls.TlsHandshakeError, f"{PREFIX}truncated {needed} {available}") as info:
            tls.decode_message(32, data[:cut])
        assert info.value.code == CODES["truncated"]


@pytest.mark.parametrize(
    ("payload", "kind", "encoded"),
    [
        (("supported_versions", [0x0304, 0x7A7A]), 43, "0403047a7a"),
        (("selected_version", 0x0304), 43, "0304"),
        (("supported_groups", [0x001D, 0x0017, 0xAAAA]), 10, "0006001d0017aaaa"),
        (("signature_algorithms", [0x0403, 0x0804]), 13, "000404030804"),
        (("client_key_share", []), 51, "0000"),
        (
            ("client_key_share", [{"group": 0x001D, "key_exchange": bytes([0xAB])}]),
            51,
            "0005001d0001ab",
        ),
        (("server_key_share", {"group": 0x0017, "key_exchange": bytes([0xAB])}), 51, "00170001ab"),
        (("retry_key_share", 0x0017), 51, "0017"),
        (
            ("alpn", [bytes([108, 105, 98, 112, 50, 112]), bytes([0xFF])]),
            16,
            "0009066c696270327001ff",
        ),
        (("quic_transport_parameters", bytes([1, 0])), 57, "0100"),
    ],
)
def test_extension_payload(payload: tls.Payload, kind: int, encoded: str) -> None:
    # Sources: RFC 9846 §§4.3.1, 4.3.3, 4.3.7, 4.3.8; RFC 7301 §3.1; RFC 9001 §8.2.
    extension: tls.Extension = {"kind": kind, "data": bytes.fromhex(encoded)}
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
        ("alpn", [b""]),
        ("alpn", [bytes(256)]),
        ("server_key_share", {"group": 0x0017, "key_exchange": b""}),
        ("quic_transport_parameters", bytes(65536)),
    ],
)
def test_payload_length_rejected(payload: tls.Payload) -> None:
    with raises(tls.TlsHandshakeError, f"{PREFIX}length") as info:
        tls.encode_payload(payload)
    assert info.value.code == CODES["length"]


@pytest.mark.parametrize(
    ("form", "kind", "data", "error"),
    [
        # An incomplete field inside a complete extension cannot be repaired by more input.
        ("supported_versions", 43, "03030400", "length"),
        ("supported_versions", 43, "00", "length"),
        ("supported_groups", 10, "000100", "length"),
        ("signature_algorithms", 13, "0003040300", "length"),
        ("selected_version", 43, "030400", "trailing 1"),
        ("selected_version", 10, "0304", "constant"),
        ("server_key_share", 51, "00170000", "length"),
        ("client_key_share", 51, "000100", "length"),
        ("alpn", 16, "00020000", "length"),
        ("alpn", 16, "0003016162", "length"),
    ],
)
def test_bad_payload(form: tls.PayloadForm, kind: int, data: str, error: str) -> None:
    with raises(tls.TlsHandshakeError, f"{PREFIX}{error}") as info:
        tls.decode_payload(form, {"kind": kind, "data": bytes.fromhex(data)})
    assert info.value.code == CODES[error.split()[0]]


@pytest.mark.parametrize(
    ("encoded", "error"),
    [
        ("080000030000aa", "trailing 1"),
        ("080000030001aa", "length"),
        ("0800000a00080039000000390000", "duplicateExtension 57"),
        ("0b000009000000050000000000", "length"),
        # A CertificateRequest block of 1 byte holds no whole extension, though its floor is 0.
        ("0d00000400000100", "length"),
        ("ff000000", "messageType 255"),
        # A peer cannot send the transcript's synthetic message_hash (§4.1).
        ("fe000020" + "00" * 32, "messageType 254"),
        ("1400001f" + "00" * 31, "length"),
        ("14000021" + "00" * 33, "trailing 1"),
    ],
)
def test_bad_message(encoded: str, error: str) -> None:
    with raises(tls.TlsHandshakeError, f"{PREFIX}{error}") as info:
        tls.decode_message(32, bytes.fromhex(encoded))
    assert info.value.code == CODES[error.split()[0]]


def test_client_hello_extensions_below_their_floor() -> None:
    # RFC 9846 §4.2.2: `Extension extensions<7..2^16-1>;`, and this block has 6 bytes.
    extensions: list[tls.Extension] = [{"kind": 0xAAAA, "data": bytes(2)}]
    with raises(tls.TlsHandshakeError, f"{PREFIX}length") as info:
        tls.encode_message(32, ("client_hello", {**SMALL_CLIENT, "extensions": extensions}))
    assert info.value.code == CODES["length"]
    encoded = "010000310303" + "00" * 32 + "000002130101000006aaaa00020000"
    with raises(tls.TlsHandshakeError, f"{PREFIX}length") as info:
        tls.decode_message(32, bytes.fromhex(encoded))
    assert info.value.code == CODES["length"]


@pytest.mark.parametrize("index", [0, 1])
def test_legacy_version(index: int) -> None:
    # RFC 9846 §§4.2.2 and 4.2.3 fix legacy_version to 0303 in both hellos, with its own alert.
    data = bytes.fromhex(MESSAGES[index][1])
    for version in [b"\x03\x04", b"\x03\x02", b"\x02\x03"]:
        with raises(tls.TlsHandshakeError, f"{PREFIX}legacyVersion") as info:
            tls.decode_message(32, data[:4] + version + data[6:])
        assert info.value.code == CODES["legacyVersion"]


def test_legacy_compression() -> None:
    data = bytes.fromhex(MESSAGES[0][1])
    # RFC 9846 §4.2.2 fixes the compression methods to 01 00.
    with raises(tls.TlsHandshakeError, f"{PREFIX}constant") as info:
        tls.decode_message(32, data[:44] + b"\x01" + data[45:])
    assert info.value.code == CODES["constant"]


def test_unknown_extensions_keep_their_order() -> None:
    extensions: list[tls.Extension] = [
        {"kind": 0xAAAA, "data": bytes([0xFF, 0])},
        {"kind": 0xBBBB, "data": b""},
    ]
    encoded = bytes.fromhex("0800000c000aaaaa0002ff00bbbb0000")
    message: tls.Message = ("encrypted_extensions", extensions)
    assert tls.encode_message(32, message) == encoded
    assert tls.decode_message(32, encoded) == (message, b"")


def test_duplicate_extension_encoding() -> None:
    with raises(tls.TlsHandshakeError, f"{PREFIX}duplicateExtension 57") as info:
        tls.encode_message(32, ("encrypted_extensions", [PARAMETERS, PARAMETERS]))
    assert info.value.code == CODES["duplicateExtension"]


def test_duplicate_extension_type_with_different_data() -> None:
    # RFC 9846 §4.3 forbids repeated extension types even when their data differs.
    extensions: list[tls.Extension] = [
        {"kind": 0xAAAA, "data": bytes([0xAB])},
        {"kind": 0xAAAA, "data": bytes([0xCD])},
    ]
    error = f"{PREFIX}duplicateExtension {0xAAAA}"
    with raises(tls.TlsHandshakeError, error) as info:
        tls.encode_message(32, ("encrypted_extensions", extensions))
    assert info.value.code == CODES["duplicateExtension"]
    encoded = bytes.fromhex("0800000c000aaaaa0001abaaaa0001cd")
    with raises(tls.TlsHandshakeError, error) as info:
        tls.decode_message(32, encoded)
    assert info.value.code == CODES["duplicateExtension"]


def test_caller_supplies_finished_hash_length() -> None:
    data = bytes.fromhex("14000030") + bytes(48)
    assert tls.encode_message(48, ("finished", bytes(48))) == data
    assert tls.decode_message(48, data) == (("finished", bytes(48)), b"")
    with raises(tls.TlsHandshakeError, f"{PREFIX}length") as info:
        tls.encode_message(32, ("finished", bytes(48)))
    assert info.value.code == CODES["length"]


def test_rfc8448_trace() -> None:
    # Source: RFC 8448 §3, its complete ClientHello, ServerHello and server flight.
    messages = [CLIENT_HELLO, SERVER_HELLO]
    remaining = SERVER_FLIGHT
    kinds: list[str] = []
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
    # Source: RFC 9846 §4.2.3 fixes the retry random and retains the ServerHello layout.
    random = bytes.fromhex("cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c")
    encoded = bytes.fromhex("0200002e0303") + random + bytes.fromhex("001301000006002b00020304")
    message: tls.Message = ("server_hello", {**SMALL_SERVER, "random": random})
    assert tls.encode_message(32, message) == encoded
    assert tls.decode_message(32, encoded) == (message, b"")
