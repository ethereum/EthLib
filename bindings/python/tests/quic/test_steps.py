"""Mutual libp2p QUIC TLS authentication and its rejection rules."""

import hashlib
import hmac
from typing import cast

import pytest

from ethlib.networking.libp2p import tls as certificate_tls
from ethlib.networking.quic import handshake as hs, tls
from raising import raises

# These credentials instantiate RFC 5280 §4.1 and pinned libp2p TLS's SignedKey format.
# Source: libp2p/specs c750236de43cd8b246a824b377dfdb26bae686db, tls/tls.md.
# OpenSSL 4.0.3 generated the signatures independently of EthLib.
# The certificate signing scalars are 1 and 3; the P-256 host scalars are 2 and 4.
# Both certificates are valid from 2020-01-01 through 2035-01-01, with no unique IDs.
# Each expected peer ID is 12 20 followed by hashlib.sha256 of the host-key protobuf.
CLIENT_CERTIFICATE = bytes.fromhex(
    "308201e53082018ca003020102020101300a06082a8648ce3d040302301a311830160603550403130f4574684c696220"
    "544c532074657374301e170d3230303130313030303030305a170d3335303130313030303030305a301a311830160603"
    "550403130f4574684c696220544c5320746573743059301306072a8648ce3d020106082a8648ce3d030107034200046b"
    "17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162b"
    "ce33576b315ececbb6406837bf51f5a381c23081bf3081bc060a2b0601040183a25a01010481ad3081aa045f0803125b"
    "3059301306072a8648ce3d020106082a8648ce3d030107034200047cf27b188d034f7e8a52380304b51ac3c08969e277"
    "f21b35a60b48fc4766997807775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d10447304502"
    "2100f561d06ddd0aa1357fc5c7bf22f4316dc12c04e83182b7a5d3a3966dff88833002205caa250147648181c1dfb94e"
    "31af8305a2ec9a3a82783ffcdf77c18543de645e300a06082a8648ce3d040302034700304402204d9f7ad53ee4c49d06"
    "cf4ce3ed5723156dc120d0e7e7ce10b95c4742b953a9c00220605b9d0e4872a4eea843abf0ce239118db99016cfe5e12"
    "53be1958c907bcc90e"
)
CLIENT_PEER_ID = bytes.fromhex(
    "122018d92c028418e744b42f365bb0badcc0b7ffd6b1f3238ceac63e583eb704e116"
)
SERVER_CERTIFICATE = bytes.fromhex(
    "308201e53082018ba003020102020103300a06082a8648ce3d040302301a311830160603550403130f4574684c696220"
    "544c532074657374301e170d3230303130313030303030305a170d3335303130313030303030305a301a311830160603"
    "550403130f4574684c696220544c5320746573743059301306072a8648ce3d020106082a8648ce3d030107034200045e"
    "cbe4d1a6330a44c8f7ef951d4bf165e6c6b721efada985fb41661bc6e7fd6c8734640c4998ff7e374b06ce1a64a2ecd8"
    "2ab036384fb83d9a79b127a27d5032a381c13081be3081bb060a2b0601040183a25a01010481ac3081a9045f0803125b"
    "3059301306072a8648ce3d020106082a8648ce3d03010703420004e2534a3532d08fbba02dde659ee62bd0031fe2db78"
    "5596ef509302446b030852e0f1575a4c633cc719dfee5fda862d764efc96c3f30ee0055c42c23f184ed8c60446304402"
    "201f530ae9c07690986e2202f19ab1acbd1414b4c07f23a18ebff7a2f32cdb513b02204daa78dad43f8c08237c37a4d0"
    "3597a476bd7fb867bd80cd3b2d8dba3459f891300a06082a8648ce3d0403020348003045022055f2f146b2922d087f9a"
    "bfae0cc1cdec56c08bd84fa5453910f04a37e561463e022100c6012c8c2853939aad9cd0f0de2d113a0296bc284910d7"
    "f068544035b3835bb6"
)
SERVER_PEER_ID = bytes.fromhex(
    "1220b1ba98726fe4ccd575532be974cc87139e87f5d38a16d951d0d864a28e8c0d1a"
)

# A separately signed server certificate has noncritical KeyUsage = keyEncipherment only.
# RFC 8446 §4.4.2.2 requires digitalSignature for the TLS signing key.
BAD_KEY_USAGE_CERTIFICATE = bytes.fromhex(
    "308201f43082019aa003020102020103300a06082a8648ce3d040302301a311830160603550403130f4574684c696220"
    "544c532074657374301e170d3230303130313030303030305a170d3335303130313030303030305a301a311830160603"
    "550403130f4574684c696220544c5320746573743059301306072a8648ce3d020106082a8648ce3d030107034200045e"
    "cbe4d1a6330a44c8f7ef951d4bf165e6c6b721efada985fb41661bc6e7fd6c8734640c4998ff7e374b06ce1a64a2ecd8"
    "2ab036384fb83d9a79b127a27d5032a381d03081cd3081bd060a2b0601040183a25a01010481ae3081ab045f0803125b"
    "3059301306072a8648ce3d020106082a8648ce3d03010703420004e2534a3532d08fbba02dde659ee62bd0031fe2db78"
    "5596ef509302446b030852e0f1575a4c633cc719dfee5fda862d764efc96c3f30ee0055c42c23f184ed8c60448304602"
    "2100b9ec5f0f10f4891cbe495f254f2c19cea36a4f5d6e59fd21fe4cc340574c811c022100c1eba91daede2d6dbc683b"
    "0aab87efef3958d9cc6ccb587891f3b812663294f7300b0603551d0f040403020520300a06082a8648ce3d0403020348"
    "0030450220037483817ca3ad8a357a84c0a0b01118d5f23d9056ca267208842b8764d2f827022100f4660d6551c2ccf9"
    "cb53668a184f943d165c53ea3b400b58019ec7435246f709"
)

# This independently re-signed server credential carries issuerUniqueID bits aa.
# Pinned libp2p TLS forbids sending unique IDs but permits receivers to tolerate them.
UNIQUE_ID_CERTIFICATE = bytes.fromhex(
    "308201ec30820191a003020102020103300a06082a8648ce3d040302301a311830160603550403130f4574684c696220"
    "544c532074657374301e170d3230303130313030303030305a170d3335303130313030303030305a301a311830160603"
    "550403130f4574684c696220544c5320746573743059301306072a8648ce3d020106082a8648ce3d030107034200045e"
    "cbe4d1a6330a44c8f7ef951d4bf165e6c6b721efada985fb41661bc6e7fd6c8734640c4998ff7e374b06ce1a64a2ecd8"
    "2ab036384fb83d9a79b127a27d5032810200aaa381c33081c03081bd060a2b0601040183a25a01010481ae3081ab045f"
    "0803125b3059301306072a8648ce3d020106082a8648ce3d03010703420004e2534a3532d08fbba02dde659ee62bd003"
    "1fe2db785596ef509302446b030852e0f1575a4c633cc719dfee5fda862d764efc96c3f30ee0055c42c23f184ed8c604"
    "4830460221009a1419d645b68dbf11e9688f71fd380e3294dffbd15d318cc8c8fa3d389c8c3c022100be89d14e9d44d6"
    "84c80d8691a9ba9c1d23494a67c2fcf10f9c458b0ac56c6edb300a06082a8648ce3d0403020349003046022100bd45f3"
    "647a34ea973888932998c32cb63416927c381adf49723f0b18a5b596f1022100d9773b02042ca1c6b36b6eb75973afb5"
    "b8d7d2c3951094b11ace68ee591072eb"
)

# RFC 7748 §6.1: the two private inputs and their shared X25519 output.
X25519_CLIENT = bytes.fromhex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
X25519_SERVER = bytes.fromhex("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
X25519_SHARED = bytes.fromhex("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
# OpenSSL 4.0.3 pkeyutl -derive on P-256 scalars 1 and 2 gives x(2G).
P256_SHARED = bytes.fromhex("7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978")
# P-256's subgroup order and x(G), SEC 2 v2 §2.4.2.
P256_ORDER = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
P256_GENERATOR_X = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
PREFIX = "TLS handshake rejected: EthLib.Networking.Quic.Tls.Handshake.Error."


def config(server: bool, group: int = 0x001D, suite: int = 0x1301) -> hs.Config:
    # The test chooses a profile explicitly; it establishes no default for libp2p.
    secret = X25519_SERVER if server else X25519_CLIENT
    if group == 0x0017:
        secret = (2 if server else 1).to_bytes(32, "big")
    return {
        "policy": {
            "cipher_suites": [suite],
            "groups": [group],
            "signature_schemes": [0x0403],
            "certificates": {
                "host_algorithms": ["p256"],
                "certificate_algorithms": ["p256_sha256"],
                "reject_unique_ids": True,
            },
            "reject_legacy_session_id": True,
        },
        "now": 1_800_000_000,
        "certificates": [SERVER_CERTIFICATE if server else CLIENT_CERTIFICATE],
        "signing_key": (3 if server else 1).to_bytes(32, "big"),
        "signing_nonce": (2 if server else 1).to_bytes(32, "big"),
        "random": bytes([0x53 if server else 0x43]) * 32,
        "ephemeral_keys": [{"group": group, "secret": secret}],
        "initial_shares": [group],
        "transport_parameters": b"",
    }


def message(level: hs.Level, value: tls.Message) -> hs.FlightMessage:
    return {"level": level, "data": tls.encode_message(32, value)}


def decoded(value: hs.FlightMessage) -> tls.Message:
    fields, trailing = tls.decode_message(32, value["data"])
    assert trailing == b""
    return fields


def replace_extension(hello: tls.ClientHello, kind: int, replacement: tls.Extension | None) -> None:
    hello["extensions"] = [ext for ext in hello["extensions"] if ext["kind"] != kind]
    if replacement is not None:
        hello["extensions"].append(replacement)


def extract(salt: bytes, value: bytes) -> bytes:
    return hmac.digest(salt, value, "sha256")


def expand(secret: bytes, label: bytes, context: bytes) -> bytes:
    # RFC 8446 §7.1, with the one SHA-256 output block of RFC 5869 §2.3.
    full_label = b"tls13 " + label
    info = b"\x00\x20" + bytes([len(full_label)]) + full_label + bytes([len(context)]) + context
    return hmac.digest(secret, info + b"\x01", "sha256")


def reference_schedule(shared: bytes, hello: bytes, server: bytes) -> hs.TrafficSecrets:
    # RFC 8446 §7.1: every expected secret is computed independently with stdlib HMAC.
    empty_hash = hashlib.sha256(b"").digest()
    early = extract(bytes(32), bytes(32))
    handshake = extract(expand(early, b"derived", empty_hash), shared)
    master = extract(expand(handshake, b"derived", empty_hash), bytes(32))
    hello_hash, server_hash = hashlib.sha256(hello).digest(), hashlib.sha256(server).digest()
    return {
        "early": early,
        "handshake": handshake,
        "master": master,
        "client_handshake": expand(handshake, b"c hs traffic", hello_hash),
        "server_handshake": expand(handshake, b"s hs traffic", hello_hash),
        "client_application": expand(master, b"c ap traffic", server_hash),
        "server_application": expand(master, b"s ap traffic", server_hash),
    }


def reference_signature(server: bool, transcript: bytes) -> bytes:
    # SEC 1 v2 §4.1.3, using k=1 or k=2 and independently known x(kG).
    context = (
        b"TLS 1.3, server CertificateVerify" if server else b"TLS 1.3, client CertificateVerify"
    )
    content = b" " * 64 + context + b"\x00" + hashlib.sha256(transcript).digest()
    e = int.from_bytes(hashlib.sha256(content).digest(), "big")
    r = int.from_bytes(P256_SHARED, "big") if server else P256_GENERATOR_X
    d, k = (3, 2) if server else (1, 1)
    s = (pow(k, -1, P256_ORDER) * (e + r * d)) % P256_ORDER
    integers = []
    for value in (r, s):
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        if raw[0] & 0x80:
            raw = b"\x00" + raw
        integers.append(b"\x02" + bytes([len(raw)]) + raw)
    body = b"".join(integers)
    return b"\x30" + bytes([len(body)]) + body


def assert_flight_authentication(
    flight: list[hs.FlightMessage], transcript: bytes, server: bool, secret: bytes
) -> None:
    for outgoing in flight:
        fields = decoded(outgoing)
        if fields[0] == "certificate_verify":
            assert fields == (
                "certificate_verify",
                0x0403,
                list(reference_signature(server, transcript)),
            )
        elif fields[0] == "finished":
            key = expand(secret, b"finished", b"")
            expected = hmac.digest(key, hashlib.sha256(transcript).digest(), "sha256")
            assert fields == ("finished", list(expected))
        transcript += outgoing["data"]


@pytest.mark.parametrize("group", [0x001D, 0x0017])
@pytest.mark.parametrize("suite", [0x1301, 0x1303])
@pytest.mark.parametrize("retry", [False, True])
def test_mutual_authentication(group: int, suite: int, retry: bool) -> None:
    client_config, server_config = config(False, group, suite), config(True, group, suite)
    if retry:
        client_config["initial_shares"] = []
    client = hs.client_start(client_config)
    assert len(client["output"]) == 1
    client_hello = client["output"][0]
    hello = decoded(client_hello)
    assert hello[0] == "client_hello"
    assert all(ext["kind"] != 0 for ext in hello[1]["extensions"])
    server = hs.server_step(server_config, hs.server_start(server_config), client_hello)
    prefix = client_hello["data"]
    if retry:
        assert len(server["output"]) == 1
        retry_message = server["output"][0]
        client = hs.client_step(client_config, SERVER_PEER_ID, client["state"], retry_message)
        assert len(client["output"]) == 1
        prefix = (
            b"\xfe\x00\x00\x20"
            + hashlib.sha256(client_hello["data"]).digest()
            + retry_message["data"]
            + client["output"][0]["data"]
        )
        server = hs.server_step(server_config, server["state"], client["output"][0])
    server_flight = server["output"]
    assert [item["level"] for item in server_flight] == ["initial"] + ["handshake"] * 5
    assert [decoded(item)[0] for item in server_flight] == [
        "server_hello",
        "encrypted_extensions",
        "certificate_request",
        "certificate",
        "certificate_verify",
        "finished",
    ]
    hello_transcript = prefix + server_flight[0]["data"]
    server_transcript = prefix + b"".join(item["data"] for item in server_flight)
    shared = X25519_SHARED if group == 0x001D else P256_SHARED
    expected_secrets = reference_schedule(shared, hello_transcript, server_transcript)
    assert_flight_authentication(server_flight, prefix, True, expected_secrets["server_handshake"])
    for incoming in server_flight:
        client = hs.client_step(client_config, SERVER_PEER_ID, client["state"], incoming)
    client_completion = client["completion"]
    assert client_completion is not None
    assert client_completion["peer_id"] == SERVER_PEER_ID
    assert client_completion["peer_chain"] == [SERVER_CERTIFICATE]
    assert [decoded(item)[0] for item in client["output"]] == [
        "certificate",
        "certificate_verify",
        "finished",
    ]
    assert_flight_authentication(
        client["output"], server_transcript, False, expected_secrets["client_handshake"]
    )
    for incoming in client["output"]:
        server = hs.server_step(server_config, server["state"], incoming)
    server_completion = server["completion"]
    assert server_completion is not None
    assert server_completion["peer_id"] == CLIENT_PEER_ID
    assert server_completion["peer_chain"] == [CLIENT_CERTIFICATE]
    for completion in (client_completion, server_completion):
        negotiated = completion["negotiated"]
        assert negotiated["suite"] == suite
        assert negotiated["group"] == group
        assert negotiated["shared_secret"] == shared
        assert negotiated["hello_transcript"] == hello_transcript
        assert negotiated["server_transcript"] == server_transcript
        assert negotiated["secrets"] == expected_secrets


def server_flight() -> tuple[hs.Config, hs.Config, hs.Step, hs.Step]:
    client_config, server_config = config(False), config(True)
    client = hs.client_start(client_config)
    server = hs.server_step(server_config, hs.server_start(server_config), client["output"][0])
    return client_config, server_config, client, server


def client_before(index: int) -> tuple[hs.Config, hs.Step, list[hs.FlightMessage]]:
    client_config, _, client, server = server_flight()
    for incoming in server["output"][:index]:
        client = hs.client_step(client_config, SERVER_PEER_ID, client["state"], incoming)
    return client_config, client, server["output"]


@pytest.mark.parametrize("field", ["cipher_suites", "groups", "signature_schemes"])
def test_policy_requires_explicit_nonempty_algorithm_lists(field: str) -> None:
    client_config = config(False)
    cast("dict[str, object]", client_config["policy"])[field] = []
    with raises(hs.TlsStepError, PREFIX + "configuration") as error:
        hs.client_start(client_config)
    assert error.value.code == 0x150


@pytest.mark.parametrize(
    ("field", "identifier"),
    [("cipher_suites", 0x1302), ("groups", 0x0018), ("signature_schemes", 0x0804)],
)
def test_policy_cannot_enable_an_unimplemented_backend(field: str, identifier: int) -> None:
    client_config = config(False)
    cast("dict[str, object]", client_config["policy"])[field] = [identifier]
    with raises(hs.TlsStepError, PREFIX + "configuration"):
        hs.client_start(client_config)


def test_local_signing_key_must_match_the_certificate() -> None:
    client_config = config(False)
    client_config["signing_key"] = (5).to_bytes(32, "big")
    with raises(hs.TlsStepError, PREFIX + "configuration"):
        hs.client_start(client_config)


@pytest.mark.parametrize("protocols", [[list(b"h3")], []])
def test_server_rejects_client_without_libp2p_alpn(protocols: list[list[int]]) -> None:
    client_config, server_config = config(False), config(True)
    client = hs.client_start(client_config)
    hello = decoded(client["output"][0])
    assert hello[0] == "client_hello"
    # RFC 7301 requires a nonempty list, so an empty ALPN list is malformed syntax.
    alpn_extension: tls.Extension
    if protocols:
        alpn_extension = tls.encode_payload(("alpn", protocols))
        expected, code = "noApplicationProtocol", 0x178
    else:
        alpn_extension = {"kind": 16, "data": [0, 0]}
        expected, code = "decodeError", 0x132
    replace_extension(hello[1], 16, alpn_extension)
    with raises(hs.TlsStepError, PREFIX + expected) as error:
        hs.server_step(server_config, hs.server_start(server_config), message("initial", hello))
    assert error.value.code == code


@pytest.mark.parametrize("kind", [16, 43, 57, 10, 13, 51])
def test_server_requires_handshake_extensions(kind: int) -> None:
    client_config, server_config = config(False), config(True)
    client = hs.client_start(client_config)
    hello = decoded(client["output"][0])
    assert hello[0] == "client_hello"
    replace_extension(hello[1], kind, None)
    expected, code = ("noApplicationProtocol", 0x178) if kind == 16 else ("missingExtension", 0x16D)
    with raises(hs.TlsStepError, PREFIX + expected) as error:
        hs.server_step(server_config, hs.server_start(server_config), message("initial", hello))
    assert error.value.code == code


def test_server_ignores_received_sni() -> None:
    client_config, server_config = config(False), config(True)
    client = hs.client_start(client_config)
    hello = decoded(client["output"][0])
    assert hello[0] == "client_hello"
    # Pinned libp2p TLS Future Extensibility requires servers to ignore received SNI.
    hello[1]["extensions"].append({"kind": 0, "data": list(b"ignored")})
    server = hs.server_step(
        server_config, hs.server_start(server_config), message("initial", hello)
    )
    assert server["state"]["phase"] == "client_certificate"
    encrypted = decoded(server["output"][1])
    assert encrypted[0] == "encrypted_extensions"
    assert all(ext["kind"] != 0 for ext in encrypted[1])


@pytest.mark.parametrize("version", [0x0303, 0x7A7A])
def test_server_rejects_offer_without_tls13(version: int) -> None:
    client_config, server_config = config(False), config(True)
    hello = decoded(hs.client_start(client_config)["output"][0])
    assert hello[0] == "client_hello"
    replace_extension(hello[1], 43, tls.encode_payload(("supported_versions", [version])))
    with raises(hs.TlsStepError, PREFIX + "protocolVersion") as error:
        hs.server_step(server_config, hs.server_start(server_config), message("initial", hello))
    assert error.value.code == 0x146


@pytest.mark.parametrize("reject", [True, False])
def test_server_session_id_rule_is_explicit(reject: bool) -> None:
    client_config, server_config = config(False), config(True)
    server_config["policy"]["reject_legacy_session_id"] = reject
    hello = decoded(hs.client_start(client_config)["output"][0])
    assert hello[0] == "client_hello"
    hello[1]["legacy_session_id"] = [1]
    if reject:
        with raises(hs.TlsStepError, PREFIX + "protocolViolation") as error:
            hs.server_step(server_config, hs.server_start(server_config), message("initial", hello))
        assert error.value.code == 0x0A
    else:
        server = hs.server_step(
            server_config, hs.server_start(server_config), message("initial", hello)
        )
        server_hello = decoded(server["output"][0])
        assert server_hello[0] == "server_hello"
        assert server_hello[1]["legacy_session_id_echo"] == [1]


@pytest.mark.parametrize("suite", [0x1302, 0x7A7A])
def test_client_rejects_unoffered_or_non_sha256_suite(suite: int) -> None:
    client_config, _, client, server = server_flight()
    server_hello = decoded(server["output"][0])
    assert server_hello[0] == "server_hello"
    server_hello[1]["cipher_suite"] = suite
    with raises(hs.TlsStepError, PREFIX + "illegalParameter") as error:
        hs.client_step(
            client_config, SERVER_PEER_ID, client["state"], message("initial", server_hello)
        )
    assert error.value.code == 0x12F


def test_client_requires_libp2p_alpn_selection() -> None:
    client_config, client, flight = client_before(1)
    encrypted = decoded(flight[1])
    assert encrypted[0] == "encrypted_extensions"
    encrypted[1][:] = [ext for ext in encrypted[1] if ext["kind"] != 16]
    encrypted[1].append(tls.encode_payload(("alpn", [list(b"h3")])))
    with raises(hs.TlsStepError, PREFIX + "noApplicationProtocol") as error:
        hs.client_step(
            client_config, SERVER_PEER_ID, client["state"], message("handshake", encrypted)
        )
    assert error.value.code == 0x178


@pytest.mark.parametrize("index", [1, 2, 3, 4, 5])
def test_client_rejects_out_of_order_server_messages(index: int) -> None:
    client_config, _, client, server = server_flight()
    with raises(hs.TlsStepError, PREFIX + "unexpectedMessage") as error:
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], server["output"][index])
    assert error.value.code == 0x10A


def test_client_checks_the_dialled_peer_id() -> None:
    client_config, client, flight = client_before(3)
    with raises(
        hs.TlsStepError, PREFIX + "certificate (EthLib.Networking.Libp2p.Tls.TlsCertError.peerId)"
    ) as error:
        hs.client_step(client_config, CLIENT_PEER_ID, client["state"], flight[3])
    assert error.value.code == 0x12A


@pytest.mark.parametrize("index", [4, 5])
def test_client_rejects_changed_signature_or_finished(index: int) -> None:
    client_config, client, flight = client_before(index)
    original = flight[index]
    data = original["data"]
    changed: hs.FlightMessage = {
        "level": original["level"],
        "data": data[:-1] + bytes([data[-1] ^ 1]),
    }
    with raises(hs.TlsStepError, PREFIX + "decryptError") as error:
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], changed)
    assert error.value.code == 0x133


def test_server_requires_a_nonempty_client_certificate() -> None:
    _, server_config, _, server = server_flight()
    empty = message("handshake", ("certificate", {"context": [], "entries": []}))
    with raises(hs.TlsStepError, PREFIX + "certificateRequired") as error:
        hs.server_step(server_config, server["state"], empty)
    assert error.value.code == 0x174


def test_client_rejects_second_hello_retry_request() -> None:
    client_config, server_config = config(False), config(True)
    client_config["initial_shares"] = []
    client = hs.client_start(client_config)
    server = hs.server_step(server_config, hs.server_start(server_config), client["output"][0])
    retry = server["output"][0]
    client = hs.client_step(client_config, SERVER_PEER_ID, client["state"], retry)
    with raises(hs.TlsStepError, PREFIX + "unexpectedMessage"):
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], retry)


def test_retry_rejects_changes_to_client_hello_random() -> None:
    client_config, server_config = config(False), config(True)
    client_config["initial_shares"] = []
    client = hs.client_start(client_config)
    server = hs.server_step(server_config, hs.server_start(server_config), client["output"][0])
    client = hs.client_step(client_config, SERVER_PEER_ID, client["state"], server["output"][0])
    hello = decoded(client["output"][0])
    assert hello[0] == "client_hello"
    hello[1]["random"] = bytes(32)
    with raises(hs.TlsStepError, PREFIX + "illegalParameter"):
        hs.server_step(server_config, server["state"], message("initial", hello))


def test_invalid_early_share_is_not_used_as_a_shared_secret() -> None:
    client_config, server_config = config(False), config(True)
    hello = decoded(hs.client_start(client_config)["output"][0])
    assert hello[0] == "client_hello"
    replace_extension(
        hello[1],
        51,
        tls.encode_payload(("client_key_share", [{"group": 0x001D, "key_exchange": [0] * 32}])),
    )
    with raises(
        hs.TlsStepError, PREFIX + "crypto (EthLib.Networking.Quic.Tls.Crypto.Error.sharedSecret)"
    ) as error:
        hs.server_step(server_config, hs.server_start(server_config), message("initial", hello))
    assert error.value.code == 0x12F


def client_flight() -> tuple[hs.Config, hs.Config, hs.Step, hs.Step]:
    client_config, server_config, client, server = server_flight()
    for incoming in server["output"]:
        client = hs.client_step(client_config, SERVER_PEER_ID, client["state"], incoming)
    return client_config, server_config, client, server


@pytest.mark.parametrize("index", [1, 2])
def test_server_rejects_changed_client_signature_or_finished(index: int) -> None:
    _, server_config, client, server = client_flight()
    for incoming in client["output"][:index]:
        server = hs.server_step(server_config, server["state"], incoming)
    original = client["output"][index]
    data = original["data"]
    changed: hs.FlightMessage = {
        "level": original["level"],
        "data": data[:-1] + bytes([data[-1] ^ 1]),
    }
    with raises(hs.TlsStepError, PREFIX + "decryptError") as error:
        hs.server_step(server_config, server["state"], changed)
    assert error.value.code == 0x133


def test_server_rejects_finished_before_client_authentication() -> None:
    _, server_config, client, server = client_flight()
    with raises(hs.TlsStepError, PREFIX + "unexpectedMessage"):
        hs.server_step(server_config, server["state"], client["output"][-1])


@pytest.mark.parametrize("client_role", [True, False])
def test_wrong_encryption_level_is_rejected(client_role: bool) -> None:
    client_config, server_config, client, server = server_flight()
    changed: hs.FlightMessage
    if client_role:
        changed = {**server["output"][0], "level": "handshake"}
        with raises(hs.TlsStepError, PREFIX + "unexpectedMessage"):
            hs.client_step(client_config, SERVER_PEER_ID, client["state"], changed)
    else:
        changed = {**client["output"][0], "level": "application"}
        with raises(hs.TlsStepError, PREFIX + "unexpectedMessage"):
            hs.server_step(server_config, hs.server_start(server_config), changed)


def ticket(early_data: bytes | None = None) -> hs.FlightMessage:
    # RFC 8446 §4.6.1: lifetime, age_add, nonce, ticket and extensions.
    extensions = b"" if early_data is None else b"\x00\x2a\x00\x04" + early_data
    body = (60).to_bytes(4, "big") + bytes(4) + b"\x00\x00\x01x"
    body += len(extensions).to_bytes(2, "big") + extensions
    return {"level": "application", "data": b"\x04" + len(body).to_bytes(3, "big") + body}


@pytest.mark.parametrize("early_data", [None, b"\xff" * 4])
def test_completed_client_accepts_session_ticket_without_changing_transcript(
    early_data: bytes | None,
) -> None:
    client_config, _, client, _ = client_flight()
    result = hs.client_step(client_config, SERVER_PEER_ID, client["state"], ticket(early_data))
    assert result == {"state": client["state"], "output": [], "completion": None}


def test_ticket_early_data_uses_quic_sentinel() -> None:
    client_config, _, client, _ = client_flight()
    with raises(hs.TlsStepError, PREFIX + "protocolViolation") as error:
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], ticket(bytes(4)))
    assert error.value.code == 0x0A


@pytest.mark.parametrize(
    ("data", "expected", "code"),
    [
        (b"\x18\x00\x00\x01\x00", "unexpectedMessage", 0x10A),
        (b"\x0d\x00\x00\x00", "protocolViolation", 0x0A),
        (b"\x04\x00\x00\x01", "decodeError", 0x132),
    ],
)
def test_completed_client_rejects_forbidden_or_malformed_messages(
    data: bytes,
    expected: str,
    code: int,
) -> None:
    client_config, _, client, _ = client_flight()
    with raises(hs.TlsStepError, PREFIX + expected) as error:
        hs.client_step(
            client_config, SERVER_PEER_ID, client["state"], {"level": "application", "data": data}
        )
    assert error.value.code == code


def test_ticket_rejects_an_extension_in_the_wrong_message() -> None:
    client_config, _, client, _ = client_flight()
    incoming = ticket(b"\xff" * 4)
    # RFC 8446 §4.2 permits signature_algorithms in ClientHello and CertificateRequest only.
    incoming["data"] = incoming["data"].replace(b"\x00\x2a\x00\x04", b"\x00\x0d\x00\x04")
    with raises(hs.TlsStepError, PREFIX + "illegalParameter"):
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], incoming)


@pytest.mark.parametrize("modes", [None, [1, 1]])
def test_psk_offer_requires_modes_and_valid_framing(modes: list[int] | None) -> None:
    client_config, server_config = config(False), config(True)
    hello = decoded(hs.client_start(client_config)["output"][0])
    assert hello[0] == "client_hello"
    if modes is not None:
        hello[1]["extensions"].append({"kind": 45, "data": modes})
    hello[1]["extensions"].append({"kind": 41, "data": []})
    expected = "missingExtension" if modes is None else "decodeError"
    with raises(hs.TlsStepError, PREFIX + expected):
        hs.server_step(server_config, hs.server_start(server_config), message("initial", hello))


def test_server_can_decline_a_well_formed_psk_offer() -> None:
    client_config, server_config = config(False), config(True)
    hello = decoded(hs.client_start(client_config)["output"][0])
    assert hello[0] == "client_hello"
    # RFC 8446 §4.2.11: one identity 'x', zero age and one 32-byte binder.
    psk = bytes.fromhex("000700017800000000002120") + bytes(32)
    hello[1]["extensions"].extend(
        [
            {"kind": 45, "data": [1, 1]},
            {"kind": 41, "data": list(psk)},
        ]
    )
    server = hs.server_step(
        server_config, hs.server_start(server_config), message("initial", hello)
    )
    server_hello = decoded(server["output"][0])
    assert server_hello[0] == "server_hello"
    assert all(ext["kind"] != 41 for ext in server_hello[1]["extensions"])
    assert server["state"]["phase"] == "client_certificate"


def test_server_ignores_unknown_offered_versions_when_tls13_is_present() -> None:
    client_config, server_config = config(False), config(True)
    hello = decoded(hs.client_start(client_config)["output"][0])
    assert hello[0] == "client_hello"
    replace_extension(hello[1], 43, tls.encode_payload(("supported_versions", [0x7A7A, 0x0304])))
    server = hs.server_step(
        server_config, hs.server_start(server_config), message("initial", hello)
    )
    assert server["state"]["phase"] == "client_certificate"


@pytest.mark.parametrize("kind", [16, 57])
def test_client_requires_alpn_and_quic_parameters(kind: int) -> None:
    client_config, client, flight = client_before(1)
    encrypted = decoded(flight[1])
    assert encrypted[0] == "encrypted_extensions"
    encrypted[1][:] = [ext for ext in encrypted[1] if ext["kind"] != kind]
    expected, code = ("noApplicationProtocol", 0x178) if kind == 16 else ("missingExtension", 0x16D)
    with raises(hs.TlsStepError, PREFIX + expected) as error:
        hs.client_step(
            client_config, SERVER_PEER_ID, client["state"], message("handshake", encrypted)
        )
    assert error.value.code == code


def test_client_rejects_a_response_to_an_unoffered_extension() -> None:
    client_config, client, flight = client_before(1)
    encrypted = decoded(flight[1])
    assert encrypted[0] == "encrypted_extensions"
    encrypted[1].append({"kind": 0xAAAA, "data": []})
    with raises(hs.TlsStepError, PREFIX + "unsupportedExtension") as error:
        hs.client_step(
            client_config, SERVER_PEER_ID, client["state"], message("handshake", encrypted)
        )
    assert error.value.code == 0x16E


def test_client_rejects_a_retry_for_a_group_already_shared() -> None:
    client_config, _, client, server = server_flight()
    server_hello = decoded(server["output"][0])
    assert server_hello[0] == "server_hello"
    retry = server_hello[1]
    retry["random"] = bytes.fromhex(
        "cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c"
    )
    retry["extensions"] = [
        tls.encode_payload(("selected_version", 0x0304)),
        tls.encode_payload(("retry_key_share", 0x001D)),
    ]
    with raises(hs.TlsStepError, PREFIX + "illegalParameter"):
        hs.client_step(
            client_config,
            SERVER_PEER_ID,
            client["state"],
            message("initial", ("server_hello", retry)),
        )


@pytest.mark.parametrize("local", [True, False])
def test_certificate_key_usage_must_allow_signing(local: bool) -> None:
    expected = PREFIX + "certificate (EthLib.Networking.Libp2p.Tls.TlsCertError.publicKey)"
    if local:
        server_config = config(True)
        server_config["certificates"] = [BAD_KEY_USAGE_CERTIFICATE]
        with raises(hs.TlsStepError, expected) as error:
            hs.server_start(server_config)
    else:
        client_config, client, flight = client_before(3)
        certificate = decoded(flight[3])
        assert certificate[0] == "certificate"
        certificate[1]["entries"][0]["data"] = list(BAD_KEY_USAGE_CERTIFICATE)
        with raises(hs.TlsStepError, expected) as error:
            hs.client_step(
                client_config, SERVER_PEER_ID, client["state"], message("handshake", certificate)
            )
    assert error.value.code == 0x12A


def psk_offer(identities: list[tuple[bytes, int]], binder_byte: int) -> tls.Extension:
    # RFC 8446 §4.2.11: identity ages and binders may change after a retry.
    encoded_identities = b"".join(
        len(identity).to_bytes(2, "big") + identity + age.to_bytes(4, "big")
        for identity, age in identities
    )
    binders = (b"\x20" + bytes([binder_byte]) * 32) * len(identities)
    data = len(encoded_identities).to_bytes(2, "big") + encoded_identities
    data += len(binders).to_bytes(2, "big") + binders
    return {"kind": 41, "data": list(data)}


@pytest.mark.parametrize("identities", [[b"x"], [b"y"], [b"x", b"y"]])
def test_retry_preserves_psk_identities_but_allows_updated_ages_and_binders(
    identities: list[bytes],
) -> None:
    client_config, server_config = config(False), config(True)
    client_config["initial_shares"] = []
    first = decoded(hs.client_start(client_config)["output"][0])
    assert first[0] == "client_hello"
    first[1]["extensions"].extend([{"kind": 45, "data": [1, 1]}, psk_offer([(b"x", 0)], 0)])
    server = hs.server_step(
        server_config, hs.server_start(server_config), message("initial", first)
    )
    assert len(server["output"]) == 1
    # RFC 7748 §6.1 supplies the public share for this configured private input.
    public = bytes.fromhex("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
    key_share = tls.encode_payload(
        ("client_key_share", [{"group": 0x001D, "key_exchange": list(public)}])
    )
    second: tls.ClientHello = {**first[1], "extensions": list(first[1]["extensions"])}
    replace_extension(second, 51, key_share)
    # Keep the PSK last after replacing the earlier key_share extension.
    psk = psk_offer([(identity, 1) for identity in identities], 1)
    replace_extension(second, 41, psk)
    if identities == [b"x"]:
        result = hs.server_step(
            server_config, server["state"], message("initial", ("client_hello", second))
        )
        assert result["state"]["phase"] == "client_certificate"
    else:
        with raises(hs.TlsStepError, PREFIX + "illegalParameter") as error:
            hs.server_step(
                server_config, server["state"], message("initial", ("client_hello", second))
            )
        assert error.value.code == 0x12F


def test_cookie_only_retry_echoes_exact_cookie_and_preserves_key_share() -> None:
    client_config, _, client, server = server_flight()
    first = decoded(client["output"][0])
    assert first[0] == "client_hello"
    server_hello = decoded(server["output"][0])
    assert server_hello[0] == "server_hello"
    # RFC 8446 §4.2.2: a retry cookie is echoed unchanged, including opaque zero bytes.
    cookie: tls.Extension = {"kind": 44, "data": [0, 5, 255, 0, 1, 0, 255]}
    retry: tls.ServerHello = {
        **server_hello[1],
        "random": bytes.fromhex("cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c"),
        "extensions": [tls.encode_payload(("selected_version", 0x0304)), cookie],
    }
    incoming = message("initial", ("server_hello", retry))
    result = hs.client_step(client_config, SERVER_PEER_ID, client["state"], incoming)
    assert len(result["output"]) == 1
    second = decoded(result["output"][0])
    assert second[0] == "client_hello"
    assert second[1] == {**first[1], "extensions": first[1]["extensions"] + [cookie]}
    expected_transcript = (
        b"\xfe\x00\x00\x20"
        + hashlib.sha256(client["output"][0]["data"]).digest()
        + incoming["data"]
        + result["output"][0]["data"]
    )
    assert bytes(result["state"]["transcript"]["bytes"]) == expected_transcript
    # A cookie-only retry does not force a different group in the final ServerHello.
    accepted = hs.client_step(client_config, SERVER_PEER_ID, result["state"], server["output"][0])
    assert accepted["state"]["phase"] == "encrypted_extensions"


@pytest.mark.parametrize("change", ["suite", "group"])
def test_server_hello_must_preserve_retry_suite_and_requested_group(change: str) -> None:
    client_config, server_config = config(False), config(True)
    client_config["policy"]["cipher_suites"] = [0x1301, 0x1303]
    client_config["policy"]["groups"] = [0x001D, 0x0017]
    client_config["ephemeral_keys"].append({"group": 0x0017, "secret": (1).to_bytes(32, "big")})
    client_config["initial_shares"] = []
    client = hs.client_start(client_config)
    server = hs.server_step(server_config, hs.server_start(server_config), client["output"][0])
    client = hs.client_step(client_config, SERVER_PEER_ID, client["state"], server["output"][0])
    server = hs.server_step(server_config, server["state"], client["output"][0])
    final = decoded(server["output"][0])
    assert final[0] == "server_hello"
    if change == "suite":
        # Both suites were initially offered, so only the retry fixes the selected one.
        final[1]["cipher_suite"] = 0x1303
    else:
        # P-256 was initially supported, but the retry requested a single X25519 share.
        p256_public = bytes.fromhex(
            "047cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978"
            "07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1"
        )
        replacement = tls.encode_payload(
            ("server_key_share", {"group": 0x0017, "key_exchange": list(p256_public)})
        )
        final[1]["extensions"] = [
            replacement if ext["kind"] == 51 else ext for ext in final[1]["extensions"]
        ]
    with raises(hs.TlsStepError, PREFIX + "illegalParameter") as error:
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], message("initial", final))
    assert error.value.code == 0x12F


@pytest.mark.parametrize("client_role", [False, True])
@pytest.mark.parametrize(
    "public",
    [
        b"\x04" + bytes(64),
        b"\x03" + bytes(32),
        b"\x04" + bytes(63),
        b"\x04"
        + bytes.fromhex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff")
        + bytes(32),
    ],
)
def test_p256_peer_share_requires_a_valid_uncompressed_point(
    public: bytes,
    client_role: bool,
) -> None:
    client_config, server_config = config(False, 0x0017), config(True, 0x0017)
    client = hs.client_start(client_config)
    if client_role:
        server = hs.server_step(server_config, hs.server_start(server_config), client["output"][0])
        incoming = decoded(server["output"][0])
        assert incoming[0] == "server_hello"
        replacement = tls.encode_payload(
            ("server_key_share", {"group": 0x0017, "key_exchange": list(public)})
        )
        incoming[1]["extensions"] = [
            replacement if ext["kind"] == 51 else ext for ext in incoming[1]["extensions"]
        ]
    else:
        incoming = decoded(client["output"][0])
        assert incoming[0] == "client_hello"
        replace_extension(
            incoming[1],
            51,
            tls.encode_payload(
                ("client_key_share", [{"group": 0x0017, "key_exchange": list(public)}])
            ),
        )
    expected = PREFIX + "crypto (EthLib.Networking.Quic.Tls.Crypto.Error.keyShare)"
    with raises(hs.TlsStepError, expected) as error:
        if client_role:
            hs.client_step(
                client_config, SERVER_PEER_ID, client["state"], message("initial", incoming)
            )
        else:
            hs.server_step(
                server_config, hs.server_start(server_config), message("initial", incoming)
            )
    assert error.value.code == 0x12F


def test_client_rejects_an_empty_server_certificate_with_decode_error() -> None:
    client_config, client, _ = client_before(3)
    # RFC 8446 §4.4.2.4 requires decode_error for an empty server certificate list.
    empty = message("handshake", ("certificate", {"context": [], "entries": []}))
    with raises(hs.TlsStepError, PREFIX + "decodeError") as error:
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], empty)
    assert error.value.code == 0x132


@pytest.mark.parametrize("client_role", [False, True])
def test_legacy_compression_must_be_null(client_role: bool) -> None:
    client_config, server_config, client, server = server_flight()
    # RFC 8446 §§4.1.2 and 4.1.3 require illegal_parameter for non-null compression.
    original = server["output"][0] if client_role else client["output"][0]
    data = original["data"]
    compression_index = 41 if client_role else 44
    assert data[compression_index] == 0
    changed: hs.FlightMessage = {
        "level": "initial",
        "data": data[:compression_index] + b"\x01" + data[compression_index + 1 :],
    }
    with raises(hs.TlsStepError, PREFIX + "illegalParameter") as error:
        if client_role:
            hs.client_step(client_config, SERVER_PEER_ID, client["state"], changed)
        else:
            hs.server_step(server_config, hs.server_start(server_config), changed)
    assert error.value.code == 0x12F


def test_duplicate_handshake_extensions_use_illegal_parameter() -> None:
    client_config, client, flight = client_before(1)
    # RFC 8446 §4.2 forbids duplicate extensions, independently of their contents.
    original = flight[1]["data"]
    assert original[0] == 8
    extensions = original[6:]
    assert int.from_bytes(original[4:6], "big") == len(extensions)
    extensions += bytes.fromhex("00390000")
    body = len(extensions).to_bytes(2, "big") + extensions
    incoming: hs.FlightMessage = {
        "level": "handshake",
        "data": b"\x08" + len(body).to_bytes(3, "big") + body,
    }
    with raises(hs.TlsStepError, PREFIX + "illegalParameter") as error:
        hs.client_step(client_config, SERVER_PEER_ID, client["state"], incoming)
    assert error.value.code == 0x12F


def test_psk_identity_and_binder_counts_must_agree() -> None:
    client_config, server_config = config(False), config(True)
    hello = decoded(hs.client_start(client_config)["output"][0])
    assert hello[0] == "client_hello"
    # RFC 8446 §4.2.11 assigns one binder per identity.
    # Unequal counts are inconsistent fields: illegal_parameter under §6.2.
    # Both vectors are well-framed: two one-byte identities and a single 32-byte binder.
    psk = bytes.fromhex("000e0001780000000000017900000000002120") + bytes(32)
    hello[1]["extensions"].extend([{"kind": 45, "data": [1, 1]}, {"kind": 41, "data": list(psk)}])
    with raises(hs.TlsStepError, PREFIX + "illegalParameter") as error:
        hs.server_step(server_config, hs.server_start(server_config), message("initial", hello))
    assert error.value.code == 0x12F


@pytest.mark.parametrize("server_role", [False, True])
def test_local_certificate_must_omit_unique_ids_even_when_receivers_tolerate_them(
    server_role: bool,
) -> None:
    endpoint_config = config(server_role)
    endpoint_config["certificates"] = [UNIQUE_ID_CERTIFICATE]
    endpoint_config["signing_key"] = (3).to_bytes(32, "big")
    endpoint_config["policy"]["certificates"]["reject_unique_ids"] = False
    # The independently signed certificate is acceptable under this explicit receiver policy.
    assert (
        certificate_tls.authenticate(
            endpoint_config["policy"]["certificates"],
            endpoint_config["now"],
            [UNIQUE_ID_CERTIFICATE],
        )
        == SERVER_PEER_ID
    )
    with raises(hs.TlsStepError, PREFIX + "configuration") as error:
        if server_role:
            hs.server_start(endpoint_config)
        else:
            hs.client_start(endpoint_config)
    assert error.value.code == 0x150


@pytest.mark.parametrize("offers", ["suites", "groups", "signatures"])
def test_disjoint_algorithm_offers_use_handshake_failure(offers: str) -> None:
    server_config = config(True)
    client_config = config(False, 0x0017 if offers == "groups" else 0x001D)
    if offers == "suites":
        client_config["policy"]["cipher_suites"] = [0x1303]
    incoming = decoded(hs.client_start(client_config)["output"][0])
    assert incoming[0] == "client_hello"
    if offers == "signatures":
        # A remote peer can offer RSA without offering the server's P-256 signature scheme.
        replace_extension(incoming[1], 13, tls.encode_payload(("signature_algorithms", [0x0804])))
    with raises(hs.TlsStepError, PREFIX + "handshakeFailure") as error:
        hs.server_step(server_config, hs.server_start(server_config), message("initial", incoming))
    assert error.value.code == 0x128


@pytest.mark.parametrize("server_role", [False, True])
@pytest.mark.parametrize("field", ["random", "signing_key", "signing_nonce", "ephemeral_secret"])
@pytest.mark.parametrize("size", [0, 31, 33])
def test_fixed_size_configuration_inputs_reject_wrong_lengths(
    server_role: bool,
    field: str,
    size: int,
) -> None:
    endpoint_config = config(server_role)
    if field == "ephemeral_secret":
        endpoint_config["ephemeral_keys"][0]["secret"] = bytes(size)
        prefix = "ephemeral_keys: secret"
    else:
        cast("dict[str, object]", endpoint_config)[field] = bytes(size)
        prefix = field
    # The typed export rejects the field before it reaches any protocol operation.
    with raises(hs.TlsStepError, f"{prefix}: expected 32 bytes, got {size}") as error:
        if server_role:
            hs.server_start(endpoint_config)
        else:
            hs.client_start(endpoint_config)
    assert error.value.code == 0


@pytest.mark.parametrize("client_role", [False, True])
@pytest.mark.parametrize("form", ["truncated", "trailing", "coalesced"])
def test_step_input_is_exactly_one_complete_handshake_message(client_role: bool, form: str) -> None:
    client_config, server_config, client, server = server_flight()
    original = server["output"][0] if client_role else client["output"][0]
    data = original["data"]
    if form == "truncated":
        data = data[:-1]
    elif form == "trailing":
        data += b"\x00"
    else:
        data += data
    incoming: hs.FlightMessage = {"level": "initial", "data": data}
    # CRYPTO reassembly must provide exactly one complete message at the step boundary.
    with raises(hs.TlsStepError, PREFIX + "decodeError") as error:
        if client_role:
            hs.client_step(client_config, SERVER_PEER_ID, client["state"], incoming)
        else:
            hs.server_step(server_config, hs.server_start(server_config), incoming)
    assert error.value.code == 0x132
