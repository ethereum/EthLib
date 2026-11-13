"""The Builder API containers and signatures against the examples of the builder specification."""

import hashlib
import json
import struct
from collections.abc import Sequence
from pathlib import Path
from typing import Any

import pytest
from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from ethlib.errors import SszError, TransitionError
from ethlib.networking import snappy
from raising import raises

ERROR = SszError
# The examples of the builder specification, pinned in tests/sources.toml.
EXAMPLES = Path(__file__).resolve().parents[4] / "tests/consensus/builder_api"
# The forks of the examples, by their consensus version names.
VERSIONS = ["bellatrix", "capella", "deneb", "electra", "fulu"]
# The offset of the value in a bid: 4 bytes per variable-size field before it.
VALUE_AT = {"bellatrix": 4, "capella": 4, "deneb": 8, "electra": 12, "fulu": 12}
ZERO = bytes(32)
# The bytes of a blob, its field elements, and the bound on the blobs of a bundle, in mainnet.
BLOB_SIZE = 131_072
FIELD_ELEMENTS_PER_BLOB = 4096
MAX_BLOBS = 4096
SECRET_KEY = 42
PUBKEY = G2ProofOfPossession.SkToPk(SECRET_KEY)


def _sha(data: bytes) -> bytes:
    """The SHA-256 digest of the bytes."""
    return hashlib.sha256(data).digest()


def _signature_root(signature: bytes) -> bytes:
    """The root of 96 bytes: three chunks, padded to four."""
    chunks = [signature[i : i + 32] for i in range(0, 96, 32)] + [ZERO]
    return _sha(_sha(chunks[0] + chunks[1]) + _sha(chunks[2] + chunks[3]))


def _example(fork: str, name: str) -> bytes:
    """The SSZ bytes of an example of a fork."""
    return (EXAMPLES / fork / f"{name}.ssz").read_bytes()


def _example_json(fork: str, name: str) -> Any:
    """The JSON value of an example of a fork."""
    return json.loads((EXAMPLES / fork / f"{name}.json").read_text())["value"]


def _split(data: bytes) -> tuple[bytes, bytes]:
    """The message and the signature of a signed container whose message has a variable size."""
    (offset,) = struct.unpack_from("<I", data, 0)
    assert offset == 4 + 96
    return data[offset:], data[4:offset]


def _message_root(name: str, fork: str, message: bytes) -> bytes:
    """The Lean root of a message, after checking that it re-encodes to the same bytes."""
    root, again = consensus.ssz_static("mainnet", fork, name, message)
    assert again == message
    return root


def _merkleize(chunks: list[bytes]) -> bytes:
    """The root of chunks of 32 bytes, padded with zero chunks to a power of two."""
    while len(chunks) & (len(chunks) - 1):
        chunks = [*chunks, ZERO]
    while len(chunks) > 1:
        chunks = [_sha(chunks[i] + chunks[i + 1]) for i in range(0, len(chunks), 2)]
    return chunks[0]


def _pubkey_root(pubkey: bytes) -> bytes:
    """The root of 48 bytes: two chunks."""
    return _merkleize([pubkey[:32], pubkey[32:].ljust(32, b"\0")])


def _registration_root(message: bytes) -> bytes:
    """The root of a registration, computed field by field in Python."""
    fee, gas, time, pubkey = message[:20], message[20:28], message[28:36], message[36:84]
    chunks = [fee.ljust(32, b"\0"), gas.ljust(32, b"\0"), time.ljust(32, b"\0")]
    return _merkleize([*chunks, _pubkey_root(pubkey)])


def _builder_domain(version: bytes | None = None) -> bytes:
    """The domain of the Builder API: a genesis fork version, zero validators root."""
    if version is None:
        version = bytes.fromhex(consensus.config("mainnet")["GENESIS_FORK_VERSION"][2:])
    fork_data_root = _sha(version + bytes(28) + ZERO)
    return bytes([0, 0, 0, 1]) + fork_data_root[:28]


def _sign(message_root: bytes, domain: bytes) -> bytes:
    """The signature of the secret key of the test over a root, under a domain."""
    return G2ProofOfPossession.Sign(SECRET_KEY, _sha(message_root + domain))


@pytest.mark.parametrize("source", VERSIONS)
@pytest.mark.parametrize(
    ("example", "name", "message"),
    [
        ("signed_builder_bid", "SignedBuilderBid", "BuilderBid"),
        ("signed_blinded_beacon_block", "SignedBlindedBeaconBlock", "BlindedBeaconBlock"),
    ],
    ids=["bid", "blinded block"],
)
def test_example(source: str, example: str, name: str, message: str):
    fork = consensus.consensus_version_fork(source)
    data = _example(source, example)
    root, again = consensus.ssz_static("mainnet", fork, name, data)
    assert again == data
    body, signature = _split(data)
    assert root == _sha(_message_root(message, fork, body) + _signature_root(signature))


@pytest.mark.parametrize("source", ["bellatrix", "capella"])
def test_bid_root(source: str):
    # Before Deneb a bid has three fields: the header, the value and the key.
    message, _ = _split(_example(source, "signed_builder_bid"))
    fork = consensus.consensus_version_fork(source)
    (offset,) = struct.unpack_from("<I", message, 0)
    header = _message_root("ExecutionPayloadHeader", fork, message[offset:])
    value, pubkey = message[4:36], message[36:84]
    expected = _merkleize([header, value, _pubkey_root(pubkey)])
    assert _message_root("BuilderBid", fork, message) == expected


@pytest.mark.parametrize("source", VERSIONS)
def test_bid_fields(source: str):
    # The fixture bytes agree with the JSON form, so the offsets of the helpers are right.
    message, _ = _split(_example(source, "signed_builder_bid"))
    expected = _example_json(source, "signed_builder_bid")["data"]["message"]
    at = VALUE_AT[source]
    assert int.from_bytes(message[at : at + 32], "little") == int(expected["value"])
    assert "0x" + message[at + 32 : at + 80].hex() == expected["pubkey"]


@pytest.mark.parametrize("source", VERSIONS)
def test_blinded_block_fields(source: str):
    # The fixture bytes agree with the JSON form; the root test reads the same bytes in Lean.
    message, _ = _split(_example(source, "signed_blinded_beacon_block"))
    expected = _example_json(source, "signed_blinded_beacon_block")["message"]
    slot, proposer = struct.unpack_from("<QQ", message, 0)
    assert (slot, proposer) == (int(expected["slot"]), int(expected["proposer_index"]))
    assert "0x" + message[16:48].hex() == expected["parent_root"]
    assert "0x" + message[48:80].hex() == expected["state_root"]


def test_registration_example():
    # A registration has a fixed size: its message, then its signature.
    data = _example("bellatrix", "signed_validator_registrations")
    [expected] = _example_json("bellatrix", "signed_validator_registrations")
    root, again = consensus.ssz_static(
        "mainnet", "bellatrix", "SignedValidatorRegistrationV1", data
    )
    assert again == data
    message, signature = data[:84], data[84:]
    assert _message_root("ValidatorRegistrationV1", "bellatrix", message) == _registration_root(
        message
    )
    assert root == _sha(_registration_root(message) + _signature_root(signature))
    fields = expected["message"]
    assert "0x" + message[:20].hex() == fields["fee_recipient"]
    assert struct.unpack_from("<QQ", message, 20) == (
        int(fields["gas_limit"]),
        int(fields["timestamp"]),
    )
    assert "0x" + message[36:84].hex() == fields["pubkey"]
    assert "0x" + signature.hex() == expected["signature"]


def _registration(gas_limit: int = 36_000_000, version: bytes | None = None) -> bytes:
    """A registration of the key of the test, signed under the domain of the Builder API."""
    message = bytes(20) + struct.pack("<QQ", gas_limit, 1_700_000_000) + PUBKEY
    return message + _sign(_registration_root(message), _builder_domain(version))


@pytest.mark.parametrize("source", VERSIONS)
def test_registration_signature(source: str):
    fork = consensus.consensus_version_fork(source)
    # The domain reads only the genesis fork version, so one signature holds at every fork.
    assert consensus.is_valid_builder_signature(
        "mainnet", fork, "SignedValidatorRegistrationV1", _registration()
    )


def test_registration_signature_of_another_chain():
    # A chain with another genesis fork version has another domain.
    version = bytes.fromhex("10000910")
    signed = _registration(version=version)
    config = {"GENESIS_FORK_VERSION": "0x" + version.hex()}
    kind = "SignedValidatorRegistrationV1"
    assert consensus.is_valid_builder_signature("mainnet", "bellatrix", kind, signed, config)
    assert not consensus.is_valid_builder_signature("mainnet", "bellatrix", kind, signed)


def test_registration_signature_of_another_message():
    signed = _registration()
    other = _registration(30_000_000)
    assert not consensus.is_valid_builder_signature(
        "mainnet", "bellatrix", "SignedValidatorRegistrationV1", other[:84] + signed[84:]
    )


def test_registration_signature_under_the_proposer_domain():
    # The same message signed under the domain type of a block does not pass.
    signed = _registration()
    root = _registration_root(signed[:84])
    domain = bytes(4) + _builder_domain()[4:]
    forged = signed[:84] + _sign(root, domain)
    assert not consensus.is_valid_builder_signature(
        "mainnet", "bellatrix", "SignedValidatorRegistrationV1", forged
    )


def test_registration_example_signature():
    # The example carries a placeholder signature.
    data = _example("bellatrix", "signed_validator_registrations")
    assert not consensus.is_valid_builder_signature(
        "mainnet", "bellatrix", "SignedValidatorRegistrationV1", data
    )


def _bid(source: str, pubkey: bytes = PUBKEY) -> bytes:
    """The example bid of a fork with a builder key, signed with the secret key of the test."""
    message, _ = _split(_example(source, "signed_builder_bid"))
    at = VALUE_AT[source] + 32
    message = message[:at] + pubkey + message[at + 48 :]
    root = _message_root("BuilderBid", consensus.consensus_version_fork(source), message)
    return struct.pack("<I", 4 + 96) + _sign(root, _builder_domain()) + message


@pytest.mark.parametrize("source", VERSIONS)
def test_bid_signature(source: str):
    assert consensus.is_valid_builder_signature(
        "mainnet", consensus.consensus_version_fork(source), "SignedBuilderBid", _bid(source)
    )


@pytest.mark.parametrize("source", VERSIONS)
def test_bid_signature_of_another_builder(source: str):
    # The message names another key than the one that signed it.
    other = G2ProofOfPossession.SkToPk(SECRET_KEY + 1)
    assert not consensus.is_valid_builder_signature(
        "mainnet", consensus.consensus_version_fork(source), "SignedBuilderBid", _bid(source, other)
    )


@pytest.mark.parametrize("fork", ["phase0", "altair", "glamsterdam"])
def test_no_builder_api_messages_outside_bellatrix_to_fulu(fork: str):
    with raises(ERROR, f"no Builder API messages at {fork}") as info:
        consensus.is_valid_builder_signature("mainnet", fork, "SignedBuilderBid", b"")
    assert info.value.code == 0


@pytest.mark.parametrize(
    "name", ["SignedBuilderBid", "SignedBlindedBeaconBlock", "ValidatorRegistrationV1"]
)
def test_no_container_at_gloas(name: str):
    with raises(ERROR, f"no container {name} at glamsterdam") as info:
        consensus.ssz_static("mainnet", "glamsterdam", name, b"")
    assert info.value.code == 0


def _list_root(roots: list[bytes], limit: int) -> bytes:
    """The root of a list: its element roots in a tree of `limit` leaves, then its length."""
    zero = ZERO
    level = roots
    width = 1
    while width < limit:
        if len(level) % 2:
            level = [*level, zero]
        level = [_sha(level[i] + level[i + 1]) for i in range(0, len(level), 2)]
        zero = _sha(zero + zero)
        width *= 2
    node = level[0] if level else zero
    return _sha(node + len(roots).to_bytes(32, "little"))


def _items(data: bytes, start: int, end: int, size: int) -> list[bytes]:
    """The fixed-size items of a list held between two offsets."""
    assert (end - start) % size == 0
    return [data[i : i + size] for i in range(start, end, size)]


def _bundle_root(bundle: bytes, proofs_limit: int) -> bytes:
    """The root of a blobs bundle, computed field by field in Python."""
    first, second, third = struct.unpack_from("<III", bundle, 0)
    commitments = _items(bundle, first, second, 48)
    proofs = _items(bundle, second, third, 48)
    blobs = _items(bundle, third, len(bundle), BLOB_SIZE)
    # A commitment and a proof are 48-byte vectors, so their roots are those of a public key.
    blob_roots = [_merkleize([blob[i : i + 32] for i in range(0, BLOB_SIZE, 32)]) for blob in blobs]
    return _merkleize(
        [
            _list_root([_pubkey_root(c) for c in commitments], MAX_BLOBS),
            _list_root([_pubkey_root(p) for p in proofs], proofs_limit),
            _list_root(blob_roots, MAX_BLOBS),
        ]
    )


@pytest.mark.parametrize("source", ["bellatrix", "capella"])
def test_execution_payload_example(source: str):
    # Before Deneb a builder reveals the payload alone; the example round-trips through Lean.
    fork = consensus.consensus_version_fork(source)
    data = _example(source, "execution_payload")
    _, again = consensus.ssz_static("mainnet", fork, "ExecutionPayload", data)
    assert again == data
    envelope = _example_json(source, "execution_payload")
    assert envelope["version"] == source
    expected = envelope["data"]
    # The block hash follows 472 bytes of fixed fields and offsets.
    assert "0x" + data[472:504].hex() == expected["block_hash"]


@pytest.mark.parametrize(
    ("source", "proofs_limit", "size"),
    [
        ("deneb", MAX_BLOBS, 131_919),
        ("electra", MAX_BLOBS, 131_919),
        # From Fulu the bound is the field elements of every extended blob.
        ("fulu", 2 * FIELD_ELEMENTS_PER_BLOB * MAX_BLOBS, 138_015),
    ],
)
def test_revealed_payload_and_blobs_bundle(source: str, proofs_limit: int, size: int):
    fork = consensus.consensus_version_fork(source)
    data = _example(source, "execution_payload_and_blobs_bundle")
    assert len(data) == size
    root, again = consensus.ssz_static("mainnet", fork, "ExecutionPayloadAndBlobsBundle", data)
    assert again == data
    payload_at, bundle_at = struct.unpack_from("<II", data, 0)
    payload, bundle = data[payload_at:bundle_at], data[bundle_at:]
    bundle_root, again = consensus.ssz_static("mainnet", fork, "BlobsBundle", bundle)
    assert again == bundle
    assert bundle_root == _bundle_root(bundle, proofs_limit)
    payload_root = _message_root("ExecutionPayload", fork, payload)
    assert root == _sha(payload_root + bundle_root)
    envelope = _example_json(source, "execution_payload_and_blobs_bundle")
    assert envelope["version"] == source
    expected = envelope["data"]["blobs_bundle"]
    first, second, third = struct.unpack_from("<III", bundle, 0)
    assert ["0x" + c.hex() for c in _items(bundle, first, second, 48)] == expected["commitments"]
    assert ["0x" + p.hex() for p in _items(bundle, second, third, 48)] == expected["proofs"]
    assert len(_items(bundle, third, len(bundle), BLOB_SIZE)) == len(expected["blobs"])


def _bundle_of_proofs(count: int) -> bytes:
    """A bundle with no commitment, no blob, and `count` zero proofs."""
    proofs = 48 * count
    return struct.pack("<III", 12, 12, 12 + proofs) + bytes(proofs)


def test_blobs_bundle_proofs_over_bound():
    # Before Fulu a bundle holds at most one proof per possible blob.
    message = f"input rejected: EthLib.Serialization.Ssz.Err.overLimit {MAX_BLOBS} {MAX_BLOBS + 1}"
    with raises(ERROR, message):
        consensus.ssz_static("mainnet", "dencun", "BlobsBundle", _bundle_of_proofs(MAX_BLOBS + 1))


def test_blobs_bundle_proofs_under_fulu_bound():
    # From Fulu the same bundle decodes, under the larger bound of the source.
    bundle = _bundle_of_proofs(MAX_BLOBS + 1)
    root, again = consensus.ssz_static("mainnet", "fusaka", "BlobsBundle", bundle)
    assert again == bundle
    assert root == _bundle_root(bundle, 2 * FIELD_ELEMENTS_PER_BLOB * MAX_BLOBS)


@pytest.mark.parametrize("fork", ["bellatrix", "shapella", "glamsterdam"])
@pytest.mark.parametrize("name", ["BlobsBundle", "ExecutionPayloadAndBlobsBundle"])
def test_no_blobs_bundle_outside_deneb_to_fulu(fork: str, name: str):
    with raises(ERROR, f"no container {name} at {fork}") as info:
        consensus.ssz_static("mainnet", fork, name, b"")
    assert info.value.code == 0


# The example of the payload that a builder reveals, by fork.
REVEALED = {
    "bellatrix": "execution_payload",
    "capella": "execution_payload",
    "deneb": "execution_payload_and_blobs_bundle",
    "electra": "execution_payload_and_blobs_bundle",
    "fulu": "execution_payload_and_blobs_bundle",
}
# The generalized index of the transactions root of a payload: 16 leaves before Deneb, 32 from it.
TRANSACTIONS_AT = {"bellatrix": 29, "capella": 29, "deneb": 45, "electra": 45, "fulu": 45}
# The header of a payload holds the transactions root after 504 bytes.
# From Capella the withdrawals root follows it.
HEADER_TRANSACTIONS_AT = 504


def _payload(source: str) -> bytes:
    """The payload alone of the example that a builder reveals at a fork."""
    data = _example(source, REVEALED[source])
    if source in ("bellatrix", "capella"):
        return data
    payload_at, bundle_at = struct.unpack_from("<II", data, 0)
    return data[payload_at:bundle_at]


def _header_at(signed: bytes) -> int:
    """Where the header of the payload starts in a signed blinded block."""
    (message_at,) = struct.unpack_from("<I", signed, 0)
    (body_at,) = struct.unpack_from("<I", signed, message_at + 80)
    # Before the header: the reveal, the eth1 vote, the graffiti, five offsets, the sync aggregate.
    (header_at,) = struct.unpack_from("<I", signed, message_at + body_at + 96 + 72 + 32 + 20 + 160)
    return message_at + body_at + header_at


def _matching_blinded(source: str) -> bytes:
    """The example blinded block, with the payload's transactions and withdrawals roots."""
    fork = consensus.consensus_version_fork(source)
    payload = _payload(source)
    signed = bytearray(_example(source, "signed_blinded_beacon_block"))
    at = _header_at(bytes(signed)) + HEADER_TRANSACTIONS_AT
    for offset in range(2 if source != "bellatrix" else 1):
        gindex = TRANSACTIONS_AT[source] + offset
        node, _ = consensus.merkle_proof("mainnet", fork, "ExecutionPayload", payload, gindex)
        signed[at + 32 * offset : at + 32 * offset + 32] = node
    return bytes(signed)


@pytest.mark.parametrize("source", VERSIONS)
def test_unblind(source: str):
    # A blinded block whose header is that of the payload unblinds to a block of the same root.
    fork = consensus.consensus_version_fork(source)
    blinded = _matching_blinded(source)
    blinded_root, _ = consensus.ssz_static("mainnet", fork, "SignedBlindedBeaconBlock", blinded)
    revealed = _example(source, REVEALED[source])
    result = consensus.unblind_signed_blinded_block("mainnet", fork, blinded, revealed)
    assert result is not None
    root, full = result
    assert consensus.ssz_static("mainnet", fork, "SignedBeaconBlock", full) == (root, full)
    # The block has the root of the blinded block, keeps its signature and holds the payload.
    assert root == blinded_root
    assert full[4:100] == blinded[4:100]
    assert _payload(source) in full


@pytest.mark.parametrize("source", VERSIONS)
def test_unblind_example_pair(source: str):
    # The pinned blinded block carries placeholder roots, so its header is not that of the payload.
    fork = consensus.consensus_version_fork(source)
    blinded = _example(source, "signed_blinded_beacon_block")
    revealed = _example(source, REVEALED[source])
    assert consensus.unblind_signed_blinded_block("mainnet", fork, blinded, revealed) is None


@pytest.mark.parametrize(
    ("source", "other", "message"),
    [
        ("deneb", "capella", "firstOffset 8 1309511375"),
        ("capella", "deneb", "firstOffset 512 1"),
    ],
    ids=["payload alone at deneb", "bundle at capella"],
)
def test_unblind_payload_of_another_form(source: str, other: str, message: str):
    # The fork chooses the form of the payload, and the other form does not decode.
    fork = consensus.consensus_version_fork(source)
    blinded = _example(source, "signed_blinded_beacon_block")
    revealed = _example(other, REVEALED[other])
    with raises(ERROR, f"payload rejected: EthLib.Serialization.Ssz.Err.{message}") as info:
        consensus.unblind_signed_blinded_block("mainnet", fork, blinded, revealed)
    assert info.value.code == 7


def test_unblind_changed_payload():
    # One bit of the block hash changes the header, so the payload no longer matches.
    blinded = _matching_blinded("deneb")
    revealed = bytearray(_example("deneb", REVEALED["deneb"]))
    (payload_at,) = struct.unpack_from("<I", revealed, 0)
    revealed[payload_at + 472] ^= 1
    assert (
        consensus.unblind_signed_blinded_block("mainnet", "dencun", blinded, bytes(revealed))
        is None
    )


@pytest.mark.parametrize("fork", ["altair", "glamsterdam"])
def test_no_unblinding_outside_bellatrix_to_fulu(fork: str):
    with raises(ERROR, f"no Builder API messages at {fork}") as info:
        consensus.unblind_signed_blinded_block("mainnet", fork, b"", b"")
    assert info.value.code == 0


def test_unknown_message():
    with raises(ERROR, "no signed message SignedBlindedBeaconBlock in the Builder API") as info:
        consensus.is_valid_builder_signature(
            "mainnet", "bellatrix", "SignedBlindedBeaconBlock", b""
        )
    assert info.value.code == 0


def _auth_message(data: bytes = b"builder.example.com", slot: int = 1) -> bytes:
    """The SSZ bytes of request authentication, with its variable data after the fixed part."""
    return struct.pack("<IQ", 12, slot) + data


def _auth_root(message: bytes) -> bytes:
    """The root of request authentication: its padded data and length, then its slot."""
    data = message[12:]
    chunks = [data[i : i + 32].ljust(32, b"\0") for i in range(0, len(data), 32)]
    chunks += [ZERO] * (128 - len(chunks))
    data_root = _sha(_merkleize(chunks) + len(data).to_bytes(32, "little"))
    return _sha(data_root + message[4:12] + bytes(24))


def _auth_domain(kind: bytes = bytes([11, 0, 0, 1])) -> bytes:
    """A domain at the mainnet genesis fork version, with a zero validators root."""
    return kind + _builder_domain()[4:]


def _signed_auth(message: bytes | None = None, domain: bytes | None = None) -> bytes:
    """Request authentication signed by the test key under the requested domain."""
    if message is None:
        message = _auth_message()
    if domain is None:
        domain = _auth_domain()
    return struct.pack("<I", 4 + 96) + _sign(_auth_root(message), domain) + message


@pytest.mark.parametrize("fork", ["glamsterdam", "hegota"])
def test_gloas_examples(fork: str):
    # The Gloas examples of the builder specification, against roots computed here.
    signed = _example("gloas", "signed_builder_request_auth")
    message, signature = _split(signed)
    expected = _example_json("gloas", "signed_builder_request_auth")
    assert message[12:] == bytes.fromhex(expected["message"]["data"][2:])
    assert struct.unpack_from("<Q", message, 4)[0] == int(expected["message"]["slot"])
    assert signature == bytes.fromhex(expected["signature"][2:])
    auth_root = _auth_root(message)
    assert _message_root("BuilderRequestAuth", fork, message) == auth_root
    signed_root = _sha(auth_root + _signature_root(signature))
    assert _message_root("SignedBuilderRequestAuth", fork, signed) == signed_root
    preferences = _example("gloas", "builder_preferences")
    expected_cap = _example_json("gloas", "builder_preferences")["max_execution_payment"]
    assert int.from_bytes(preferences, "little") == int(expected_cap)
    preferences_root = preferences + bytes(24)
    assert _message_root("BuilderPreferences", fork, preferences) == preferences_root
    request = _example("gloas", "builder_preferences_request")
    assert request[:8] == preferences
    assert struct.unpack_from("<I", request, 8)[0] == 12
    assert request[12:] == signed
    assert _message_root("BuilderPreferencesRequest", fork, request) == _sha(
        preferences_root + signed_root
    )


@pytest.mark.parametrize("fork", ["glamsterdam", "hegota"])
def test_builder_request_auth_signature(fork: str):
    assert consensus.verify_builder_request_auth_signature("mainnet", fork, PUBKEY, _signed_auth())


@pytest.mark.parametrize(
    "kind",
    [bytes(4), bytes([0, 0, 0, 1]), bytes([11, 0, 0, 0])],
    ids=["beacon proposer", "registrations and bids", "beacon builder"],
)
def test_builder_request_auth_wrong_domain(kind: bytes):
    signed = _signed_auth(domain=_auth_domain(kind))
    assert not consensus.verify_builder_request_auth_signature(
        "mainnet", "glamsterdam", PUBKEY, signed
    )


@pytest.mark.parametrize("message", [_auth_message(slot=2), _auth_message(b"other.example.com")])
def test_builder_request_auth_changed_message(message: bytes):
    signed = _signed_auth()[:100] + message
    assert not consensus.verify_builder_request_auth_signature(
        "mainnet", "glamsterdam", PUBKEY, signed
    )


def test_builder_request_auth_wrong_key():
    other = G2ProofOfPossession.SkToPk(SECRET_KEY + 1)
    assert not consensus.verify_builder_request_auth_signature(
        "mainnet", "glamsterdam", other, _signed_auth()
    )


def test_builder_request_auth_other_genesis_version():
    config = {"GENESIS_FORK_VERSION": "0x10000910"}
    domain = bytes([11, 0, 0, 1]) + _builder_domain(bytes.fromhex("10000910"))[4:]
    signed = _signed_auth(domain=domain)
    assert consensus.verify_builder_request_auth_signature(
        "mainnet", "glamsterdam", PUBKEY, signed, config
    )
    assert not consensus.verify_builder_request_auth_signature(
        "mainnet", "glamsterdam", PUBKEY, signed
    )


def test_builder_request_auth_placeholder_signature():
    assert not consensus.verify_builder_request_auth_signature(
        "mainnet", "glamsterdam", PUBKEY, _example("gloas", "signed_builder_request_auth")
    )


def test_builder_request_auth_data_limit():
    message = _auth_message(bytes(4096))
    assert _message_root("BuilderRequestAuth", "glamsterdam", message) == _auth_root(message)
    with raises(ERROR, "input rejected: EthLib.Serialization.Ssz.Err.overLimit 4096 4097"):
        consensus.ssz_static(
            "mainnet", "glamsterdam", "BuilderRequestAuth", _auth_message(bytes(4097))
        )


@pytest.mark.parametrize(
    "kind",
    [
        "BuilderRequestAuth",
        "SignedBuilderRequestAuth",
        "BuilderPreferences",
        "BuilderPreferencesRequest",
    ],
)
def test_no_gloas_builder_container_before_gloas(kind: str):
    with raises(ERROR, f"no container {kind} at fusaka") as info:
        consensus.ssz_static("mainnet", "fusaka", kind, b"")
    assert info.value.code == 0


def test_no_request_authentication_before_gloas():
    with raises(ERROR, "no builder request authentication at fusaka") as info:
        consensus.verify_builder_request_auth_signature("mainnet", "fusaka", PUBKEY, b"")
    assert info.value.code == 0


# The data that the test signs in a request authentication, as its builder agreed it.
AGREED = b"builder.example.com"
# The data of the pinned Gloas examples.
PINNED_DATA = bytes.fromhex("1234567890abcdef")


def _auth_failures(
    signed: bytes,
    agreed: bytes = AGREED,
    path_slot: int = 1,
    pubkey: bytes = PUBKEY,
    header: str | None = "gloas",
    fork: str = "glamsterdam",
) -> list[str]:
    """The failed checks of a request for a bid."""
    return consensus.builder_request_auth_failures(
        "mainnet", fork, agreed, path_slot, pubkey, header, signed
    )


def _preferences_request(signed: bytes, cap: int = 10**9) -> bytes:
    """The SSZ bytes of a preferences request: the cap, then the offset of the authentication."""
    return struct.pack("<QI", cap, 12) + signed


def _preferences_failures(
    request: bytes,
    current_slot: int = 1,
    agreed: bytes = AGREED,
    pubkey: bytes = PUBKEY,
    header: str | None = "gloas",
) -> list[str]:
    """The failed checks of a request that submits preferences, at Gloas."""
    return consensus.builder_preferences_failures(
        "mainnet", "glamsterdam", agreed, current_slot, pubkey, header, request
    )


def _pinned_signed_auth() -> bytes:
    """The pinned authentication, signed again by the test key in place of its placeholder."""
    return _signed_auth(_example("gloas", "signed_builder_request_auth")[100:])


def _pinned_request() -> bytes:
    """The pinned preferences request, with its authentication signed by the test key."""
    request = _example("gloas", "builder_preferences_request")
    return request[:12] + _signed_auth(request[112:])


@pytest.mark.parametrize("fork", ["glamsterdam", "hegota"])
def test_request_auth_passes(fork: str):
    assert _auth_failures(_signed_auth(), fork=fork) == []


@pytest.mark.parametrize(
    ("change", "failures"),
    [
        ({"path_slot": 2}, ["slot_mismatch"]),
        ({"agreed": b"other.example.com"}, ["data_mismatch"]),
        ({"pubkey": G2ProofOfPossession.SkToPk(SECRET_KEY + 1)}, ["bad_signature"]),
        ({"header": None}, ["bad_version"]),
        ({"header": ""}, ["bad_version"]),
        ({"header": "phase0"}, ["bad_version"]),
        ({"header": "fulu"}, ["bad_version"]),
        ({"header": "Gloas"}, ["bad_version"]),
        ({"header": " gloas"}, ["bad_version"]),
    ],
    ids=[
        "other slot",
        "other data",
        "other key",
        "no header",
        "empty header",
        "phase0",
        "fork before the body",
        "wrong case",
        "space",
    ],
)
def test_request_auth_one_failure(change: dict[str, Any], failures: list[str]):
    assert _auth_failures(_signed_auth(), **change) == failures


def test_request_auth_empty_data():
    # Empty data fails even when the agreed data is empty too.
    signed = _signed_auth(_auth_message(b""))
    assert _auth_failures(signed, agreed=b"") == ["empty_data"]
    assert _auth_failures(signed) == ["empty_data", "data_mismatch"]


def test_request_auth_every_failure():
    # Every failed check is listed, in the order of the checks: the header comes first.
    signed = _signed_auth(_auth_message(b""))
    other = G2ProofOfPossession.SkToPk(SECRET_KEY + 1)
    assert _auth_failures(signed, path_slot=2, pubkey=other, header=None) == [
        "bad_version",
        "empty_data",
        "data_mismatch",
        "slot_mismatch",
        "bad_signature",
    ]


def test_request_auth_pinned_example():
    # The pinned example carries a placeholder signature, so only that check fails.
    signed = _example("gloas", "signed_builder_request_auth")
    assert _auth_failures(signed, agreed=PINNED_DATA) == ["bad_signature"]


def test_request_auth_pinned_example_signed():
    signed = _pinned_signed_auth()
    assert _auth_failures(signed, agreed=PINNED_DATA) == []
    assert _auth_failures(signed, agreed=PINNED_DATA, path_slot=2) == ["slot_mismatch"]


def test_request_auth_other_genesis_version():
    # The configuration reaches the signature check through the domain.
    config = {"GENESIS_FORK_VERSION": "0x10000910"}
    domain = bytes([11, 0, 0, 1]) + _builder_domain(bytes.fromhex("10000910"))[4:]
    signed = _signed_auth(domain=domain)
    args = ("mainnet", "glamsterdam", AGREED, 1, PUBKEY, "gloas", signed)
    assert consensus.builder_request_auth_failures(*args, config) == []
    assert consensus.builder_request_auth_failures(*args) == ["bad_signature"]


def test_preferences_pinned_example_signed():
    # The slot of the request has not passed at the builder's slot 1, since 1 < 1 is false.
    request = _pinned_request()
    assert _preferences_failures(request, agreed=PINNED_DATA) == []
    assert _preferences_failures(request, current_slot=2, agreed=PINNED_DATA) == ["slot_passed"]


def test_preferences_for_a_later_slot():
    # A request ahead of the builder's slot passes: only a past slot fails.
    assert _preferences_failures(_preferences_request(_signed_auth()), current_slot=0) == []


def test_preferences_signature_does_not_cover_the_cap():
    # The signature covers the data and the slot, so another cap keeps it valid.
    assert _preferences_failures(_preferences_request(_signed_auth(), cap=0)) == []


def test_preferences_every_failure():
    request = _preferences_request(_signed_auth(_auth_message(b"")))
    other = G2ProofOfPossession.SkToPk(SECRET_KEY + 1)
    assert _preferences_failures(request, current_slot=2, pubkey=other, header=None) == [
        "bad_version",
        "empty_data",
        "data_mismatch",
        "slot_passed",
        "bad_signature",
    ]


def test_preferences_pinned_example():
    request = _example("gloas", "builder_preferences_request")
    assert _preferences_failures(request, agreed=PINNED_DATA) == ["bad_signature"]
    assert _preferences_failures(request, current_slot=2, agreed=PINNED_DATA) == [
        "slot_passed",
        "bad_signature",
    ]


def test_request_checks_malformed_body():
    with raises(ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 100 0") as info:
        _auth_failures(b"")
    assert info.value.code == 4
    request = struct.pack("<QI", 0, 13) + _signed_auth()
    with raises(ERROR, "input rejected: EthLib.Serialization.Ssz.Err.firstOffset 12 13") as info:
        _preferences_failures(request)
    assert info.value.code == 7


def test_no_request_checks_before_gloas():
    with raises(ERROR, "no builder request authentication at fusaka") as info:
        _auth_failures(_signed_auth(), fork="fusaka")
    assert info.value.code == 0
    with raises(ERROR, "no builder request authentication at fusaka") as info:
        consensus.builder_preferences_failures("mainnet", "fusaka", AGREED, 1, PUBKEY, "gloas", b"")
    assert info.value.code == 0


def test_builder_request_auth_short_key():
    with raises(ERROR, "expected 48 bytes, got 47") as info:
        consensus.verify_builder_request_auth_signature(
            "mainnet", "glamsterdam", PUBKEY[:47], _signed_auth()
        )
    assert info.value.code == 0


def test_builder_request_auth_over_limit():
    with raises(ERROR, "input rejected: EthLib.Serialization.Ssz.Err.overLimit 4096 4097"):
        consensus.verify_builder_request_auth_signature(
            "mainnet", "glamsterdam", PUBKEY, _signed_auth(_auth_message(bytes(4097)))
        )


@pytest.mark.parametrize(
    ("value", "payment", "cap", "expected"),
    [
        (1_000_000_000, 5_000_000_000, 0, 1_000_000_000),
        (1_000_000_000, 5_000_000_000, 2**64 - 1, 6_000_000_000),
        (1, 5, 3, 4),
        (2**64 - 1, 2**64 - 1, 2**64 - 1, 2**65 - 2),
    ],
)
def test_builder_bid_value(value: int, payment: int, cap: int, expected: int):
    assert consensus.builder_bid_value(value, payment, cap) == expected


@pytest.mark.parametrize("value", [2**64, 2**64 + 1])
@pytest.mark.parametrize("position", range(3))
def test_builder_bid_value_out_of_range(value: int, position: int):
    # Lean reads each amount as a 64-bit number, and rejects a larger one instead of reducing it.
    amounts = [1, 5, 3]
    amounts[position] = value
    with raises(consensus.ConsensusError, f"expected an int below {2**64}, got {value}") as info:
        consensus.builder_bid_value(*amounts)
    assert info.value.code == 0


# A minimal Bellatrix state of the consensus tests, whose validator i has the secret key i + 1.
STATE = (
    Path(__file__).resolve().parents[4]
    / "tests/consensus/light_client/minimal/bellatrix/light_client/single_merkle_proof"
    / "BeaconState/current_sync_committee_merkle_proof/object.ssz_snappy"
)
# The validator of the registrations below, and its secret key.
INDEX = 3
# A registration message: fee recipient, gas limit, timestamp and key.
MESSAGE_SIZE = 20 + 8 + 8 + 48
REGISTRANT_KEY = INDEX + 1
# The activation epoch follows the key, credentials, balance, slashed flag and eligibility.
ACTIVATION_AFTER_KEY = 48 + 32 + 8 + 1 + 8
FAR_FUTURE = 2**64 - 1


def _state() -> bytes:
    """The pinned state, which every registration below reads."""
    return snappy.decompress(STATE.read_bytes())


def _with_epochs(state: bytes, activation: int, exit_epoch: int) -> bytes:
    """The state with new activation and exit epochs for the registering validator."""
    at = state.index(G2ProofOfPossession.SkToPk(REGISTRANT_KEY)) + ACTIVATION_AFTER_KEY
    return state[:at] + struct.pack("<QQ", activation, exit_epoch) + state[at + 16 :]


def _signed_registration(timestamp: int, key: int = REGISTRANT_KEY) -> bytes:
    """A registration of a key at a time, signed by that key under the Builder API domain."""
    pubkey = G2ProofOfPossession.SkToPk(key)
    message = bytes(20) + struct.pack("<QQ", 30_000_000, timestamp) + pubkey
    # The minimal configuration has its own genesis fork version, which enters the domain.
    version = bytes.fromhex(consensus.config("minimal")["GENESIS_FORK_VERSION"][2:])
    root = _sha(_registration_root(message) + _builder_domain(version))
    return message + G2ProofOfPossession.Sign(key, root)


def _register(
    signed: bytes, now: int, state: bytes | None = None, kept: Sequence[bytes] = ()
) -> str | None:
    """The rule that refuses a registration on the pinned state, or None when it is kept."""
    state = _state() if state is None else state
    return consensus.process_registration("minimal", "bellatrix", state, list(kept), signed, now)


@pytest.mark.parametrize(
    ("now", "expected"),
    [(89, "too_far_in_future"), (90, None), (100, None)],
    ids=["eleven seconds ahead", "ten seconds ahead", "on time"],
)
def test_registration_lookahead(now: int, expected: str | None):
    # A registration may be at most ten seconds ahead of the builder's clock.
    assert _register(_signed_registration(100), now) == expected


def test_registration_older_than_kept():
    kept = _signed_registration(101)[:MESSAGE_SIZE]
    assert _register(_signed_registration(100), 100, kept=[kept]) == "older_than_previous"
    assert _register(_signed_registration(101), 100, kept=[kept]) is None


def test_registration_of_unknown_key():
    assert _register(_signed_registration(100, key=10**6), 100) == "unknown_validator"


def test_registration_of_exited_validator():
    state = _with_epochs(_state(), 0, 0)
    assert _register(_signed_registration(100), 100, state) == "not_eligible"


def test_registration_of_pending_validator():
    # A validator whose activation is still ahead may register.
    state = _with_epochs(_state(), FAR_FUTURE, FAR_FUTURE)
    assert _register(_signed_registration(100), 100, state) is None


def test_registration_with_another_signature():
    signed = _signed_registration(100)
    other = _signed_registration(101)
    assert _register(signed[:MESSAGE_SIZE] + other[MESSAGE_SIZE:], 100) == "bad_signature"


def test_registration_clock_overflow():
    # The source adds the lookahead to the clock as a 64-bit integer, which fails at the end.
    assert _register(_signed_registration(100), 2**64 - 10) == "clock_overflow"
    assert _register(_signed_registration(100), 2**64 - 11) is None


def test_registration_rules_in_order():
    # The first rule that fails names the refusal.
    signed = _signed_registration(150, key=10**6)
    assert _register(signed[:MESSAGE_SIZE] + bytes(96), 100) == "unknown_validator"
    state = _with_epochs(_state(), 0, 0)
    assert _register(_signed_registration(150), 100, state) == "not_eligible"


# Where a minimal state stores the offset of its latest payload header, from Bellatrix to Fulu.
HEADER_OFFSET_AT = 10_229
# The block hash follows 472 bytes of the header.
# They hold the parent hash, the fee recipient, two roots, the bloom and the RANDAO mix.
# Four numbers, the offset of the extra data and the base fee come next.
BLOCK_HASH_IN_HEADER = 472
# The slot follows the genesis time and the genesis validators root.
SLOT_AT = 40
# A fee recipient that no pinned bid names.
OTHER_RECIPIENT = bytes(19) + b"\x13"


def _fork_state(source: str) -> bytes:
    """The pinned minimal state of the fork of a consensus version."""
    path = (
        Path(__file__).resolve().parents[4]
        / f"tests/consensus/light_client/minimal/{source}/light_client/single_merkle_proof"
        / "BeaconState/current_sync_committee_merkle_proof/object.ssz_snappy"
    )
    return snappy.decompress(path.read_bytes())


def _block_hash_at(state: bytes) -> int:
    """The position of the block hash of the latest payload header of a minimal state."""
    (header,) = struct.unpack_from("<I", state, HEADER_OFFSET_AT)
    return header + BLOCK_HASH_IN_HEADER


def _with_block_hash(state: bytes, block_hash: bytes) -> bytes:
    """The state with another block hash in its latest payload header."""
    at = _block_hash_at(state)
    return state[:at] + block_hash + state[at + 32 :]


def _minimal_bid(source: str, key: int = SECRET_KEY) -> bytes:
    """The example bid of a fork, with the test key as builder, signed for the minimal chain."""
    message, _ = _split(_example(source, "signed_builder_bid"))
    at = VALUE_AT[source] + 32
    message = message[:at] + PUBKEY + message[at + 48 :]
    fork = consensus.consensus_version_fork(source)
    root, again = consensus.ssz_static("minimal", fork, "BuilderBid", message)
    assert again == message
    version = bytes.fromhex(consensus.config("minimal")["GENESIS_FORK_VERSION"][2:])
    signature = G2ProofOfPossession.Sign(key, _sha(root + _builder_domain(version)))
    return struct.pack("<I", 4 + 96) + signature + message


def _bid_header(signed: bytes) -> tuple[bytes, bytes]:
    """The parent hash and the fee recipient of the header of a signed bid."""
    message, _ = _split(signed)
    (header,) = struct.unpack_from("<I", message, 0)
    return message[header : header + 32], message[header + 32 : header + 52]


def _process_bid(source: str, state: bytes, signed: bytes, fee_recipient: bytes) -> str | None:
    """The rule that refuses a bid on a minimal state, or None when the proposer accepts it."""
    fork = consensus.consensus_version_fork(source)
    return consensus.process_bid("minimal", fork, state, signed, fee_recipient)


@pytest.mark.parametrize("source", VERSIONS)
def test_process_bid(source: str):
    signed = _minimal_bid(source)
    parent, recipient = _bid_header(signed)
    state = _with_block_hash(_fork_state(source), parent)
    assert _process_bid(source, state, signed, recipient) is None
    assert _process_bid(source, state, signed, OTHER_RECIPIENT) == "wrong_fee_recipient"
    other_parent = bytes(a ^ 1 for a in parent)
    moved = _with_block_hash(state, other_parent)
    assert _process_bid(source, moved, signed, recipient) == "wrong_parent_hash"
    # The rules run in order: the parent hash is checked before the fee recipient.
    assert _process_bid(source, moved, signed, OTHER_RECIPIENT) == "wrong_parent_hash"


@pytest.mark.parametrize("source", VERSIONS)
def test_process_bid_signed_by_another_key(source: str):
    # The bid names the test key, and another key signed it.
    signed = _minimal_bid(source, key=SECRET_KEY + 1)
    parent, recipient = _bid_header(signed)
    state = _with_block_hash(_fork_state(source), parent)
    assert _process_bid(source, state, signed, recipient) == "bad_signature"
    # The signature is checked last.
    assert _process_bid(source, state, signed, OTHER_RECIPIENT) == "wrong_fee_recipient"
    moved = _with_block_hash(state, bytes(a ^ 1 for a in parent))
    assert _process_bid(source, moved, signed, recipient) == "wrong_parent_hash"


def _proposer(source: str, state: bytes) -> int:
    """The index of the proposer of the slot of a minimal state."""
    fork = consensus.consensus_version_fork(source)
    index = 0
    while not consensus.is_proposer("minimal", fork, state, index):
        index += 1
    return index


def _registered(index: int) -> bytes:
    """A registration message of a validator of the pinned states, whose secret key is index + 1."""
    pubkey = G2ProofOfPossession.SkToPk(index + 1)
    return bytes(20) + struct.pack("<QQ", 30_000_000, 100) + pubkey


def _eligible(
    source: str, state: bytes, kept: Sequence[bytes], slot: int, parent: bytes, pubkey: bytes
) -> bool:
    """Whether a builder serves a request for a bid on a minimal state."""
    fork = consensus.consensus_version_fork(source)
    return consensus.is_eligible_for_bid("minimal", fork, state, list(kept), slot, parent, pubkey)


@pytest.mark.parametrize("source", VERSIONS)
def test_is_eligible_for_bid(source: str):
    state = _fork_state(source)
    (slot,) = struct.unpack_from("<Q", state, SLOT_AT)
    at = _block_hash_at(state)
    parent = state[at : at + 32]
    proposer = _proposer(source, state)
    other = proposer + 1
    pubkey = G2ProofOfPossession.SkToPk(proposer + 1)
    kept = [_registered(proposer), _registered(other)]
    assert _eligible(source, state, kept, slot, parent, pubkey)
    # A request for another slot than that of the state.
    assert not _eligible(source, state, kept, slot + 1, parent, pubkey)
    # A proposer that has not registered.
    assert not _eligible(source, state, kept[1:], slot, parent, pubkey)
    # A registered validator that does not propose at the slot.
    other_key = G2ProofOfPossession.SkToPk(other + 1)
    assert not _eligible(source, state, kept, slot, parent, other_key)
    # Another parent hash than the latest block hash of the state.
    assert not _eligible(source, state, kept, slot, bytes(a ^ 1 for a in parent), pubkey)


@pytest.mark.parametrize("fork", ["altair", "glamsterdam"])
def test_no_bids_outside_bellatrix_to_fulu(fork: str):
    with raises(ERROR, f"no Builder API messages at {fork}") as info:
        consensus.process_bid("minimal", fork, b"", b"", bytes(20))
    assert info.value.code == 0
    with raises(TransitionError, f"no Builder API messages at {fork}") as info:
        consensus.is_eligible_for_bid("minimal", fork, b"", [], 0, ZERO, bytes(48))
    assert info.value.code == 0


def test_is_eligible_for_bid_state_that_does_not_decode():
    with raises(
        TransitionError, "state rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 10233 0"
    ) as info:
        consensus.is_eligible_for_bid("minimal", "bellatrix", b"", [], 0, ZERO, bytes(48))
    assert info.value.code == 0
