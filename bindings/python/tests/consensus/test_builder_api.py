"""The Builder API containers and signatures against the examples of the builder specification."""

import hashlib
import json
import struct
from pathlib import Path
from typing import Any

import pytest
from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from ethlib.errors import SszError
from raising import raises

ERROR = SszError
# The examples of the builder specification, pinned in tests/sources.toml.
EXAMPLES = Path(__file__).resolve().parents[4] / "tests/consensus/builder_api"
# Each fork of the examples, with its name in Lean.
FORKS = {
    "bellatrix": "bellatrix",
    "capella": "shapella",
    "deneb": "dencun",
    "electra": "pectra",
    "fulu": "fusaka",
}
# The offset of the value in a bid: 4 bytes per variable-size field before it.
VALUE_AT = {"bellatrix": 4, "capella": 4, "deneb": 8, "electra": 12, "fulu": 12}
ZERO = bytes(32)
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


@pytest.mark.parametrize("source", FORKS)
@pytest.mark.parametrize(
    ("example", "name", "message"),
    [
        ("signed_builder_bid", "SignedBuilderBid", "BuilderBid"),
        ("signed_blinded_beacon_block", "SignedBlindedBeaconBlock", "BlindedBeaconBlock"),
    ],
    ids=["bid", "blinded block"],
)
def test_example(source: str, example: str, name: str, message: str):
    data = _example(source, example)
    root, again = consensus.ssz_static("mainnet", FORKS[source], name, data)
    assert again == data
    body, signature = _split(data)
    assert root == _sha(_message_root(message, FORKS[source], body) + _signature_root(signature))


@pytest.mark.parametrize("source", ["bellatrix", "capella"])
def test_bid_root(source: str):
    # Before Deneb a bid has three fields: the header, the value and the key.
    message, _ = _split(_example(source, "signed_builder_bid"))
    (offset,) = struct.unpack_from("<I", message, 0)
    header = _message_root("ExecutionPayloadHeader", FORKS[source], message[offset:])
    value, pubkey = message[4:36], message[36:84]
    expected = _merkleize([header, value, _pubkey_root(pubkey)])
    assert _message_root("BuilderBid", FORKS[source], message) == expected


@pytest.mark.parametrize("source", FORKS)
def test_bid_fields(source: str):
    # The fixture bytes agree with the JSON form, so the offsets of the helpers are right.
    message, _ = _split(_example(source, "signed_builder_bid"))
    expected = _example_json(source, "signed_builder_bid")["data"]["message"]
    at = VALUE_AT[source]
    assert int.from_bytes(message[at : at + 32], "little") == int(expected["value"])
    assert "0x" + message[at + 32 : at + 80].hex() == expected["pubkey"]


@pytest.mark.parametrize("source", FORKS)
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


@pytest.mark.parametrize("fork", FORKS.values())
def test_registration_signature(fork: str):
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
    root = _message_root("BuilderBid", FORKS[source], message)
    return struct.pack("<I", 4 + 96) + _sign(root, _builder_domain()) + message


@pytest.mark.parametrize("source", FORKS)
def test_bid_signature(source: str):
    assert consensus.is_valid_builder_signature(
        "mainnet", FORKS[source], "SignedBuilderBid", _bid(source)
    )


@pytest.mark.parametrize("source", FORKS)
def test_bid_signature_of_another_builder(source: str):
    # The message names another key than the one that signed it.
    other = G2ProofOfPossession.SkToPk(SECRET_KEY + 1)
    assert not consensus.is_valid_builder_signature(
        "mainnet", FORKS[source], "SignedBuilderBid", _bid(source, other)
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


def test_unknown_message():
    with raises(ERROR, "no signed message SignedBlindedBeaconBlock in the Builder API") as info:
        consensus.is_valid_builder_signature(
            "mainnet", "bellatrix", "SignedBlindedBeaconBlock", b""
        )
    assert info.value.code == 0
