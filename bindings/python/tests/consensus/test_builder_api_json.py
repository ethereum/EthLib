"""The JSON bodies of the Builder API against the examples of the builder specification."""

import json
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy
from raising import raises

# The examples of the builder specification, pinned in tests/sources.toml.
EXAMPLES = Path(__file__).resolve().parents[4] / "tests/consensus/builder_api"

# The container of each example whose body carries its version.
VERSIONED = {
    "signed_builder_bid": "SignedBuilderBid",
    "execution_payload": "ExecutionPayload",
    "execution_payload_and_blobs_bundle": "ExecutionPayloadAndBlobsBundle",
}
# The examples whose body is the data alone, which test_beacon_api_json.py reads.
PLAIN = {
    "signed_blinded_beacon_block",
    "builder_preferences",
    "builder_preferences_request",
    "signed_builder_request_auth",
}
# The body of a registration request is a JSON array of this container.
REGISTRATION = ("signed_validator_registrations", "SignedValidatorRegistrationV1")

# A Gloas bid of the consensus test vectors, since the builder specification has no such example.
GLOAS_BID = (
    Path(__file__).resolve().parents[4]
    / "tests/consensus/ssz_static/mainnet/gloas/ssz_static/SignedExecutionPayloadBid"
    / "ssz_random/case_0/serialized.ssz_snappy"
)

# Every JSON example, as (directory, file name without the suffix).
FILES = sorted((path.parent.name, path.stem) for path in EXAMPLES.glob("*/*.json"))
# Every SSZ example, named the same way.
SSZ_FILES = sorted((path.parent.name, path.stem) for path in EXAMPLES.glob("*/*.ssz"))


def _example(version: str, name: str) -> tuple[bytes, Any]:
    """The SSZ bytes of an example and the JSON body, which the file holds under `value`."""
    data = (EXAMPLES / version / f"{name}.ssz").read_bytes()
    return data, json.loads((EXAMPLES / version / f"{name}.json").read_text())["value"]


def test_every_example_has_a_container():
    names = {name for _, name in FILES}
    assert names == {*VERSIONED, *PLAIN, REGISTRATION[0]}
    assert len(FILES) == 19
    assert SSZ_FILES == FILES


@pytest.mark.parametrize(("version", "name"), [f for f in FILES if f[1] in VERSIONED])
def test_versioned_body(version: str, name: str):
    fork = consensus.consensus_version_fork(version)
    data, body = _example(version, name)
    assert body["version"] == version
    assert consensus.builder_api_ssz("mainnet", fork, VERSIONED[name], body) == data
    assert consensus.builder_api_json("mainnet", fork, VERSIONED[name], data) == body


def test_gloas_bid_body():
    # No independent JSON of a Gloas bid exists, so this pins the envelope and the round trip.
    data = snappy.decompress(GLOAS_BID.read_bytes())
    name = "SignedExecutionPayloadBid"
    body = consensus.builder_api_json("mainnet", "glamsterdam", name, data)
    assert body == {
        "version": "gloas",
        "data": consensus.api_json("mainnet", "glamsterdam", name, data),
    }
    assert consensus.builder_api_ssz("mainnet", "glamsterdam", name, body) == data


def test_registrations_body():
    # The elements have a fixed size, so the SSZ list is their encodings end to end.
    name, container = REGISTRATION
    data, body = _example("bellatrix", name)
    parts = [consensus.api_ssz("mainnet", "bellatrix", container, item) for item in body]
    assert b"".join(parts) == data
    assert [consensus.api_json("mainnet", "bellatrix", container, part) for part in parts] == body


@pytest.mark.parametrize(
    ("fork", "version", "message"),
    [
        # A Capella node refuses the Bellatrix bid on its version, before it reads the data.
        ("shapella", "bellatrix", "version bellatrix, expected capella"),
        ("bellatrix", "capella", "version capella, expected bellatrix"),
        # A name that the Builder API does not list, and one that is no consensus version.
        ("bellatrix", "phase0", "version phase0, expected bellatrix"),
        ("bellatrix", "Bellatrix", "malformed version"),
    ],
)
def test_body_of_another_version(fork: str, version: str, message: str):
    _, body = _example("bellatrix", "signed_builder_bid")
    renamed = {**body, "version": version}
    with raises(SszError, f"body rejected: {message}") as info:
        consensus.builder_api_ssz("mainnet", fork, "SignedBuilderBid", renamed)
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("edit", "message"),
    [
        (lambda body: {"data": body["data"]}, "version absent, expected bellatrix"),
        (lambda body: {"version": body["version"]}, "no data"),
        (lambda body: [body], "not an object"),
    ],
    ids=["no version", "no data", "array"],
)
def test_body_that_is_no_envelope(edit: Callable[[Any], Any], message: str):
    _, body = _example("bellatrix", "signed_builder_bid")
    with raises(SszError, f"body rejected: {message}") as info:
        consensus.builder_api_ssz("mainnet", "bellatrix", "SignedBuilderBid", edit(body))
    assert info.value.code == 0


def test_body_with_a_malformed_beacon_key():
    # The Builder API defines no such key; the reader checks it as the Beacon API does.
    _, body = _example("bellatrix", "signed_builder_bid")
    edited = {**body, "execution_optimistic": "yes"}
    with raises(SszError, "body rejected: malformed execution_optimistic") as info:
        consensus.builder_api_ssz("mainnet", "bellatrix", "SignedBuilderBid", edited)
    assert info.value.code == 0


def test_body_with_another_key():
    data, body = _example("bellatrix", "signed_builder_bid")
    assert (
        consensus.builder_api_ssz("mainnet", "bellatrix", "SignedBuilderBid", {**body, "x": 1})
        == data
    )


def test_bytes_that_do_not_decode():
    data, _ = _example("bellatrix", "signed_builder_bid")
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err.overLimit 32 33") as info:
        consensus.builder_api_json("mainnet", "bellatrix", "SignedBuilderBid", data + b"\0")
    assert info.value.code == 2


def test_body_whose_data_does_not_read():
    # The data keeps the code of its SSZ error, unlike a fault of the envelope.
    _, body = _example("bellatrix", "signed_builder_bid")
    with raises(
        SszError, 'document rejected: EthLib.Serialization.Ssz.Err.missingField "message"'
    ) as info:
        consensus.builder_api_ssz("mainnet", "bellatrix", "SignedBuilderBid", {**body, "data": {}})
    assert info.value.code == 73


@pytest.mark.parametrize(
    ("fork", "name", "message"),
    [
        pytest.param("phase0", "SignedBuilderBid", "no Builder API version at phase0", id="before"),
        pytest.param(
            "hegota",
            "SignedExecutionPayloadBid",
            "no Builder API version at hegota",
            id="after",
        ),
        pytest.param(
            "glamsterdam",
            "SignedBuilderBid",
            "no versioned body SignedBuilderBid at glamsterdam",
            id="bid at gloas",
        ),
        pytest.param(
            "dencun",
            "ExecutionPayload",
            "no versioned body ExecutionPayload at dencun",
            id="payload at deneb",
        ),
        pytest.param(
            "shapella",
            "ExecutionPayloadAndBlobsBundle",
            "no versioned body ExecutionPayloadAndBlobsBundle at shapella",
            id="bundle at capella",
        ),
        pytest.param(
            "glamsterdam",
            "ExecutionPayloadAndBlobsBundle",
            "no versioned body ExecutionPayloadAndBlobsBundle at glamsterdam",
            id="bundle at gloas",
        ),
        pytest.param(
            "fusaka",
            "SignedExecutionPayloadBid",
            "no versioned body SignedExecutionPayloadBid at fusaka",
            id="gloas bid at fulu",
        ),
        pytest.param(
            "bellatrix",
            "SignedBlindedBeaconBlock",
            "no versioned body SignedBlindedBeaconBlock at bellatrix",
            id="request body",
        ),
    ],
)
def test_no_versioned_body(fork: str, name: str, message: str):
    with raises(SszError, message) as info:
        consensus.builder_api_json("mainnet", fork, name, b"")
    assert info.value.code == 0
    with raises(SszError, message) as info:
        consensus.builder_api_ssz("mainnet", fork, name, {})
    assert info.value.code == 0
