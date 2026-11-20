"""The requests of the Remote-signing API against the examples of its sign endpoint."""

import copy
from pathlib import Path
from typing import Any

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from raising import raises

ERROR = consensus.RemoteSigningError
# The start of the message of every refused request.
REJECTED = "request rejected: EthLib.Consensus.RemoteSigningApi.RequestError."

# Most examples read under either preset, but five fix the size of a bitfield.
# The Altair block has 4 bytes of sync committee bits, the size of the minimal preset.
# The contribution has 1 byte of aggregation bits, the size of the minimal preset.
# The Electra, Fulu and Gloas aggregates have 8 bytes of committee bits, as the mainnet preset has.
# Each of them is refused under the other preset, at the key of the field it puts in the request.
_BAD = f"{REJECTED}badField"

# The preset of the tests that change one example.
PRESET = "minimal"
MINIMAL_ONLY = {
    "BLOCK_V2 (ALTAIR)": f'{_BAD} "block" (EthLib.Serialization.Ssz.Err.scope 64 4)',
    "SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF": (
        f'{_BAD} "contribution_and_proof" (EthLib.Serialization.Ssz.Err.scope 16 1)'
    ),
}
MAINNET_ONLY = {
    f"AGGREGATE_AND_PROOF_V2 ({version})": f'{_BAD} "data" (EthLib.Serialization.Ssz.Err.scope 1 8)'
    for version in ("ELECTRA", "FULU", "GLOAS")
}

# The sign endpoint of the Remote-signing API, pinned in tests/sources.toml.
SIGN = (
    Path(__file__).resolve().parents[4]
    / "tests/consensus/remote_signing_api/signing/paths/sign.yaml"
)

# The kinds of request that exist before Gloas.
KINDS = {
    "AGGREGATION_SLOT",
    "AGGREGATE_AND_PROOF",
    "AGGREGATE_AND_PROOF_V2",
    "ATTESTATION",
    "BLOCK",
    "BLOCK_V2",
    "DEPOSIT",
    "RANDAO_REVEAL",
    "VOLUNTARY_EXIT",
    "SYNC_COMMITTEE_MESSAGE",
    "SYNC_COMMITTEE_SELECTION_PROOF",
    "SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF",
    "VALIDATOR_REGISTRATION",
}
# The kinds of request that Gloas adds.
GLOAS_KINDS = {
    "EXECUTION_PAYLOAD_BID",
    "EXECUTION_PAYLOAD_ENVELOPE",
    "PAYLOAD_ATTESTATION_MESSAGE",
    "PROPOSER_PREFERENCES",
    "BUILDER_REQUEST_AUTH",
}
# The two examples whose fields are not spelled as the schemas spell them.
# Their fork info writes `previousVersion` and `currentVersion`, and the block writes camel case.
MISSPELLED = {"AGGREGATION_SLOT", "BLOCK (DEPRECATED)"}
# The envelope example has a logs bloom of 262 bytes, where the bloom has 256.
ENVELOPE = "EXECUTION_PAYLOAD_ENVELOPE (GLOAS)"


def _examples() -> dict[str, Any]:
    """Every example request of the sign endpoint, by its name."""
    document = YAML(typ="safe").load(SIGN.read_text())
    examples = document["post"]["requestBody"]["content"]["application/json"]["examples"]
    return {name: example["value"] for name, example in examples.items()}


EXAMPLES = _examples()
WELL_SPELLED = sorted(
    name
    for name, value in EXAMPLES.items()
    if value["type"] in KINDS | GLOAS_KINDS and name not in MISSPELLED | {ENVELOPE}
)


def test_every_kind_has_an_example():
    assert {value["type"] for value in EXAMPLES.values()} == KINDS | GLOAS_KINDS
    assert len(EXAMPLES) == 32
    assert len(WELL_SPELLED) == 29


def _presets(name: str) -> set[str]:
    """The presets whose sizes an example has."""
    if name in MINIMAL_ONLY:
        return {"minimal"}
    if name in MAINNET_ONLY:
        return {"mainnet"}
    return {"minimal", "mainnet"}


@pytest.mark.parametrize("name", WELL_SPELLED)
@pytest.mark.parametrize("preset", ["minimal", "mainnet"])
def test_example_reads_back(name: str, preset: str):
    example = EXAMPLES[name]
    if preset in _presets(name):
        assert consensus.read_signing_request(preset, example) == example
    else:
        with raises(ERROR, {**MINIMAL_ONLY, **MAINNET_ONLY}[name]) as info:
            consensus.read_signing_request(preset, example)
        assert info.value.code == 3


def test_versions_of_the_examples():
    versions = {
        value["type"]: set()
        for value in EXAMPLES.values()
        if value["type"] in {"AGGREGATE_AND_PROOF_V2", "BLOCK_V2"}
    }
    for value in EXAMPLES.values():
        body = value.get("aggregate_and_proof") or value.get("beacon_block")
        if value["type"] in versions:
            versions[value["type"]].add(body["version"])
    every = {"PHASE0", "ALTAIR", "BELLATRIX", "CAPELLA", "DENEB", "ELECTRA", "FULU", "GLOAS"}
    assert versions == {"AGGREGATE_AND_PROOF_V2": every, "BLOCK_V2": every}


def test_misspelled_fork_info_is_refused():
    example = EXAMPLES["AGGREGATION_SLOT"]
    message = (
        "request rejected: EthLib.Consensus.RemoteSigningApi.RequestError.badField"
        ' "fork_info" (EthLib.Serialization.Ssz.Err.undeclaredField "currentVersion")'
    )
    with raises(ERROR, message) as info:
        consensus.read_signing_request(PRESET, example)
    assert info.value.code == 3
    # With the spelling of the `Fork` schema, the example reads back.
    fixed = copy.deepcopy(example)
    fork = fixed["fork_info"]["fork"]
    fork["previous_version"] = fork.pop("previousVersion")
    fork["current_version"] = fork.pop("currentVersion")
    assert consensus.read_signing_request(PRESET, fixed) == fixed


def test_misspelled_block_is_refused():
    message = (
        "request rejected: EthLib.Consensus.RemoteSigningApi.RequestError.badField"
        ' "fork_info" (EthLib.Serialization.Ssz.Err.undeclaredField "currentVersion")'
    )
    with raises(ERROR, message):
        consensus.read_signing_request(PRESET, EXAMPLES["BLOCK (DEPRECATED)"])


def test_payload_attestation_example():
    data = EXAMPLES["PAYLOAD_ATTESTATION_MESSAGE (GLOAS)"]["payload_attestation_message"]["data"]
    root = "0xcf8e0d4e9587369b2301d0790347320302cc0943d5a1884560367e8208d920f2"
    assert data == {
        "beacon_block_root": root,
        "slot": "1",
        "payload_present": True,
        "blob_data_available": True,
    }


@pytest.mark.parametrize(
    ("name", "key"),
    [
        ("EXECUTION_PAYLOAD_BID (GLOAS)", "execution_payload_bid"),
        ("EXECUTION_PAYLOAD_ENVELOPE (GLOAS)", "execution_payload_envelope"),
        ("PAYLOAD_ATTESTATION_MESSAGE (GLOAS)", "payload_attestation_message"),
        ("PROPOSER_PREFERENCES (GLOAS)", "proposer_preferences"),
        ("BUILDER_REQUEST_AUTH (GLOAS)", "builder_request_auth"),
    ],
)
def test_gloas_kinds_take_only_gloas(name: str, key: str):
    example = copy.deepcopy(EXAMPLES[name])
    example[key]["version"] = "FULU"
    with raises(ERROR, f'{REJECTED}unknownVersion "{key}" "FULU"') as info:
        consensus.read_signing_request(PRESET, example)
    assert info.value.code == 5


def test_envelope_example_has_a_long_bloom():
    example = copy.deepcopy(EXAMPLES[ENVELOPE])
    message = f'{_BAD} "data" (EthLib.Serialization.Ssz.Err.hexLength 256 262)'
    for preset in ("minimal", "mainnet"):
        with raises(ERROR, message):
            consensus.read_signing_request(preset, example)
    # With a bloom of 256 bytes, the example reads back under either preset.
    example["execution_payload_envelope"]["data"]["payload"]["logs_bloom"] = "0x" + "00" * 256
    for preset in ("minimal", "mainnet"):
        assert consensus.read_signing_request(preset, example) == example


def test_empty_auth_data_is_refused():
    example = copy.deepcopy(EXAMPLES["BUILDER_REQUEST_AUTH (GLOAS)"])
    example["builder_request_auth"]["data"]["data"] = "0x"
    with raises(ERROR, f"{REJECTED}emptyAuthData") as info:
        consensus.read_signing_request(PRESET, example)
    assert info.value.code == 6


@pytest.mark.parametrize(("size", "reads"), [(1, True), (4096, True), (4097, False)])
def test_auth_data_size(size: int, reads: bool):
    example = copy.deepcopy(EXAMPLES["BUILDER_REQUEST_AUTH (GLOAS)"])
    example["builder_request_auth"]["data"]["data"] = "0x" + "ab" * size
    if reads:
        assert consensus.read_signing_request(PRESET, example) == example
    else:
        message = f'{_BAD} "data" (EthLib.Serialization.Ssz.Err.documentOverLimit 4096 4097)'
        with raises(ERROR, message):
            consensus.read_signing_request(PRESET, example)


def test_auth_takes_no_fork_info():
    example = EXAMPLES["BUILDER_REQUEST_AUTH (GLOAS)"]
    assert "fork_info" not in example
    assert consensus.read_signing_request(PRESET, example) == example


def test_unknown_keys_are_ignored():
    example = copy.deepcopy(EXAMPLES["RANDAO_REVEAL"])
    extended = {**example, "comment": "ignored"}
    assert consensus.read_signing_request(PRESET, extended) == example


def test_unknown_keys_of_a_versioned_body_are_ignored():
    example = copy.deepcopy(EXAMPLES["BLOCK_V2 (FULU)"])
    extended = copy.deepcopy(example)
    extended["beacon_block"]["comment"] = "ignored"
    assert consensus.read_signing_request(PRESET, extended) == example


def test_every_field_of_a_body_is_required():
    example = copy.deepcopy(EXAMPLES["DEPOSIT"])
    del example["deposit"]["amount"]
    message = (
        "request rejected: EthLib.Consensus.RemoteSigningApi.RequestError.badField"
        ' "deposit" (EthLib.Serialization.Ssz.Err.missingField "amount")'
    )
    with raises(ERROR, message):
        consensus.read_signing_request(PRESET, example)


def test_signing_root_is_optional():
    example = copy.deepcopy(EXAMPLES["RANDAO_REVEAL"])
    del example["signingRoot"]
    assert consensus.read_signing_request(PRESET, example) == example


@pytest.mark.parametrize(
    ("change", "code", "message"),
    [
        (
            lambda d: d.pop("fork_info"),
            2,
            'EthLib.Consensus.RemoteSigningApi.RequestError.missingField "fork_info"',
        ),
        (
            lambda d: d.pop("randao_reveal"),
            2,
            'EthLib.Consensus.RemoteSigningApi.RequestError.missingField "randao_reveal"',
        ),
        (
            lambda d: d.update(type="randao_reveal"),
            4,
            'EthLib.Consensus.RemoteSigningApi.RequestError.unknownType "randao_reveal"',
        ),
        (
            lambda d: d.update(type=1),
            3,
            'EthLib.Consensus.RemoteSigningApi.RequestError.badField "type"'
            " (EthLib.Serialization.Ssz.Err.typeMismatch)",
        ),
        (
            lambda d: d.update(signingRoot="0x00"),
            3,
            'EthLib.Consensus.RemoteSigningApi.RequestError.badField "signingRoot"'
            " (EthLib.Serialization.Ssz.Err.typeMismatch)",
        ),
        (
            lambda d: d["randao_reveal"].update(slot="3"),
            3,
            'EthLib.Consensus.RemoteSigningApi.RequestError.badField "randao_reveal"'
            ' (EthLib.Serialization.Ssz.Err.undeclaredField "slot")',
        ),
    ],
    ids=["no fork info", "no body", "lowercase type", "numeric type", "short root", "extra field"],
)
def test_malformed_request_is_refused(change: Any, code: int, message: str):
    example = copy.deepcopy(EXAMPLES["RANDAO_REVEAL"])
    change(example)
    with raises(ERROR, f"request rejected: {message}") as info:
        consensus.read_signing_request(PRESET, example)
    assert info.value.code == code


@pytest.mark.parametrize(
    ("version", "message"),
    [
        ("phase0", 'unknownVersion "beacon_block" "phase0"'),
        ("HEZE", 'unknownVersion "beacon_block" "HEZE"'),
    ],
)
def test_unknown_version_is_refused(version: str, message: str):
    example = copy.deepcopy(EXAMPLES["BLOCK_V2 (FULU)"])
    example["beacon_block"]["version"] = version
    with raises(
        ERROR, f"request rejected: EthLib.Consensus.RemoteSigningApi.RequestError.{message}"
    ):
        consensus.read_signing_request(PRESET, example)


def test_header_is_refused_before_bellatrix():
    example = copy.deepcopy(EXAMPLES["BLOCK_V2 (BELLATRIX)"])
    example["beacon_block"]["version"] = "ALTAIR"
    message = (
        'request rejected: EthLib.Consensus.RemoteSigningApi.RequestError.missingField "block"'
    )
    with raises(ERROR, message):
        consensus.read_signing_request(PRESET, example)


def test_aggregate_takes_the_shape_of_its_version():
    example = copy.deepcopy(EXAMPLES["AGGREGATE_AND_PROOF_V2 (ELECTRA)"])
    example["aggregate_and_proof"]["version"] = "DENEB"
    message = (
        "request rejected: EthLib.Consensus.RemoteSigningApi.RequestError.badField"
        ' "data" (EthLib.Serialization.Ssz.Err.undeclaredField "committee_bits")'
    )
    with raises(ERROR, message):
        consensus.read_signing_request(PRESET, example)
