"""The gossip validation of EthLib against the gossip validation vectors."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "gossip"

# The topics that EthLib validates, with the first fork of their cases.
TOPICS = {
    "attester_slashing": "phase0",
    "proposer_slashing": "phase0",
    "voluntary_exit": "phase0",
    "beacon_block": "phase0",
    "beacon_attestation": "phase0",
    "beacon_aggregate_and_proof": "phase0",
    "sync_committee_message": "altair",
    "sync_committee_contribution_and_proof": "altair",
    "bls_to_execution_change": "capella",
    "blob_sidecar": "deneb",
    "data_column_sidecar": "fulu",
    "partial_data_column_sidecar": "fulu",
    "proposer_preferences": "gloas",
    "execution_payload_envelope": "gloas",
    "payload_attestation_message": "gloas",
    "execution_payload_bid": "gloas",
    "inclusion_list": "heze",
}
SPECIFIED = (
    "phase0",
    "altair",
    "bellatrix",
    "capella",
    "deneb",
    "electra",
    "fulu",
    "gloas",
    "heze",
)
# The topics whose cases stop before Heze, with their last fork.
# Blob sidecars travel only at Deneb and Electra.
LAST = {"blob_sidecar": "electra"}

# The release archives that hold the cases.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}

_YAML = YAML(typ="safe")

# The topics of the messages that a case of another topic sends, by the prefix of their file.
# A bid case sends the preferences and the envelopes.
# From Heze it also sends the inclusion lists that its bids rely on.
_MESSAGE_TOPICS = {
    "proposer_preferences": "proposer_preferences",
    "execution_payload_envelope": "execution_payload",
    "inclusion_list": "inclusion_list",
}

# The statuses of a payload, as the specification numbers them.
_STATUSES = {"VALID": 0, "INVALIDATED": 1, "NOT_VALIDATED": 2}


def runs(fork: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a gossip handler at a fork."""
    topic = handler.removeprefix("gossip_")
    return (
        fork in SPECIFIED
        and topic in TOPICS
        and SPECIFIED.index(TOPICS[topic])
        <= SPECIFIED.index(fork)
        <= SPECIFIED.index(LAST.get(topic, "heze"))
    )


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def _read(case: Path, name: str) -> bytes:
    """The bytes of an SSZ file of a case, without the Snappy framing."""
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def _partial_messages(case: Path, meta: dict) -> list:
    """
    The partial messages of a case, after the headers that the node validated before it.

    Each message starts with its kind, 1 for such a header and 0 for a sidecar.

    The group of the message follows: the root of its block, and from Gloas its slot.

    The column of a sidecar takes the place of the subnet.
    """
    headers = [
        (0, 0, b"\x01" + _hex(entry["block_root"]) + _read(case, entry["header"]))
        for entry in meta.get("seen_partial_data_column_headers", [])
    ]
    sidecars = [
        (
            message.get("current_time_ms", 0),
            message["column_index"],
            b"\x00" + _read(case, message["group_id"]) + _read(case, message["message"]),
        )
        for message in meta["messages"]
    ]
    return headers + sidecars


def run_case(preset: str, fork: str, case: Path) -> None:
    """Validate the messages of a case in turn, and compare each outcome and reason."""
    meta = _YAML.load((case / "meta.yaml").read_text())
    blocks = [
        (
            1 if entry.get("failed") else 2 if entry.get("pending") else 0,
            _STATUSES.get(entry.get("payload_status")),
            _read(case, entry["block"]),
            _read(case, entry["payload"]) if "payload" in entry else b"",
        )
        for entry in meta["blocks"][1:]
    ]
    # Kind 3 gives the anchor again, for the envelope of its payload.
    anchor = meta["blocks"][0]
    if "payload" in anchor:
        blocks.insert(0, (3, None, _read(case, anchor["block"]), _read(case, anchor["payload"])))
    finalized = meta.get("finalized_checkpoint")
    if finalized is not None:
        # A checkpoint names its root, or the signed block whose message has the root.
        # The message of a signed block starts after its 4-byte offset and its signature.
        root = (
            bytes.fromhex(finalized["root"][2:])
            if "root" in finalized
            else consensus.ssz_static(
                preset, FORKS[fork], "BeaconBlock", _read(case, finalized["block"])[100:]
            )[0]
        )
        finalized = (finalized["epoch"], root)
    # Setting 2 marks placeholder signatures, which the case must not check.
    verify = meta.get("bls_setting", 0) != 2
    config_file = case / "config.yaml"
    config = (
        replacements(_YAML.load(config_file.read_text()), preset) if config_file.exists() else None
    )
    if meta["topic"] == "partial_data_column_sidecar":
        messages = _partial_messages(case, meta)
    else:
        messages = [
            (
                message.get("current_time_ms", 0),
                message.get("subnet_id", 0),
                _read(case, message["message"]),
                _MESSAGE_TOPICS.get(message["message"].rsplit("_0x", 1)[0], ""),
            )
            for message in meta["messages"]
        ]
    outcomes = consensus.gossip_validation(
        preset,
        FORKS[fork],
        _read(case, "state"),
        _read(case, meta["blocks"][0]["block"]),
        meta["topic"],
        messages,
        verify,
        config,
        blocks,
        finalized,
    )
    expected = [(message["expected"], message.get("reason")) for message in meta["messages"]]
    assert outcomes == expected


def _cases() -> list:
    """Every vendored case, as its preset, fork and directory."""
    cases = []
    for meta in sorted(FILES.rglob("meta.yaml")):
        case = meta.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


def _archive_cases() -> list:
    """Every case of the archives for a topic that EthLib validates, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        base = (
            archives.unpack(name, *(f"tests/{preset}/{fork}/networking" for fork in SPECIFIED))
            / "tests"
            / preset
        )
        for meta in sorted(base.glob("*/networking/gossip_*/*/*/meta.yaml")):
            case = meta.parent
            fork, _, handler = case.relative_to(base).parts[:3]
            if runs(fork, handler):
                cases.append(
                    pytest.param(
                        preset,
                        fork,
                        case,
                        id=f"{preset}/{case.relative_to(base).as_posix()}",
                        marks=pytest.mark.archive(name),
                    )
                )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no gossip validation case")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if line and not line.startswith("#")]
    assert len(entries) == sum(
        1 for path in FILES.rglob("*") if path.is_file() and path.name != "SHA256SUMS"
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_case(preset, fork, case):
    assert runs(fork, case.parts[-3])
    run_case(preset, fork, case)


@archives.parametrize("preset, fork, case", _archive_cases)
def test_archive_case(preset, fork, case):
    run_case(preset, fork, case)


def _valid_case(handler: str) -> Path:
    """The vendored Capella case of a handler with one valid message."""
    return (
        FILES
        / "minimal"
        / "capella"
        / "networking"
        / handler
        / "pyspec_tests"
        / (f"{handler}__valid")
    )


def test_unknown_topic():
    case = _valid_case("gossip_voluntary_exit")
    with raises(
        consensus.ForkChoiceError,
        "gossip validation of the topic light_client_optimistic_update at shapella is not yet "
        "specified",
    ) as info:
        consensus.gossip_validation(
            "minimal",
            "shapella",
            _read(case, "state"),
            b"",
            "light_client_optimistic_update",
            [],
        )
    assert info.value.code == 0


def test_change_of_credentials_before_capella():
    case = _valid_case("gossip_voluntary_exit")
    with raises(
        consensus.ForkChoiceError,
        "gossip validation of the topic bls_to_execution_change at bellatrix is not yet specified",
    ):
        consensus.gossip_validation(
            "minimal", "bellatrix", _read(case, "state"), b"", "bls_to_execution_change", []
        )


def test_seen_keys_follow_valid_messages():
    # A valid exit records its validator, so the same exit is then ignored.
    case = _valid_case("gossip_voluntary_exit")
    meta = _YAML.load((case / "meta.yaml").read_text())
    message = meta["messages"][0]
    data = _read(case, message["message"])
    outcomes = consensus.gossip_validation(
        "minimal",
        "shapella",
        _read(case, "state"),
        _read(case, meta["blocks"][0]["block"]),
        "voluntary_exit",
        [(message["current_time_ms"], 0, data)] * 2,
    )
    assert outcomes == [
        ("valid", None),
        ("ignore", "already seen voluntary exit for this validator"),
    ]


def test_message_of_another_shape():
    with raises(
        consensus.ForkChoiceError,
        "a message is (time, subnet, bytes) or (time, subnet, bytes, topic)",
    ) as info:
        consensus.gossip_validation("minimal", "shapella", b"", b"", "voluntary_exit", [(1, 0)])  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0


def test_block_of_another_shape():
    with raises(
        consensus.ForkChoiceError,
        "a block is (kind, status, bytes) or (kind, status, bytes, envelope)",
    ) as info:
        consensus.gossip_validation(
            "minimal",
            "shapella",
            b"",
            b"",
            "voluntary_exit",
            [],
            blocks=[(0, None)],  # ty: ignore[invalid-argument-type]
        )
    assert info.value.code == 0


def test_time_out_of_range():
    message = f"expected an int below {2**64}, got {2**64}"
    with raises(consensus.ForkChoiceError, message) as info:
        consensus.gossip_validation(
            "minimal", "shapella", b"", b"", "voluntary_exit", [(2**64, 0, b"")]
        )
    assert info.value.code == 0


def test_finalized_root_length():
    with raises(consensus.ForkChoiceError, "expected 32 bytes, got 31") as info:
        consensus.gossip_validation(
            "minimal", "shapella", b"", b"", "voluntary_exit", [], finalized=(0, bytes(31))
        )
    assert info.value.code == 0


@pytest.mark.parametrize("verify", [1, None])
def test_verify_must_be_a_bool(verify):
    with raises(consensus.ForkChoiceError, "expected a bool") as info:
        consensus.gossip_validation("minimal", "shapella", b"", b"", "voluntary_exit", [], verify)
    assert info.value.code == 0


def _envelope_error(envelope: bytes | None) -> tuple[int, str]:
    # The anchor block is empty, so the run stops at its decoding, after the blocks are read.
    case = _valid_case("gossip_voluntary_exit")
    try:
        consensus.gossip_validation(
            "minimal",
            "shapella",
            _read(case, "state"),
            b"",
            "voluntary_exit",
            [],
            blocks=[(0, None, b"", envelope)],
        )
    except consensus.ForkChoiceError as error:
        return error.code, str(error)
    raise AssertionError("the run did not stop")


def test_none_is_no_envelope():
    # None reads as empty bytes, so both stop at the same point with the same error.
    assert _envelope_error(None) == _envelope_error(b"")
