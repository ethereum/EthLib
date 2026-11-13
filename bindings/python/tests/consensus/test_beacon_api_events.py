"""The events of received objects on the Beacon API event stream, against the source and vectors."""

import json
from pathlib import Path
from typing import Any

import pytest
from ruamel.yaml import YAML

from ethlib import consensus

from .containers import FORKS
from .test_beacon_api_json import BEACON_API
from .test_gossip_validation import FILES, case_store, read

# The event stream of ethereum/beacon-APIs at 7911555e, pinned in tests/sources.toml.
EVENTSTREAM = BEACON_API / "apis" / "eventstream" / "index.yaml"

# Each event whose example carries a whole object: its gossip topic, its type, and a fork.
# The fork is one whose container reads the example.
OBJECT_EVENTS = {
    "voluntary_exit": ("voluntary_exit", "SignedVoluntaryExit", "phase0"),
    "proposer_slashing": ("proposer_slashing", "ProposerSlashing", "phase0"),
    "attester_slashing": ("attester_slashing", "AttesterSlashing", "phase0"),
    "bls_to_execution_change": ("bls_to_execution_change", "SignedBLSToExecutionChange", "capella"),
    "contribution_and_proof": (
        "sync_committee_contribution_and_proof",
        "SignedContributionAndProof",
        "altair",
    ),
    "single_attestation": ("beacon_attestation", "SingleAttestation", "electra"),
    "execution_payload_bid": ("execution_payload_bid", "SignedExecutionPayloadBid", "gloas"),
    "payload_attestation_message": (
        "payload_attestation_message",
        "PayloadAttestationMessage",
        "gloas",
    ),
    "proposer_preferences": ("proposer_preferences", "SignedProposerPreferences", "gloas"),
}

# The events whose example carries the object under its consensus version.
VERSIONED = {"execution_payload_bid", "payload_attestation_message", "proposer_preferences"}

_YAML = YAML(typ="safe")


def _examples() -> dict[str, tuple[str, Any]]:
    """The topic and the JSON data of each example of the event stream, by its name."""
    document = YAML(typ="safe", pure=True).load(EVENTSTREAM.read_text(encoding="utf-8"))
    examples = document["get"]["responses"]["200"]["content"]["text/event-stream"]["examples"]
    out = {}
    for name, example in examples.items():
        event, data = example["value"].strip().split("\n")
        out[name] = (event.removeprefix("event: "), json.loads(data.removeprefix("data: ")))
    return out


EXAMPLES = _examples()


def _lower(value: Any) -> Any:
    """A JSON value with each hex string in lower case, since the source writes either case."""
    if isinstance(value, dict):
        return {key: _lower(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_lower(item) for item in value]
    if isinstance(value, str) and value.startswith("0x"):
        return value.lower()
    return value


def _case(fork: str, handler: str, name: str) -> tuple[Path, dict]:
    """A minimal gossip case of a handler at a fork, and its meta."""
    case = FILES / "minimal" / fork / "networking" / handler / "pyspec_tests" / name
    return case, _YAML.load((case / "meta.yaml").read_text())


def _root(fork: str, type_name: str, value: dict) -> str:
    """The hash tree root of the container that the JSON of the API holds."""
    encoded = consensus.api_ssz("minimal", FORKS[fork], type_name, value)
    return "0x" + consensus.ssz_static("minimal", FORKS[fork], type_name, encoded)[0].hex()


def test_examples_name_their_topic() -> None:
    """Each example of the source names the event of its own key."""
    assert [name for name, (event, _) in EXAMPLES.items() if event != name] == []


@pytest.mark.parametrize("name", sorted(OBJECT_EVENTS))
def test_object_example(name: str) -> None:
    """The object of an example, once gossip accepts it, gives the example as its event."""
    topic, type_name, fork = OBJECT_EVENTS[name]
    event, data = EXAMPLES[name]
    obj = data["data"] if name in VERSIONED else data
    encoded = consensus.api_ssz("mainnet", FORKS[fork], type_name, obj)
    assert consensus.api_gossip_event("mainnet", FORKS[fork], topic, encoded) == (
        event,
        _lower(data),
    )


def test_attestation_example() -> None:
    """Before Electra, the example of an attestation without its committee bits is its event."""
    # The example has the committee bits of Electra.
    # From Electra the subnets carry single attestations, so this event exists only before.
    event, data = EXAMPLES["attestation"]
    early = {key: value for key, value in data.items() if key != "committee_bits"}
    encoded = consensus.api_ssz("mainnet", "phase0", "Attestation", early)
    assert consensus.api_gossip_event("mainnet", "phase0", "beacon_attestation", encoded) == (
        event,
        early,
    )


@pytest.mark.parametrize(
    "fork, handler, name",
    [
        ("phase0", "gossip_beacon_aggregate_and_proof", "gossip_beacon_aggregate_and_proof__valid"),
        ("altair", "gossip_sync_committee_message", "gossip_sync_committee_message__valid"),
    ],
)
def test_topic_without_event(fork: str, handler: str, name: str) -> None:
    """A topic that the event stream does not list gives no event."""
    case, meta = _case(fork, handler, name)
    data = read(case, meta["messages"][0]["message"])
    assert consensus.api_gossip_event("minimal", FORKS[fork], meta["topic"], data) is None


@pytest.mark.parametrize("fork", ["fulu", "gloas"])
def test_column_sidecar(fork: str) -> None:
    """A column sidecar that gossip accepts gives the root and slot of its block, and its index."""
    case, meta = _case(fork, "gossip_data_column_sidecar", "gossip_data_column_sidecar__valid")
    data = read(case, meta["messages"][0]["message"])
    sidecar = consensus.api_json("minimal", FORKS[fork], "DataColumnSidecar", data)
    if fork == "fulu":
        header = sidecar["signed_block_header"]["message"]
        root, slot = _root(fork, "BeaconBlockHeader", header), header["slot"]
    else:
        root, slot = sidecar["beacon_block_root"], sidecar["slot"]
    expected = {"block_root": root, "index": sidecar["index"], "slot": slot}
    assert set(expected) == set(EXAMPLES["data_column_sidecar"][1])
    assert consensus.api_gossip_event("minimal", FORKS[fork], "data_column_sidecar", data) == (
        "data_column_sidecar",
        expected,
    )


def block_events(fork: str, signed: bytes, imported: bool) -> list:
    """The events of a published block that passes gossip, and that the node may import."""
    block = consensus.api_json("minimal", FORKS[fork], "SignedBeaconBlock", signed)["message"]
    root = _root(fork, "BeaconBlock", block)
    gossip = ("block_gossip", {"slot": block["slot"], "block": root})
    if not imported:
        return [gossip]
    data = {"slot": block["slot"], "block": root, "execution_optimistic": False}
    if fork in {"gloas", "heze"}:
        bid = block["body"]["signed_execution_payload_bid"]["message"]
        data |= {"builder_index": bid["builder_index"], "block_hash": bid["block_hash"]}
    return [gossip, ("block", data)]


@pytest.mark.parametrize("fork", ["capella", "gloas"])
def test_published_block(fork: str) -> None:
    """A valid block gives its gossip event and its block event, and a second copy none."""
    case, meta = _case(fork, "gossip_beacon_block", "gossip_beacon_block__valid_block")
    message = meta["messages"][0]
    signed = read(case, message["message"])
    time = message.get("current_time_ms", 0)
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS[fork],
        requests=[(time, "blocks", [signed]), (time, "blocks", [signed])],
        **case_store("minimal", fork, case, meta),
    )
    events = block_events(fork, signed, imported=True)
    assert set(events[0][1]) == set(EXAMPLES["block_gossip"][1])
    if fork == "gloas":
        assert set(events[1][1]) == set(EXAMPLES["block"][1])
    assert [event for _, _, event in answers] == [events, []]


def envelope_events(envelope: bytes) -> list:
    """The gossip event and the payload event of a valid Gloas envelope."""
    message = consensus.api_json(
        "minimal", FORKS["gloas"], "SignedExecutionPayloadEnvelope", envelope
    )["message"]
    gossip = {
        "slot": message["payload"]["slot_number"],
        "builder_index": message["builder_index"],
        "block_hash": message["payload"]["block_hash"],
        "block_root": message["beacon_block_root"],
    }
    imported = gossip | {"execution_optimistic": False}
    return [("execution_payload_gossip", gossip), ("execution_payload", imported)]


def test_published_envelope() -> None:
    """A valid envelope gives its gossip event and its payload event, and a second copy none."""
    case, meta = _case(
        "gloas", "gossip_execution_payload_envelope", "gossip_execution_payload_envelope__valid"
    )
    envelope = read(case, meta["messages"][0]["message"])
    request = (0, "execution_payload_envelopes", [envelope])
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS["gloas"],
        requests=[request, request],
        **case_store("minimal", "gloas", case, meta),
    )
    events = envelope_events(envelope)
    assert set(events[0][1]) == set(EXAMPLES["execution_payload_gossip"][1])
    assert set(events[1][1]) == set(EXAMPLES["execution_payload"][1])
    assert [event for _, _, event in answers] == [events, []]


def test_published_block_already_held() -> None:
    """A block that the store already holds gives its gossip event, but no block event."""
    case, meta = _case("capella", "gossip_beacon_block", "gossip_beacon_block__valid_block")
    message = meta["messages"][0]
    signed = read(case, message["message"])
    store = case_store("minimal", "capella", case, meta)
    store["blocks"] = [*store["blocks"], (0, None, signed, b"")]
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS["capella"],
        requests=[(message.get("current_time_ms", 0), "blocks", [signed])],
        **store,
    )
    assert answers == [(200, [], block_events("capella", signed, imported=False))]


def test_every_example_is_covered() -> None:
    """Each event of a received object in the source has a test here."""
    # The events of the fork choice and of a proposal have their tests in other files.
    chain = {"head", "head_v2", "finalized_checkpoint", "chain_reorg", "fast_confirmation"}
    chain |= {"payload_attributes"}
    later = {
        "light_client_finality_update",
        "light_client_optimistic_update",
        "execution_payload_available",
    }
    tested = set(OBJECT_EVENTS) | {
        "attestation",
        "data_column_sidecar",
        "block",
        "block_gossip",
        "execution_payload",
        "execution_payload_gossip",
    }
    assert set(EXAMPLES) - chain - later == tested
