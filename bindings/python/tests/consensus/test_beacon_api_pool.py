"""The Beacon API pool endpoints of EthLib against the gossip validation vectors."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from raising import raises

from .containers import FORKS
from .test_gossip_validation import FILES, MESSAGE_TOPICS, case_store, read, valid_case

# The pool endpoint of each gossip handler whose objects a client may submit.
ENDPOINTS = {
    "gossip_attester_slashing": "attester_slashings",
    "gossip_proposer_slashing": "proposer_slashings",
    "gossip_voluntary_exit": "voluntary_exits",
    "gossip_bls_to_execution_change": "bls_to_execution_changes",
    "gossip_beacon_attestation": "attestations",
    "gossip_beacon_aggregate_and_proof": "aggregate_and_proofs",
    "gossip_sync_committee_message": "sync_committees",
    "gossip_sync_committee_contribution_and_proof": "contribution_and_proofs",
    "gossip_payload_attestation_message": "payload_attestations",
    "gossip_proposer_preferences": "proposer_preferences",
    "gossip_execution_payload_bid": "execution_payload_bids",
}

# The event and the type of the object of each handler whose objects give an event.
EVENTS = {
    "gossip_attester_slashing": ("attester_slashing", "AttesterSlashing"),
    "gossip_proposer_slashing": ("proposer_slashing", "ProposerSlashing"),
    "gossip_voluntary_exit": ("voluntary_exit", "SignedVoluntaryExit"),
    "gossip_bls_to_execution_change": ("bls_to_execution_change", "SignedBLSToExecutionChange"),
    "gossip_sync_committee_contribution_and_proof": (
        "contribution_and_proof",
        "SignedContributionAndProof",
    ),
    "gossip_payload_attestation_message": (
        "payload_attestation_message",
        "PayloadAttestationMessage",
    ),
    "gossip_proposer_preferences": ("proposer_preferences", "SignedProposerPreferences"),
    "gossip_execution_payload_bid": ("execution_payload_bid", "SignedExecutionPayloadBid"),
}

# The events whose data holds the object under the consensus version of its fork.
VERSIONED = {"payload_attestation_message", "proposer_preferences", "execution_payload_bid"}

# The forks before Electra, whose attestation subnets carry attestations.
EARLY = {"phase0", "altair", "bellatrix", "capella", "deneb"}

# The reasons of gossip for a message on a subnet other than its own.
# The node picks the subnet of a submitted object itself, so these cases do not apply.
WRONG_SUBNET = {"attestation is for wrong subnet", "subnet_id is not valid for the validator"}

_YAML = YAML(typ="safe")


def _submits(meta: dict) -> bool:
    """Whether a case sends only objects of its own topic, and expects no wrong subnet."""
    # A message of another topic has no pool endpoint here.
    return all(
        message.get("reason") not in WRONG_SUBNET
        and MESSAGE_TOPICS.get(message["message"].rsplit("_0x", 1)[0], meta["topic"])
        == meta["topic"]
        for message in meta["messages"]
    )


def _cases() -> list:
    """Every vendored case of a handler with a pool endpoint, as its preset, fork and directory."""
    cases = []
    for meta_file in sorted(FILES.rglob("meta.yaml")):
        case = meta_file.parent
        preset, fork, _, handler = case.relative_to(FILES).parts[:4]
        if handler in ENDPOINTS and _submits(_YAML.load(meta_file.read_text())):
            cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


def event(preset: str, fork: str, handler: str, data: bytes) -> list:
    """The events of an object that passes gossip, or none for a topic without an event."""
    if handler == "gossip_beacon_attestation":
        name, type_name = (
            ("attestation", "Attestation")
            if fork in EARLY
            else ("single_attestation", "SingleAttestation")
        )
    elif handler in EVENTS:
        name, type_name = EVENTS[handler]
    else:
        return []
    obj = consensus.api_json(preset, FORKS[fork], type_name, data)
    if name in VERSIONED:
        # The source names no consensus version from Heze.
        obj = {"version": fork, "data": obj} if fork == "gloas" else {"data": obj}
    return [(name, obj)]


def test_every_endpoint_has_cases() -> None:
    """Each pool endpoint but the bid endpoint is exercised by a vendored gossip case."""
    # Every bid case also sends the envelopes of payloads, which no pool endpoint takes.
    handlers = {param.values[2].parts[-3] for param in _cases()}
    assert handlers == set(ENDPOINTS) - {"gossip_execution_payload_bid"}


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_case(preset: str, fork: str, case: Path) -> None:
    """Each object of a case, in its own request in turn, fails exactly when gossip refuses it."""
    meta = _YAML.load((case / "meta.yaml").read_text())
    endpoint = ENDPOINTS[case.parts[-3]]
    requests = [
        (message.get("current_time_ms", 0), endpoint, [read(case, message["message"])])
        for message in meta["messages"]
    ]
    answers = consensus.api_post(
        name=preset, fork=FORKS[fork], requests=requests, **case_store(preset, fork, case, meta)
    )
    handler = case.parts[-3]
    expected = [
        (200, [], event(preset, fork, handler, item[0]))
        if message["expected"] == "valid"
        else (400, [(0, message["reason"])], [])
        for message, (_, _, item) in zip(meta["messages"], requests, strict=True)
    ]
    assert answers == expected


def test_list_reports_each_failure() -> None:
    """A list of three copies of one change fails at positions 1 and 2, and the first passes."""
    case = valid_case("gossip_bls_to_execution_change")
    meta = _YAML.load((case / "meta.yaml").read_text())
    message = meta["messages"][0]
    change = read(case, message["message"])
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS["capella"],
        requests=[(message.get("current_time_ms", 0), "bls_to_execution_changes", [change] * 3)],
        **case_store("minimal", "capella", case, meta),
    )
    reason = "already seen BLS to execution change for this validator"
    events = event("minimal", "capella", "gossip_bls_to_execution_change", change)
    assert answers == [(400, [(1, reason), (2, reason)], events)]


def test_list_events_follow_positions() -> None:
    """In a list whose first item fails and second passes, only the second gives its event."""
    case = valid_case("gossip_bls_to_execution_change")
    meta = _YAML.load((case / "meta.yaml").read_text())
    message = meta["messages"][0]
    change = read(case, message["message"])
    # The message starts with the validator index, which no validator of the state holds here.
    unknown = (2**40).to_bytes(8, "little") + change[8:]
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS["capella"],
        requests=[
            (message.get("current_time_ms", 0), "bls_to_execution_changes", [unknown, change])
        ],
        **case_store("minimal", "capella", case, meta),
    )
    [(status, failures, events)] = answers
    assert (status, [position for position, _ in failures]) == (400, [0])
    assert events == event("minimal", "capella", "gossip_bls_to_execution_change", change)


@pytest.mark.parametrize("count", [0, 2])
@pytest.mark.parametrize(
    "endpoint, message",
    [
        ("attester_slashings", "the attester slashing endpoint takes one slashing"),
        ("proposer_slashings", "the proposer slashing endpoint takes one slashing"),
        ("voluntary_exits", "the voluntary exit endpoint takes one exit"),
    ],
)
def test_one_object_per_request(endpoint: str, message: str, count: int) -> None:
    """The endpoints of slashings and of exits take exactly one object."""
    case = valid_case("gossip_voluntary_exit")
    meta = _YAML.load((case / "meta.yaml").read_text())
    with raises(consensus.ForkChoiceError, message) as info:
        consensus.api_post(
            name="minimal",
            fork=FORKS["capella"],
            requests=[(0, endpoint, [b""] * count)],
            **case_store("minimal", "capella", case, meta),
        )
    assert info.value.code == 0


@pytest.mark.parametrize(
    "endpoint, items, message",
    [
        ("deposits", [], "the pool endpoint deposits is not specified"),
        ("sync_committees", [], "the sync committee endpoints serve only from Altair"),
        ("contribution_and_proofs", [], "the sync committee endpoints serve only from Altair"),
        (
            "bls_to_execution_changes",
            [],
            "the endpoint of changes of BLS credentials serves only from Capella",
        ),
        ("payload_attestations", [], "the payload attestation endpoint serves only from Gloas"),
        ("proposer_preferences", [], "the proposer preferences endpoint serves only from Gloas"),
        ("execution_payload_bids", [], "the bid endpoint serves only from Gloas"),
    ],
)
def test_endpoint_refused(endpoint: str, items: list[bytes], message: str) -> None:
    """An endpoint that the fork does not serve fails with code 0, after the store is built."""
    case = FILES / "minimal" / "phase0" / "networking" / "gossip_voluntary_exit" / "pyspec_tests"
    case /= "gossip_voluntary_exit__valid"
    meta = _YAML.load((case / "meta.yaml").read_text())
    with raises(consensus.ForkChoiceError, message) as info:
        consensus.api_post(
            name="minimal",
            fork=FORKS["phase0"],
            requests=[(0, endpoint, items)],
            **case_store("minimal", "phase0", case, meta),
        )
    assert info.value.code == 0


def test_one_bid_per_request() -> None:
    """The bid endpoint takes exactly one bid."""
    case = FILES / "minimal" / "gloas" / "networking" / "gossip_execution_payload_bid"
    case = next(path.parent for path in sorted(case.rglob("meta.yaml")))
    meta = _YAML.load((case / "meta.yaml").read_text())
    with raises(consensus.ForkChoiceError, "the bid endpoint takes one bid") as info:
        consensus.api_post(
            name="minimal",
            fork=FORKS["gloas"],
            requests=[(0, "execution_payload_bids", [])],
            **case_store("minimal", "gloas", case, meta),
        )
    assert info.value.code == 0
