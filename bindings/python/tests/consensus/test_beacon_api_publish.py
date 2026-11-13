"""The Beacon API publish endpoints of EthLib against the gossip validation vectors."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from raising import raises

from .containers import FORKS
from .test_beacon_api_pool import ENDPOINTS
from .test_gossip_validation import FILES, MESSAGE_TOPICS, case_store, read, runs

# The publish endpoint of each gossip topic whose objects a client may publish.
PUBLISH = {
    "beacon_block": "blocks",
    "execution_payload": "execution_payload_envelopes",
}

# The endpoint of each topic that a case of a publish or bid handler sends.
TOPIC_ENDPOINTS = {
    **PUBLISH,
    "proposer_preferences": "proposer_preferences",
    "execution_payload_bid": ENDPOINTS["gossip_execution_payload_bid"],
}

# The handlers whose cases go through the endpoints: the two publish topics and the bid topic.
# Every bid case also sends envelopes, which only the publish endpoint takes.
HANDLERS = (
    "gossip_beacon_block",
    "gossip_execution_payload_envelope",
    "gossip_execution_payload_bid",
)

_YAML = YAML(typ="safe")


def _topic(meta: dict, message: dict) -> str:
    """The topic of a message of a case, by the prefix of its file."""
    return MESSAGE_TOPICS.get(message["message"].rsplit("_0x", 1)[0], meta["topic"])


def _cases() -> list:
    """Every vendored case of a handler above whose messages all have an endpoint."""
    cases = []
    for meta_file in sorted(FILES.rglob("meta.yaml")):
        case = meta_file.parent
        preset, fork, _, handler = case.relative_to(FILES).parts[:4]
        if handler not in HANDLERS or not runs(fork, handler):
            continue
        meta = _YAML.load(meta_file.read_text())
        if all(_topic(meta, message) in TOPIC_ENDPOINTS for message in meta["messages"]):
            cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


def test_every_handler_has_cases() -> None:
    """Each handler above, so each publish endpoint and the bid endpoint, has a vendored case."""
    assert {param.values[2].parts[-3] for param in _cases()} == set(HANDLERS)


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_case(preset: str, fork: str, case: Path) -> None:
    """Each object of a case, sent in turn to its endpoint, is refused exactly when gossip is."""
    meta = _YAML.load((case / "meta.yaml").read_text())
    requests = []
    for message in meta["messages"]:
        endpoint = TOPIC_ENDPOINTS[_topic(meta, message)]
        item = [read(case, message["message"])]
        time = message.get("current_time_ms", 0)
        # The publish endpoints take the gossip level; the pool endpoints take no level.
        level = "gossip" if endpoint in PUBLISH.values() else None
        requests.append((time, endpoint, item, level))
    answers = consensus.api_post(
        name=preset, fork=FORKS[fork], requests=requests, **case_store(preset, fork, case, meta)
    )
    for message, (status, failures) in zip(meta["messages"], answers, strict=True):
        if message["expected"] != "valid":
            assert (status, failures) == (400, [(0, message["reason"])])
        elif TOPIC_ENDPOINTS[_topic(meta, message)] not in PUBLISH.values():
            assert (status, failures) == (200, [])
        else:
            # A valid object passes; whether the node then integrates it is not in the case.
            # It is broadcast but not integrated within the clock disparity, for example.
            assert failures == []
            assert status in {200, 202}


def _valid_block() -> tuple[Path, dict, bytes]:
    """A valid Capella block case, its meta and the bytes of its block."""
    case = FILES / "minimal" / "capella" / "networking" / "gossip_beacon_block" / "pyspec_tests"
    case /= "gossip_beacon_block__valid_block"
    meta = _YAML.load((case / "meta.yaml").read_text())
    return case, meta, read(case, meta["messages"][0]["message"])


@pytest.mark.parametrize("level", ["gossip", "consensus", "consensus_and_equivocation", None])
def test_valid_block_is_integrated(level: str | None) -> None:
    """A valid block passes every level, joins the store, and a second copy is refused."""
    case, meta, block = _valid_block()
    time = meta["messages"][0].get("current_time_ms", 0)
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS["capella"],
        requests=[(time, "blocks", [block], level), (time, "blocks", [block], level)],
        **case_store("minimal", "capella", case, meta),
    )
    reason = "block is not the first valid block for this slot and proposer"
    assert answers == [(200, []), (400, [(0, reason)])]


def test_consensus_level_refuses_a_bad_state_root() -> None:
    """A block with a wrong state root passes gossip, but not the consensus level."""
    case, meta, block = _valid_block()
    time = meta["messages"][0].get("current_time_ms", 0)
    # The signed block is an offset and a signature, then the message.
    # The message starts with the slot, the proposer, the parent root and the state root.
    # The signatures are not checked here, so a changed state root passes gossip.
    offset = 4 + 96 + 8 + 8 + 32
    tampered = block[:offset] + bytes(32) + block[offset + 32 :]
    store = case_store("minimal", "capella", case, meta) | {"verify": False}
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS["capella"],
        requests=[
            (time, "blocks", [tampered], "consensus"),
            (time, "blocks", [tampered], "consensus_and_equivocation"),
            (time, "blocks", [tampered], None),
            (time, "blocks", [tampered], "gossip"),
        ],
        **store,
    )
    reason = (
        "consensus: EthLib.Consensus.ForkChoiceError.transition "
        "(EthLib.Consensus.TransitionError.wrongStateRoot)"
    )
    # A refused block is not seen, so the default level broadcasts it.
    # The gossip level then finds it already seen.
    seen = "block is not the first valid block for this slot and proposer"
    assert answers == [
        (400, [(0, reason)]),
        (400, [(0, reason)]),
        (202, []),
        (400, [(0, seen)]),
    ]


@pytest.mark.parametrize(
    "level, answer",
    [
        ("consensus", (200, [])),
        ("consensus_and_equivocation", (400, [(0, "equivocation: the block has a rival")])),
    ],
)
def test_equivocation_level_refuses_a_rival(level: str, answer: tuple) -> None:
    """A valid block with a rival in the store passes the consensus level, but not the highest."""
    case, meta, block = _valid_block()
    time = meta["messages"][0].get("current_time_ms", 0)
    # The rival has the slot and the proposer of the block, but a parent that the store lacks.
    # The store holds it as a block that failed validation, so gossip never saw it.
    # With no known parent it stays out of the tree of the fork choice.
    offset = 4 + 96 + 8 + 8
    rival = block[:offset] + b"\xff" * 32 + block[offset + 32 :]
    store = case_store("minimal", "capella", case, meta) | {"verify": False}
    store["blocks"] = [*store["blocks"], (1, None, rival, b"")]
    answers = consensus.api_post(
        name="minimal", fork=FORKS["capella"], requests=[(time, "blocks", [block], level)], **store
    )
    assert answers == [answer]


@pytest.mark.parametrize("level", ["gossip", "consensus", "consensus_and_equivocation"])
def test_valid_envelope_is_integrated(level: str) -> None:
    """A valid Gloas envelope passes every level and is integrated, and a second copy is refused."""
    case = FILES / "minimal" / "gloas" / "networking" / "gossip_execution_payload_envelope"
    case /= "pyspec_tests/gossip_execution_payload_envelope__valid"
    meta = _YAML.load((case / "meta.yaml").read_text())
    envelope = read(case, meta["messages"][0]["message"])
    request = (0, "execution_payload_envelopes", [envelope], level)
    answers = consensus.api_post(
        name="minimal",
        fork=FORKS["gloas"],
        requests=[request, request],
        **case_store("minimal", "gloas", case, meta),
    )
    reason = "already seen envelope for this block root from this builder"
    assert answers == [(200, []), (400, [(0, reason)])]


@pytest.mark.parametrize(
    "request_, message",
    [
        ((0, "blocks", [], None), "the block endpoint takes one block"),
        ((0, "blocks", [b"", b""], None), "the block endpoint takes one block"),
        (
            (0, "execution_payload_envelopes", [], None),
            "the envelope endpoint serves only from Gloas",
        ),
        ((0, "blocks", [b""], "full"), "the broadcast validation full is not specified"),
        ((0, "voluntary_exits", [b""], "gossip"), "a pool endpoint takes no broadcast validation"),
    ],
)
def test_request_refused(request_: consensus.PostRequest, message: str) -> None:
    """A request that the export cannot read fails with code 0."""
    case, meta, _ = _valid_block()
    with raises(consensus.ForkChoiceError, message) as info:
        consensus.api_post(
            name="minimal",
            fork=FORKS["capella"],
            requests=[request_],
            **case_store("minimal", "capella", case, meta),
        )
    assert info.value.code == 0
