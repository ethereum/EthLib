"""The request and response messages of the consensus layer, against their layouts restated here."""

import hashlib

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError, SszError

PREFIX = "/eth2/beacon_chain/req/"


def _id(name: str, version: int) -> str:
    return f"{PREFIX}{name}/{version}/ssz_snappy"


PHASE0 = [
    _id("status", 1),
    _id("goodbye", 1),
    _id("beacon_blocks_by_range", 1),
    _id("beacon_blocks_by_root", 1),
    _id("ping", 1),
    _id("metadata", 1),
]
ALTAIR = [
    _id("status", 1),
    _id("goodbye", 1),
    _id("beacon_blocks_by_range", 1),
    _id("beacon_blocks_by_range", 2),
    _id("beacon_blocks_by_root", 1),
    _id("beacon_blocks_by_root", 2),
    _id("ping", 1),
    _id("metadata", 1),
    _id("metadata", 2),
]
FULU = [
    _id("status", 1),
    _id("status", 2),
    _id("goodbye", 1),
    _id("beacon_blocks_by_range", 1),
    _id("beacon_blocks_by_range", 2),
    _id("beacon_blocks_by_root", 1),
    _id("beacon_blocks_by_root", 2),
    _id("ping", 1),
    _id("metadata", 1),
    _id("metadata", 2),
    _id("metadata", 3),
]


@pytest.mark.parametrize(
    "fork, expected",
    [("phase0", PHASE0), ("altair", ALTAIR), ("pectra", ALTAIR), ("fusaka", FULU), ("bpo2", FULU)],
)
def test_protocol_ids(fork: str, expected: list) -> None:
    assert consensus.reqresp_protocol_ids(fork) == expected


def test_protocol_ids_not_yet_specified() -> None:
    with pytest.raises(ConsensusError):
        consensus.reqresp_protocol_ids("glamsterdam")


def test_parse_protocol_ids() -> None:
    for text in FULU:
        name, version = consensus.reqresp_parse_protocol_id(text)
        assert _id(name, version) == text


@pytest.mark.parametrize(
    "text",
    [
        _id("status", 0),
        _id("status", "01"),
        _id("statu", 1),
        f"{PREFIX}status/1/ssz",
        "/eth2/beacon_chain/req/status/1/",
        _id("status", "1a"),
    ],
)
def test_parse_rejects(text: str) -> None:
    with pytest.raises(ConsensusError):
        consensus.reqresp_parse_protocol_id(text)


def _chunk(data: bytes) -> bytes:
    return data + bytes(32 - len(data))


def _merkleize(chunks: list) -> bytes:
    count = 1
    while count < len(chunks):
        count *= 2
    nodes = chunks + [bytes(32)] * (count - len(chunks))
    while len(nodes) > 1:
        nodes = [hashlib.sha256(nodes[i] + nodes[i + 1]).digest() for i in range(0, len(nodes), 2)]
    return nodes[0]


def _status(fork_digest: bytes, finalized: bytes, epoch: int, head: bytes, slot: int) -> list:
    return [_chunk(fork_digest), finalized, _chunk(epoch.to_bytes(8, "little")), head,
            _chunk(slot.to_bytes(8, "little"))]


def test_status_v1() -> None:
    digest, finalized, head = bytes.fromhex("6a95a1a9"), bytes(range(32)), bytes(range(32, 64))
    data = digest + finalized + (7).to_bytes(8, "little") + head + (300).to_bytes(8, "little")
    root, again = consensus.reqresp_message("mainnet", "pectra", "Status", data)
    assert again == data
    assert root == _merkleize(_status(digest, finalized, 7, head, 300))


def test_status_v2() -> None:
    digest, finalized, head = bytes(4), bytes(32), bytes([1]) * 32
    fields = digest + finalized + (1).to_bytes(8, "little") + head + (64).to_bytes(8, "little")
    data = fields + (32).to_bytes(8, "little")
    root, again = consensus.reqresp_message("mainnet", "fusaka", "Status", data)
    assert again == data
    chunks = _status(digest, finalized, 1, head, 64) + [_chunk((32).to_bytes(8, "little"))]
    assert root == _merkleize(chunks)
    with pytest.raises(SszError):
        consensus.reqresp_message("mainnet", "fusaka", "Status", fields)


SEQ_AND_ATTNETS = bytes(range(16))


@pytest.mark.parametrize(
    "fork, data",
    [
        ("phase0", SEQ_AND_ATTNETS),
        ("altair", SEQ_AND_ATTNETS + bytes([0x0F])),
        ("fusaka", SEQ_AND_ATTNETS + bytes([0x05]) + (4).to_bytes(8, "little")),
    ],
)
def test_metadata(fork: str, data: bytes) -> None:
    _, again = consensus.reqresp_message("mainnet", fork, "MetaData", data)
    assert again == data


def test_metadata_syncnets_padding() -> None:
    # Four sync committee subnets leave the top four bits of their byte at zero.
    with pytest.raises(SszError):
        consensus.reqresp_message("mainnet", "altair", "MetaData", SEQ_AND_ATTNETS + bytes([0x10]))


def test_ping_and_goodbye() -> None:
    for name in ("Ping", "Goodbye"):
        data = (3).to_bytes(8, "little")
        root, again = consensus.reqresp_message("mainnet", "phase0", name, data)
        assert again == data
        assert root == _chunk(data)


def test_range_request() -> None:
    data = (10).to_bytes(8, "little") + (64).to_bytes(8, "little") + (1).to_bytes(8, "little")
    _, again = consensus.reqresp_message("mainnet", "phase0", "BeaconBlocksByRangeRequest", data)
    assert again == data


@pytest.mark.parametrize("fork, limit", [("pectra", 128), ("shapella", 1024)])
def test_root_request_limit(fork: str, limit: int) -> None:
    data = bytes(32 * limit)
    _, again = consensus.reqresp_message("mainnet", fork, "BeaconBlocksByRootRequest", data)
    assert again == data
    with pytest.raises(SszError):
        consensus.reqresp_message("mainnet", fork, "BeaconBlocksByRootRequest", data + bytes(32))


def test_error_message_limit() -> None:
    consensus.reqresp_message("mainnet", "phase0", "ErrorMessage", bytes(256))
    with pytest.raises(SszError):
        consensus.reqresp_message("mainnet", "phase0", "ErrorMessage", bytes(257))


@pytest.mark.parametrize("name", ["mainnet", "minimal"])
def test_min_epochs_for_block_requests(name: str) -> None:
    config = consensus.config(name)
    expected = config["MIN_VALIDATOR_WITHDRAWABILITY_DELAY"] + config["CHURN_LIMIT_QUOTIENT"] // 2
    assert consensus.compute_min_epochs_for_block_requests(name) == expected
