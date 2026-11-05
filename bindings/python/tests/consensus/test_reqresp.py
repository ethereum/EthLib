"""The request and response messages of the consensus layer, against their layouts restated here."""

import hashlib

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError, SszError
from raising import raises

PREFIX = "/eth2/beacon_chain/req/"


def _id(name: str, version: int | str) -> str:
    return f"{PREFIX}{name}/{version}/ssz_snappy"


PHASE0 = [
    _id("status", 1),
    _id("goodbye", 1),
    _id("beacon_blocks_by_range", 1),
    _id("beacon_blocks_by_root", 1),
    _id("ping", 1),
    _id("metadata", 1),
]
LIGHT_CLIENT = [
    _id("light_client_bootstrap", 1),
    _id("light_client_updates_by_range", 1),
    _id("light_client_finality_update", 1),
    _id("light_client_optimistic_update", 1),
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
] + LIGHT_CLIENT
DENEB = ALTAIR + [_id("blob_sidecars_by_range", 1), _id("blob_sidecars_by_root", 1)]
FULU = (
    [
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
    + LIGHT_CLIENT
    + [
        _id("blob_sidecars_by_range", 1),
        _id("blob_sidecars_by_root", 1),
        _id("data_column_sidecars_by_range", 1),
        _id("data_column_sidecars_by_root", 1),
        _id("beacon_blocks_by_head", 1),
    ]
)


@pytest.mark.parametrize(
    "fork, expected",
    [
        ("phase0", PHASE0),
        ("altair", ALTAIR),
        ("shapella", ALTAIR),
        ("dencun", DENEB),
        ("pectra", DENEB),
        ("fusaka", FULU),
        ("bpo2", FULU),
    ],
)
def test_protocol_ids(fork: str, expected: list) -> None:
    assert consensus.reqresp_protocol_ids(fork) == expected


def test_protocol_ids_not_yet_specified() -> None:
    with raises(ConsensusError, "fork glamsterdam not yet specified"):
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
    with raises(ConsensusError, f"{text} names no protocol"):
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
    return [
        _chunk(fork_digest),
        finalized,
        _chunk(epoch.to_bytes(8, "little")),
        head,
        _chunk(slot.to_bytes(8, "little")),
    ]


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
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err.scope 92 84"):
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
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err.paddingBits"):
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
    with raises(
        SszError, f"input rejected: EthLib.Serialization.Ssz.Err.overLimit {limit} {limit + 1}"
    ):
        consensus.reqresp_message("mainnet", fork, "BeaconBlocksByRootRequest", data + bytes(32))


def _range(*values: int) -> bytes:
    return b"".join(value.to_bytes(8, "little") for value in values)


@pytest.mark.parametrize(
    "fork, name, data",
    [
        ("altair", "LightClientUpdatesByRangeRequest", _range(400, 8)),
        ("dencun", "BlobSidecarsByRangeRequest", _range(10, 64)),
        ("fusaka", "BeaconBlocksByHeadRequest", bytes(range(32)) + _range(64)),
    ],
)
def test_two_field_requests(fork: str, name: str, data: bytes) -> None:
    # Two fields of fixed size: the root of their two chunks.
    root, again = consensus.reqresp_message("mainnet", fork, name, data)
    assert again == data
    first, second = data[:-8], data[-8:]
    assert root == hashlib.sha256(_chunk(first) + _chunk(second)).digest()


@pytest.mark.parametrize(
    "name, fork",
    [
        ("LightClientUpdatesByRangeRequest", "phase0"),
        ("BlobSidecarsByRangeRequest", "shapella"),
        ("BlobSidecarsByRootRequest", "shapella"),
        ("DataColumnSidecarsByRangeRequest", "pectra"),
        ("DataColumnSidecarsByRootRequest", "pectra"),
        ("BeaconBlocksByHeadRequest", "pectra"),
    ],
)
def test_request_before_its_fork(name: str, fork: str) -> None:
    with raises(SszError, f"no message {name} at {fork}"):
        consensus.reqresp_message("mainnet", fork, name, bytes(16))


# A blob identifier is a root and an index: 40 bytes.
@pytest.mark.parametrize("fork, limit", [("dencun", 128 * 6), ("pectra", 128 * 9)])
def test_blob_root_request_limit(fork: str, limit: int) -> None:
    data = bytes(40 * limit)
    _, again = consensus.reqresp_message("mainnet", fork, "BlobSidecarsByRootRequest", data)
    assert again == data
    with raises(
        SszError, f"input rejected: EthLib.Serialization.Ssz.Err.overLimit {limit} {limit + 1}"
    ):
        consensus.reqresp_message("mainnet", fork, "BlobSidecarsByRootRequest", data + bytes(40))


def test_column_range_request() -> None:
    # Two fixed fields, then the offset of the list of columns.
    columns = _range(0, 5, 127)
    data = _range(10, 4) + (20).to_bytes(4, "little") + columns
    name = "DataColumnSidecarsByRangeRequest"
    _, again = consensus.reqresp_message("mainnet", "fusaka", name, data)
    assert again == data
    # The list holds at most the 128 columns.
    many = _range(10, 4) + (20).to_bytes(4, "little") + bytes(8 * 129)
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err.overLimit 128 129"):
        consensus.reqresp_message("mainnet", "fusaka", name, many)


def test_column_root_request() -> None:
    # One identifier: the offset of the identifier, its root, the offset of its columns.
    identifier = bytes([7]) * 32 + (36).to_bytes(4, "little") + _range(3, 64)
    data = (4).to_bytes(4, "little") + identifier
    name = "DataColumnSidecarsByRootRequest"
    _, again = consensus.reqresp_message("minimal", "fusaka", name, data)
    assert again == data
    # The request names at most 128 blocks.
    assert consensus.reqresp_message(
        "minimal", "fusaka", "DataColumnSidecarsByRootRequest", _identifiers(128)
    )[1] == _identifiers(128)
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err.overLimit 128 129"):
        consensus.reqresp_message(
            "minimal", "fusaka", "DataColumnSidecarsByRootRequest", _identifiers(129)
        )


def _identifiers(count: int) -> bytes:
    # Identifiers with no column: their offsets, then each a root and the offset of its columns.
    offsets = b"".join((4 * count + 36 * i).to_bytes(4, "little") for i in range(count))
    return offsets + (bytes(32) + (36).to_bytes(4, "little")) * count


def test_error_message_limit() -> None:
    consensus.reqresp_message("mainnet", "phase0", "ErrorMessage", bytes(256))
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err.overLimit 256 257"):
        consensus.reqresp_message("mainnet", "phase0", "ErrorMessage", bytes(257))


@pytest.mark.parametrize("name", ["mainnet", "minimal"])
def test_min_epochs_for_block_requests(name: str) -> None:
    config = consensus.config(name)
    expected = config["MIN_VALIDATOR_WITHDRAWABILITY_DELAY"] + config["CHURN_LIMIT_QUOTIENT"] // 2
    assert consensus.compute_min_epochs_for_block_requests(name) == expected
