"""A response chunk decodes at the bounds of its fork: the fork of its digest or of the exchange."""

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError
from ethlib.networking import enr, reqresp, uvarint
from ethlib.networking.reqresp import ResponseChunk
from raising import raises

from .test_fork_digest import SEPOLIA, SEPOLIA_RECORD, SEPOLIA_ROOT

PREFIX = "/eth2/beacon_chain/req/"

# A root for the chains whose digests the tests compute rather than read from a source.
ROOT = bytes(range(32))

FAR_FUTURE_EPOCH = 2**64 - 1


def _id(name: str, version: int) -> str:
    return f"{PREFIX}{name}/{version}/ssz_snappy"


def _success(context: bytes, payload: bytes) -> bytes:
    # The code of a success, the context bytes, then the payload.
    return reqresp.encode_response_chunk(ResponseChunk(0, context, payload))


def test_sepolia_record_digest() -> None:
    # A bootnode record of Sepolia holds the digest of Bellatrix.
    digest = enr.consensus_entries("phase0", enr.from_text(SEPOLIA_RECORD)).eth2.fork_digest
    low, _ = consensus.reqresp_response_bounds("bellatrix", _id("beacon_blocks_by_range", 2))
    payload = bytes(low)
    decoded = consensus.reqresp_decode_chunk(
        "fusaka",
        _id("beacon_blocks_by_range", 2),
        SEPOLIA_ROOT,
        _success(digest, payload),
        config=SEPOLIA,
    )
    assert decoded == ("bellatrix", ResponseChunk(0, digest, payload))


def test_phase0_block_at_version_2() -> None:
    # Version 2 also serves the blocks of Phase 0, which carry the digest of epoch 0.
    digest = consensus.compute_fork_digest("mainnet", ROOT, 0)
    low, _ = consensus.reqresp_response_bounds("phase0", _id("beacon_blocks_by_range", 1))
    payload = bytes(low)
    decoded = consensus.reqresp_decode_chunk(
        "fusaka", _id("beacon_blocks_by_range", 2), ROOT, _success(digest, payload)
    )
    assert decoded == ("phase0", ResponseChunk(0, digest, payload))


# The epoch at which each fork of mainnet starts, and the two entries of its blob schedule.
# EthLib names Capella `shapella`, Deneb `dencun`, Electra `pectra` and Fulu `fusaka`.
#
# File: configs/mainnet.yaml
# Repository: ethereum/consensus-specs
# Commit: aa16bb4c156184e9548a997d53efaf2a228a6304
MAINNET_DIGEST_FORKS = [
    (0, "phase0"),
    (74240, "altair"),
    (144896, "bellatrix"),
    (194048, "shapella"),
    (269568, "dencun"),
    (364032, "pectra"),
    (411392, "fusaka"),
    (412672, "fusaka"),
    (419072, "fusaka"),
]


@pytest.mark.parametrize(("start", "fork"), MAINNET_DIGEST_FORKS)
def test_each_digest_epoch(start: int, fork: str) -> None:
    # A chunk with the digest of each epoch at which the digest changes has the fork of that epoch.
    digest = consensus.compute_fork_digest("mainnet", ROOT, start)
    low, _ = consensus.reqresp_response_bounds(
        fork, _id("beacon_blocks_by_root", 1 if fork == "phase0" else 2)
    )
    decoded = consensus.reqresp_decode_chunk(
        "hegota", _id("beacon_blocks_by_root", 2), ROOT, _success(digest, bytes(low))
    )
    assert decoded == (fork, ResponseChunk(0, digest, bytes(low)))


def test_digest_epochs_are_the_listed_ones() -> None:
    # The list above holds every epoch at which the digest of mainnet changes.
    starts = [start for start, _ in MAINNET_DIGEST_FORKS]
    assert consensus.digest_epochs("mainnet") == [*starts, FAR_FUTURE_EPOCH]


def test_blocks_by_head_phase0_digest() -> None:
    # Blocks by head, from Fulu, also serves the blocks of Phase 0.
    digest = consensus.compute_fork_digest("mainnet", ROOT, 0)
    low, _ = consensus.reqresp_response_bounds("phase0", _id("beacon_blocks_by_range", 1))
    decoded = consensus.reqresp_decode_chunk(
        "fusaka", _id("beacon_blocks_by_head", 1), ROOT, _success(digest, bytes(low))
    )
    assert decoded == ("phase0", ResponseChunk(0, digest, bytes(low)))


@pytest.mark.parametrize(
    ("protocol", "start", "fork"),
    [
        # The light client messages have no type at Phase 0.
        (_id("light_client_bootstrap", 1), 0, "phase0"),
        # Blob sidecars have types from Deneb on.
        (_id("blob_sidecars_by_range", 1), 194048, "shapella"),
        # Data column sidecars have types from Fulu on.
        (_id("data_column_sidecars_by_root", 1), 364032, "pectra"),
    ],
)
def test_digest_before_the_type_table(protocol: str, start: int, fork: str) -> None:
    # A digest of a fork before the first fork of the protocol names no payload type.
    digest = consensus.compute_fork_digest("mainnet", ROOT, start)
    data = _success(digest, bytes(8))
    with raises(ConsensusError, f"{protocol} is not a protocol of {fork}") as info:
        consensus.reqresp_decode_chunk("fusaka", protocol, ROOT, data)
    assert info.value.code == 301


def test_bounds_of_the_digest_fork() -> None:
    # An Altair block is longer than a Phase 0 block, since it adds a sync aggregate.
    phase0_low, _ = consensus.reqresp_response_bounds("phase0", _id("beacon_blocks_by_range", 1))
    altair_low, _ = consensus.reqresp_response_bounds("altair", _id("beacon_blocks_by_range", 2))
    assert phase0_low < altair_low
    # So a Phase 0 block under the digest of Altair is too short.
    digest = consensus.compute_fork_digest("mainnet", ROOT, 74240)
    data = _success(digest, bytes(phase0_low))
    with raises(ConsensusError, f"declared length {phase0_low} is below {altair_low}") as info:
        consensus.reqresp_decode_chunk("fusaka", _id("beacon_blocks_by_range", 2), ROOT, data)
    assert info.value.code == 9


def test_upper_bound_of_the_digest_fork() -> None:
    # The largest Phase 0 block is shorter than the largest Fulu block.
    _, phase0_high = consensus.reqresp_response_bounds("phase0", _id("beacon_blocks_by_range", 1))
    _, fusaka_high = consensus.reqresp_response_bounds("fusaka", _id("beacon_blocks_by_range", 2))
    assert phase0_high < fusaka_high
    # So under the digest of Phase 0, a declared length above the Phase 0 bound fails.
    # The chunk holds the code of a success, the digest and the length prefix, with no frame.
    digest = consensus.compute_fork_digest("mainnet", ROOT, 0)
    data = bytes([0]) + digest + uvarint.encode(phase0_high + 1)
    with raises(
        ConsensusError, f"declared length {phase0_high + 1} is above {phase0_high}"
    ) as info:
        consensus.reqresp_decode_chunk("fusaka", _id("beacon_blocks_by_range", 2), ROOT, data)
    assert info.value.code == 2


# The fork before the digest's, and the digest's own fork.
@pytest.mark.parametrize("exchange", ["pectra", "fusaka"])
def test_digest_of_a_scheduled_fork(exchange: str) -> None:
    # The type of a chunk depends on the epoch of its digest alone, not on the fork of the exchange.
    # Near a fork boundary, a peer can serve a block of a fork that the requester has not reached.
    protocol = _id("beacon_blocks_by_root", 2)
    digest = consensus.compute_fork_digest("mainnet", ROOT, 411392)
    low, _ = consensus.reqresp_response_bounds("fusaka", protocol)
    decoded = consensus.reqresp_decode_chunk(exchange, protocol, ROOT, _success(digest, bytes(low)))
    assert decoded == ("fusaka", ResponseChunk(0, digest, bytes(low)))


@pytest.mark.parametrize("exchange", ["fusaka", "glamsterdam", "hegota"])
def test_unscheduled_digest(exchange: str) -> None:
    # Mainnet schedules neither Gloas (`glamsterdam`) nor Heze (`hegota`).
    # So no epoch but the far future one has its digest, which uses the version of Heze.
    # No slot has that epoch, so no payload has that digest, whatever the fork of the exchange.
    digest = consensus.compute_fork_digest("mainnet", ROOT, FAR_FUTURE_EPOCH)
    assert consensus.fork_of_digest("mainnet", ROOT, digest) == (FAR_FUTURE_EPOCH, "hegota")
    # A payload that fits the bounds of Heze, so only the digest is wrong.
    low, _ = consensus.reqresp_response_bounds("hegota", _id("beacon_blocks_by_range", 2))
    data = _success(digest, bytes(low))
    message = f"only the far future epoch has the digest 0x{digest.hex()}"
    with raises(ConsensusError, message) as info:
        consensus.reqresp_decode_chunk(exchange, _id("beacon_blocks_by_range", 2), ROOT, data)
    assert info.value.code == 306


def test_digest_of_the_last_scheduled_fork() -> None:
    # On a chain that schedules every fork, the far future epoch has the digest of the last one.
    # The first epoch with that digest starts Heze, so the chunk decodes at Heze.
    config = {"GLOAS_FORK_EPOCH": 500000, "HEZE_FORK_EPOCH": 600000}
    digest = consensus.compute_fork_digest("mainnet", ROOT, FAR_FUTURE_EPOCH, config)
    assert consensus.fork_of_digest("mainnet", ROOT, digest, config) == (600000, "hegota")
    protocol = _id("beacon_blocks_by_range", 2)
    low, _ = consensus.reqresp_response_bounds("hegota", protocol)
    data = _success(digest, bytes(low))
    decoded = consensus.reqresp_decode_chunk("hegota", protocol, ROOT, data, config=config)
    assert decoded == ("hegota", ResponseChunk(0, digest, bytes(low)))


def test_unknown_digest() -> None:
    # A digest that no epoch of the chain has names no fork.
    digest = bytes(4)
    assert consensus.fork_of_digest("mainnet", ROOT, digest) is None
    data = _success(digest, bytes(8))
    with raises(ConsensusError, "no epoch of the chain has the digest 0x00000000") as info:
        consensus.reqresp_decode_chunk("fusaka", _id("data_column_sidecars_by_root", 1), ROOT, data)
    assert info.value.code == 305


@pytest.mark.parametrize(
    ("fork", "protocol", "size"),
    [
        # A 64-bit integer.
        ("phase0", _id("ping", 1), 8),
        # A sequence number of 8 bytes, then 64 attestation subnet bits in 8 bytes.
        ("phase0", _id("metadata", 1), 16),
    ],
)
def test_no_digest(fork: str, protocol: str, size: int) -> None:
    # These protocols send no context bytes, so the chunk has the fork of the exchange.
    payload = bytes(size)
    decoded = consensus.reqresp_decode_chunk(fork, protocol, ROOT, _success(b"", payload))
    assert decoded == (fork, ResponseChunk(0, b"", payload))


def test_version_1_blocks_no_digest() -> None:
    # Version 1 of blocks by range sends no digest, and carries a Phase 0 block.
    low, _ = consensus.reqresp_response_bounds("phase0", _id("beacon_blocks_by_range", 1))
    payload = bytes(low)
    decoded = consensus.reqresp_decode_chunk(
        "altair", _id("beacon_blocks_by_range", 1), ROOT, _success(b"", payload)
    )
    assert decoded == ("altair", ResponseChunk(0, b"", payload))


def test_error_chunk() -> None:
    # An error chunk carries no context bytes, and keeps the fork of the exchange.
    chunk = ResponseChunk(3, b"", b"gone")
    data = reqresp.encode_response_chunk(chunk)
    decoded = consensus.reqresp_decode_chunk("fusaka", _id("beacon_blocks_by_root", 2), ROOT, data)
    assert decoded == ("fusaka", chunk)


def test_protocol_not_at_fork() -> None:
    # The fork of the exchange must define the protocol, whatever the chunk carries.
    protocol = _id("blob_sidecars_by_range", 1)
    with raises(ConsensusError, f"{protocol} is not a protocol of altair") as info:
        consensus.reqresp_decode_chunk("altair", protocol, ROOT, _success(bytes(4), b""))
    assert info.value.code == 301


def test_truncated_digest() -> None:
    # A success with two bytes after its code cannot hold a digest of four.
    with raises(
        ConsensusError, "response chunk has 2 context bytes, not the 4 of the method"
    ) as info:
        consensus.reqresp_decode_chunk(
            "fusaka", _id("beacon_blocks_by_range", 2), ROOT, bytes([0, 1, 2])
        )
    assert info.value.code == 8
