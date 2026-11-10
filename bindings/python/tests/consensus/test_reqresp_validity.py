"""The check of a req/resp response against its request, one rule at a time."""

import pytest

from ethlib import consensus
from ethlib.consensus import ResponseItem
from ethlib.errors import ConsensusError
from raising import raises

# Each request is written here as SSZ bytes, field by field, as in the req/resp tests.
#
# An integer takes 8 bytes, little-endian; a root takes 32 bytes.
#
# A list of fixed-size items is their bytes in order.
#
# A field of variable size is a 4-byte offset in the fixed part, its bytes after.
#
# The values below are those of the mainnet preset and configuration:
#
# - MAX_REQUEST_BLOCKS is 1024, and MAX_REQUEST_BLOCKS_DENEB 128 from Deneb.
# - MAX_BLOBS_PER_BLOCK is 6, and MAX_BLOBS_PER_BLOCK_ELECTRA 9 from Electra.
# - NUMBER_OF_COLUMNS is 128.
# - INCLUSION_LIST_COMMITTEE_SIZE and MAX_REQUEST_INCLUSION_LIST are both 16.

PREFIX = "/eth2/beacon_chain/req/"


def _id(name: str, version: int = 1) -> str:
    return f"{PREFIX}{name}/{version}/ssz_snappy"


def _u64(*values: int) -> bytes:
    return b"".join(value.to_bytes(8, "little") for value in values)


def _root(n: int) -> bytes:
    return n.to_bytes(32, "big")


def _offset(n: int) -> bytes:
    return n.to_bytes(4, "little")


def _chain(start_slot: int, length: int) -> list[tuple[int, bytes, bytes]]:
    # Blocks at consecutive slots, each naming the one before it as its parent.
    return [(start_slot + i, _root(i), _root(i + 1)) for i in range(length)]


def _envelopes(start_slot: int, length: int) -> list[tuple[int, bytes, bytes, bytes]]:
    # Envelopes at consecutive slots, each payload naming the one before it as its parent.
    return [(start_slot + i, _root(1000 + i), _root(i), _root(i + 1)) for i in range(length)]


def _blob_slots(start_slot: int, slots: int, blobs: int) -> list[tuple[int, bytes, int]]:
    # Each slot has one block, with blobs of indices 0 to blobs - 1.
    return [(start_slot + s, _root(s), i) for s in range(slots) for i in range(blobs)]


A, B, C = _root(0xA), _root(0xB), _root(0xC)

# Blocks by range: start slot 10, count 4, so slots 10 to 13, with step 1.

BLOCKS_BY_RANGE = _u64(10, 4, 1)


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(10, A, B), (11, B, C)], True, id="linked"),
        pytest.param([(10, A, B), (13, B, C)], True, id="skipped-slots"),
        pytest.param([(13, A, B)], True, id="last-slot"),
        pytest.param([(9, A, B)], False, id="before-start"),
        pytest.param([(14, A, B)], False, id="after-end"),
        pytest.param([(11, A, B), (10, B, C)], False, id="slots-descend"),
        pytest.param([(11, A, B), (11, B, C)], False, id="slot-repeats"),
        pytest.param([(10, A, B), (11, A, C)], False, id="parent-not-linked"),
    ],
)
def test_blocks_by_range(items: list[ResponseItem], valid: bool) -> None:
    protocol = _id("beacon_blocks_by_range", 2)
    assert consensus.reqresp_response_is_valid("pectra", protocol, BLOCKS_BY_RANGE, items) is valid


def test_blocks_by_range_step_two_skips_the_parent_link() -> None:
    # A step other than 1 keeps the range of slots, and drops only the parent link.
    request = _u64(10, 4, 2)
    protocol = _id("beacon_blocks_by_range")
    unlinked = [(10, A, B), (11, A, C)]
    assert consensus.reqresp_response_is_valid("pectra", protocol, request, unlinked)
    assert not consensus.reqresp_response_is_valid("pectra", protocol, request, [(14, A, B)])
    descending = [(11, A, B), (10, A, C)]
    assert not consensus.reqresp_response_is_valid("pectra", protocol, request, descending)


@pytest.mark.parametrize("fork, limit", [("phase0", 1024), ("dencun", 128), ("hegota", 128)])
def test_blocks_by_range_request_limit(fork: str, limit: int) -> None:
    # The count of 2000 slots allows more blocks than the request limit of the fork.
    request, protocol = _u64(0, 2000, 1), _id("beacon_blocks_by_range")
    assert consensus.reqresp_response_is_valid(fork, protocol, request, _chain(0, limit))
    assert not consensus.reqresp_response_is_valid(fork, protocol, request, _chain(0, limit + 1))


def test_blocks_by_range_count_bound() -> None:
    # Blocks with ascending slots inside a range of count slots number at most the count.
    # So a response over the count also breaks the order, and the count has no case of its own.
    request, protocol = _u64(10, 2, 1), _id("beacon_blocks_by_range")
    assert consensus.reqresp_response_is_valid("pectra", protocol, request, _chain(10, 2))
    over = [*_chain(10, 2), (11, _root(2), _root(3))]
    assert not consensus.reqresp_response_is_valid("pectra", protocol, request, over)


# Blocks by root: the roots A and B.


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(5, C, A), (9, C, B)], True, id="both"),
        pytest.param([(9, C, B), (5, C, A)], True, id="any-order"),
        pytest.param([(5, A, C)], False, id="not-requested"),
        pytest.param([(5, C, A), (5, C, A)], True, id="repeat-within-length"),
        pytest.param([(5, C, A), (5, C, A), (5, C, A)], False, id="over-length"),
    ],
)
@pytest.mark.parametrize("version", [1, 2])
def test_blocks_by_root(items: list[ResponseItem], valid: bool, version: int) -> None:
    protocol = _id("beacon_blocks_by_root", version)
    assert consensus.reqresp_response_is_valid("pectra", protocol, A + B, items) is valid


# Blob sidecars by range: start slot 100, count 3, so slots 100 to 102.

BLOBS_BY_RANGE = _u64(100, 3)


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(100, A, 0), (100, A, 1), (102, B, 0)], True, id="two-blocks"),
        pytest.param([(100, A, 0), (100, A, 1), (100, A, 2)], True, id="last-blobs-may-lack"),
        pytest.param([(102, A, 0)], True, id="last-slot"),
        pytest.param([(99, A, 0)], False, id="before-start"),
        pytest.param([(103, A, 0)], False, id="after-end"),
        pytest.param([(100, A, 1)], False, id="first-index-not-zero"),
        pytest.param([(100, A, 0), (101, B, 1)], False, id="next-block-not-at-zero"),
        pytest.param([(100, A, 0), (100, A, 2)], False, id="index-skipped"),
        pytest.param([(100, A, 1), (100, A, 0)], False, id="index-descends"),
        pytest.param([(100, A, 0), (100, A, 0)], False, id="index-repeats"),
        pytest.param([(100, A, 0), (100, B, 1)], False, id="other-root-same-slot"),
        pytest.param([(101, A, 0), (100, B, 0)], False, id="slots-descend"),
    ],
)
def test_blob_sidecars_by_range(items: list[ResponseItem], valid: bool) -> None:
    protocol = _id("blob_sidecars_by_range")
    assert consensus.reqresp_response_is_valid("dencun", protocol, BLOBS_BY_RANGE, items) is valid


@pytest.mark.parametrize("fork, blobs", [("dencun", 6), ("pectra", 9), ("fusaka", 9)])
def test_blob_sidecars_by_range_index_bound(fork: str, blobs: int) -> None:
    # The indices of one block run from 0 to the most blobs of one block, less one.
    protocol = _id("blob_sidecars_by_range")
    full = _blob_slots(100, 1, blobs)
    assert consensus.reqresp_response_is_valid(fork, protocol, BLOBS_BY_RANGE, full)
    over = _blob_slots(100, 1, blobs + 1)
    assert not consensus.reqresp_response_is_valid(fork, protocol, BLOBS_BY_RANGE, over)


@pytest.mark.parametrize("fork, blobs", [("dencun", 6), ("pectra", 9)])
def test_blob_sidecars_by_range_request_limit(fork: str, blobs: int) -> None:
    # The request limit is 128 blocks of the most blobs; a count of 200 allows more.
    request, protocol = _u64(0, 200), _id("blob_sidecars_by_range")
    full = _blob_slots(0, 128, blobs)
    assert consensus.reqresp_response_is_valid(fork, protocol, request, full)
    over = _blob_slots(0, 129, blobs)
    assert not consensus.reqresp_response_is_valid(fork, protocol, request, over)


# Blob sidecars by root: the identifiers (A, 0) and (B, 3), each a root and an index.

BLOBS_BY_ROOT = A + _u64(0) + B + _u64(3)


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(7, B, 3), (5, A, 0)], True, id="both-any-order"),
        pytest.param([(5, A, 0), (5, A, 0)], True, id="repeat-within-length"),
        pytest.param([(5, A, 3)], False, id="index-of-other-root"),
        pytest.param([(5, C, 0)], False, id="root-not-requested"),
        pytest.param([(5, A, 0), (5, A, 0), (7, B, 3)], False, id="over-length"),
    ],
)
def test_blob_sidecars_by_root(items: list[ResponseItem], valid: bool) -> None:
    protocol = _id("blob_sidecars_by_root")
    assert consensus.reqresp_response_is_valid("pectra", protocol, BLOBS_BY_ROOT, items) is valid


# Column sidecars by range: start slot 50, count 2, columns 3 and 7.
# The columns follow the two integers as a list, at offset 20.

COLUMNS_BY_RANGE = _u64(50, 2) + _offset(20) + _u64(3, 7)


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(50, A, 3), (50, A, 7), (51, B, 3), (51, B, 7)], True, id="two-blocks"),
        pytest.param([(51, B, 3), (51, B, 7)], True, id="one-block"),
        pytest.param([(50, A, 3)], False, id="requested-column-missing"),
        pytest.param([(50, A, 3), (50, A, 5), (50, A, 7)], False, id="column-not-requested"),
        pytest.param([(50, A, 3), (50, A, 3), (50, A, 7)], False, id="column-repeats"),
        pytest.param([(50, A, 7), (50, A, 3)], False, id="columns-descend"),
        pytest.param([(50, A, 3), (50, B, 7)], False, id="other-root-same-slot"),
        pytest.param([(49, A, 3), (49, A, 7)], False, id="before-start"),
        pytest.param([(52, A, 3), (52, A, 7)], False, id="after-end"),
        pytest.param([(51, B, 3), (51, B, 7), (50, A, 3), (50, A, 7)], False, id="slots-descend"),
    ],
)
def test_data_column_sidecars_by_range(items: list[ResponseItem], valid: bool) -> None:
    protocol = _id("data_column_sidecars_by_range")
    assert consensus.reqresp_response_is_valid("fusaka", protocol, COLUMNS_BY_RANGE, items) is valid


def test_data_column_sidecars_by_range_index_bound() -> None:
    # A request may name column 128, but no sidecar has an index of 128 or more.
    # So the only valid response is empty.
    request = _u64(50, 2) + _offset(20) + _u64(3, 128)
    protocol = _id("data_column_sidecars_by_range")
    assert consensus.reqresp_response_is_valid("fusaka", protocol, request, [])
    served = [(50, A, 3), (50, A, 128)]
    assert not consensus.reqresp_response_is_valid("fusaka", protocol, request, served)


def test_data_column_sidecars_by_range_request_limit() -> None:
    # The request limit is 128 blocks of the 128 columns; a count of 200 allows more.
    columns = list(range(128))
    request = _u64(0, 200) + _offset(20) + _u64(*columns)
    protocol = _id("data_column_sidecars_by_range")
    full = [(s, _root(s), c) for s in range(128) for c in columns]
    assert consensus.reqresp_response_is_valid("fusaka", protocol, request, full)
    over = [(s, _root(s), c) for s in range(129) for c in columns]
    assert not consensus.reqresp_response_is_valid("fusaka", protocol, request, over)


# Column sidecars by root: block A for columns 1 and 2, block B for column 5.
# The list holds two identifiers of variable size, so it starts with their two offsets.
# Each identifier is a root and the offset 36 of its columns, then those columns.

FIRST = A + _offset(36) + _u64(1, 2)
SECOND = B + _offset(36) + _u64(5)
COLUMNS_BY_ROOT = _offset(8) + _offset(8 + len(FIRST)) + FIRST + SECOND


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(9, B, 5), (8, A, 2), (8, A, 1)], True, id="all-any-order"),
        pytest.param([(8, A, 1), (8, A, 1), (8, A, 1)], True, id="repeat-within-length"),
        pytest.param([(8, A, 5)], False, id="column-of-other-block"),
        pytest.param([(8, C, 1)], False, id="root-not-requested"),
        pytest.param([(8, A, 1), (8, A, 2), (9, B, 5), (8, A, 1)], False, id="over-length"),
    ],
)
def test_data_column_sidecars_by_root(items: list[ResponseItem], valid: bool) -> None:
    protocol = _id("data_column_sidecars_by_root")
    assert consensus.reqresp_response_is_valid("fusaka", protocol, COLUMNS_BY_ROOT, items) is valid


# Payload envelopes by range: start slot 20, count 5, so slots 20 to 24.
# An envelope is its slot, its block root, the parent hash and the hash of its payload.

ENVELOPES_BY_RANGE = _u64(20, 5)


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(20, A, B, C), (22, B, C, A)], True, id="linked-with-gap"),
        pytest.param([(24, A, B, C)], True, id="last-slot"),
        pytest.param([(19, A, B, C)], False, id="before-start"),
        pytest.param([(25, A, B, C)], False, id="after-end"),
        pytest.param([(22, A, B, C), (21, B, C, A)], False, id="slots-descend"),
        pytest.param([(21, A, B, C), (21, B, C, A)], False, id="slot-repeats"),
        pytest.param([(20, A, B, C), (22, B, B, A)], False, id="parent-not-linked"),
    ],
)
def test_execution_payload_envelopes_by_range(items: list[ResponseItem], valid: bool) -> None:
    protocol = _id("execution_payload_envelopes_by_range")
    result = consensus.reqresp_response_is_valid("glamsterdam", protocol, ENVELOPES_BY_RANGE, items)
    assert result is valid


def test_execution_payload_envelopes_by_range_request_limit() -> None:
    # The request limit is 128 envelopes; a count of 200 allows more.
    request, protocol = _u64(0, 200), _id("execution_payload_envelopes_by_range")
    full = _envelopes(0, 128)
    assert consensus.reqresp_response_is_valid("glamsterdam", protocol, request, full)
    over = _envelopes(0, 129)
    assert not consensus.reqresp_response_is_valid("glamsterdam", protocol, request, over)


# Payload envelopes by root: the block roots A and B.


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(3, B, C, C), (2, A, C, C)], True, id="both-any-order"),
        pytest.param([(2, A, C, C), (2, A, C, C)], True, id="repeat-within-length"),
        pytest.param([(2, C, A, B)], False, id="root-not-requested"),
        pytest.param([(2, A, C, C), (2, A, C, C), (3, B, C, C)], False, id="over-length"),
    ],
)
def test_execution_payload_envelopes_by_root(items: list[ResponseItem], valid: bool) -> None:
    protocol = _id("execution_payload_envelopes_by_root")
    assert consensus.reqresp_response_is_valid("hegota", protocol, A + B, items) is valid


# Inclusion lists by indices: slot 96, dependent root C, and a bit for each of the 16 seats.
# Bit i of the bitvector, counted from the low bit of the first byte, is seat i.
# The committee holds validator 1000 + i at seat i.

COMMITTEE = [1000 + seat for seat in range(16)]


def _lists_request(*seats: int) -> bytes:
    bits = sum(1 << seat for seat in seats)
    return _u64(96) + C + bits.to_bytes(2, "little")


@pytest.mark.parametrize(
    "items, valid",
    [
        pytest.param([], True, id="empty"),
        pytest.param([(96, 1000, C), (96, 1002, C)], True, id="both-seats"),
        pytest.param([(96, 1002, C)], True, id="one-seat"),
        pytest.param([(96, 1001, C)], False, id="seat-not-requested"),
        pytest.param([(96, 5, C)], False, id="not-in-committee"),
        pytest.param([(97, 1000, C)], False, id="other-slot"),
        pytest.param([(96, 1000, A)], False, id="other-dependent-root"),
        pytest.param([(96, 1000, C), (96, 1000, C)], True, id="repeat-within-seats"),
        pytest.param([(96, 1000, C), (96, 1000, C), (96, 1002, C)], False, id="over-seats"),
    ],
)
def test_inclusion_lists_by_indices(items: list[ResponseItem], valid: bool) -> None:
    protocol, request = _id("inclusion_lists_by_indices"), _lists_request(0, 2)
    result = consensus.reqresp_response_is_valid("hegota", protocol, request, items, COMMITTEE)
    assert result is valid


def test_inclusion_lists_validator_with_several_seats() -> None:
    # Validator 7 holds seats 0 and 3; the request asks for seat 3 alone.
    committee = [7, 1001, 1002, 7, *COMMITTEE[4:]]
    protocol, request = _id("inclusion_lists_by_indices"), _lists_request(3)
    lists = [(96, 7, C)]
    assert consensus.reqresp_response_is_valid("hegota", protocol, request, lists, committee)
    # One requested seat bounds the response at one list.
    twice = [(96, 7, C), (96, 7, C)]
    assert not consensus.reqresp_response_is_valid("hegota", protocol, request, twice, committee)


def test_inclusion_lists_request_limit() -> None:
    # The 16 seats of the committee meet the request limit of 16 lists.
    # So a response over the limit also asks for more seats than there are, and has no case alone.
    protocol, request = _id("inclusion_lists_by_indices"), _lists_request(*range(16))
    lists = [(96, validator, C) for validator in COMMITTEE]
    assert consensus.reqresp_response_is_valid("hegota", protocol, request, lists, COMMITTEE)
    over = [*lists, (96, 1000, C)]
    assert not consensus.reqresp_response_is_valid("hegota", protocol, request, over, COMMITTEE)


@pytest.mark.parametrize("size", [0, 15, 17])
def test_inclusion_lists_committee_size(size: int) -> None:
    protocol, request = _id("inclusion_lists_by_indices"), _lists_request(0)
    committee = list(range(size))
    with raises(ConsensusError, f"the committee has {size} seats, not 16") as info:
        consensus.reqresp_response_is_valid("hegota", protocol, request, [], committee)
    assert info.value.code == 0


def test_committee_read_only_for_inclusion_lists() -> None:
    # Any other protocol ignores the committee, whatever its size.
    protocol = _id("beacon_blocks_by_range")
    assert consensus.reqresp_response_is_valid("pectra", protocol, BLOCKS_BY_RANGE, [], [1, 2])


@pytest.mark.parametrize(
    "fork, protocol",
    [
        ("pectra", _id("status")),
        ("fusaka", _id("status", 2)),
        ("pectra", _id("ping")),
        ("pectra", _id("metadata", 2)),
        ("pectra", _id("goodbye")),
        ("pectra", _id("light_client_bootstrap")),
        ("fusaka", _id("beacon_blocks_by_head")),
    ],
)
def test_protocol_without_check(fork: str, protocol: str) -> None:
    with raises(ConsensusError, f"{protocol} has no response check") as info:
        consensus.reqresp_response_is_valid(fork, protocol, b"", [])
    assert info.value.code == 0


def test_unknown_protocol() -> None:
    protocol = _id("blocks_by_nothing")
    with raises(ConsensusError, f"{protocol} names no protocol") as info:
        consensus.reqresp_response_is_valid("pectra", protocol, b"", [])
    assert info.value.code == 0


def test_protocol_not_at_fork() -> None:
    protocol = _id("blob_sidecars_by_range")
    with raises(ConsensusError, f"{protocol} is not a protocol of shapella") as info:
        consensus.reqresp_response_is_valid("shapella", protocol, _u64(0, 1), [])
    assert info.value.code == 301


def test_unknown_fork() -> None:
    with raises(ConsensusError, "no fork named nofork"):
        consensus.reqresp_response_is_valid("nofork", _id("beacon_blocks_by_range"), b"", [])


def test_malformed_request() -> None:
    # The request has three integers, so 24 bytes; 23 are too few.
    protocol = _id("beacon_blocks_by_range")
    with raises(ConsensusError, "request rejected: EthLib.Serialization.Ssz.Err.scope 24 23"):
        consensus.reqresp_response_is_valid("pectra", protocol, bytes(23), [])


def test_request_over_its_limit() -> None:
    # From Deneb, a request names at most 128 roots.
    protocol = _id("beacon_blocks_by_root")
    with raises(ConsensusError, "request rejected: EthLib.Serialization.Ssz.Err.overLimit 128 129"):
        consensus.reqresp_response_is_valid("pectra", protocol, bytes(32 * 129), [])


def test_malformed_item() -> None:
    # A root of 31 bytes, or a sidecar where a block is due.
    protocol = _id("beacon_blocks_by_range")
    with raises(ConsensusError, "expected 32 bytes, got 31") as info:
        consensus.reqresp_response_is_valid("pectra", protocol, BLOCKS_BY_RANGE, [(10, A, A[1:])])
    assert info.value.code == 0
    with raises(ConsensusError, "expected bytes"):
        consensus.reqresp_response_is_valid("pectra", protocol, BLOCKS_BY_RANGE, [(10, A, 0)])
