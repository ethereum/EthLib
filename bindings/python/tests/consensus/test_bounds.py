"""The length bounds of request, response and gossip payloads, against sizes worked out by hand."""

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError
from ethlib.networking import reqresp
from raising import raises

# Each size is the sum of the fixed fields of its container.
#
# A fork digest takes 4 bytes, a root 32, an integer 8 and a signature 96.

PREFIX = "/eth2/beacon_chain/req/"


def _id(name: str, version: int) -> str:
    return f"{PREFIX}{name}/{version}/ssz_snappy"


# A payload follows the framing format of google/snappy (framing_format.txt).
#
# Its length is a protobuf varint, as in the req/resp tests.
#
# So no byte comes from the code under test.
STREAM_IDENTIFIER = bytes([0xFF, 0x06, 0x00, 0x00]) + b"sNaPpY"


def _crc32c(data: bytes) -> int:
    # CRC-32C (Castagnoli), reflected polynomial 0x82f63b78, bit by bit.
    crc = 0xFFFFFFFF
    for byte in data:
        crc ^= byte
        for _ in range(8):
            crc = (crc >> 1) ^ (0x82F63B78 if crc & 1 else 0)
    return crc ^ 0xFFFFFFFF


def _payload(data: bytes) -> bytes:
    # The length as a one-byte varint, the stream identifier, then one uncompressed chunk.
    assert len(data) < 0x80
    crc = _crc32c(data)
    masked = ((((crc >> 15) | (crc << 17)) & 0xFFFFFFFF) + 0xA282EAD8) & 0xFFFFFFFF
    body = masked.to_bytes(4, "little") + data
    return (
        bytes([len(data)])
        + STREAM_IDENTIFIER
        + bytes([0x01])
        + len(body).to_bytes(3, "little")
        + body
    )


def test_status_v1_request() -> None:
    # fork digest, finalized root, finalized epoch, head root, head slot.
    assert consensus.reqresp_request_bounds("phase0", _id("status", 1)) == (84, 84)


def test_status_v2_request() -> None:
    # Fulu adds the earliest available slot.
    assert consensus.reqresp_request_bounds("fusaka", _id("status", 2)) == (92, 92)


def test_goodbye_request() -> None:
    assert consensus.reqresp_request_bounds("phase0", _id("goodbye", 1)) == (8, 8)


def test_blocks_by_root_request() -> None:
    # A list of at most MAX_REQUEST_BLOCKS roots, 1024 before Deneb and 128 from it.
    assert consensus.reqresp_request_bounds("phase0", _id("beacon_blocks_by_root", 1)) == (
        0,
        1024 * 32,
    )
    assert consensus.reqresp_request_bounds("dencun", _id("beacon_blocks_by_root", 2)) == (
        0,
        128 * 32,
    )


def test_metadata_has_no_request() -> None:
    with raises(ConsensusError, f"{_id('metadata', 1)} carries no request") as info:
        consensus.reqresp_request_bounds("phase0", _id("metadata", 1))
    assert info.value.code == 302


def test_request_protocol_not_at_fork() -> None:
    with raises(ConsensusError, f"{_id('status', 2)} is not a protocol of phase0") as info:
        consensus.reqresp_request_bounds("phase0", _id("status", 2))
    assert info.value.code == 301


def test_request_unknown_protocol() -> None:
    with raises(
        ConsensusError, "/eth2/beacon_chain/req/nothing/1/ssz_snappy names no protocol"
    ) as info:
        consensus.reqresp_request_bounds("phase0", _id("nothing", 1))
    assert info.value.code == 0


def test_request_unknown_fork() -> None:
    with raises(ConsensusError, "no fork named nowhere") as info:
        consensus.reqresp_request_bounds("nowhere", _id("status", 1))
    assert info.value.code == 0


def test_inclusion_list_request_from_heze() -> None:
    # The request protocol of inclusion lists is new in Heze.
    with raises(
        ConsensusError, f"{_id('inclusion_lists_by_indices', 1)} is not a protocol of glamsterdam"
    ) as info:
        consensus.reqresp_request_bounds("glamsterdam", _id("inclusion_lists_by_indices", 1))
    assert info.value.code == 301


def test_request_unknown_preset() -> None:
    with raises(ConsensusError, "no preset is named nowhere"):
        consensus.reqresp_request_bounds("phase0", _id("status", 1), name="nowhere")


def test_request_bounds_admit_the_request() -> None:
    # An 84-byte status passes the payload decoder at its bounds, and 83 bytes do not.
    low, high = consensus.reqresp_request_bounds("phase0", _id("status", 1))
    status = bytes(84)
    assert reqresp.decode_payload(low, high, _payload(status)) == status
    with raises(ValueError, "declared length 83 is below 84"):
        reqresp.decode_payload(low, high, _payload(bytes(83)))


def test_ping_response() -> None:
    assert consensus.reqresp_response_bounds("phase0", _id("ping", 1)) == (8, 8)


def test_metadata_v1_response() -> None:
    # A sequence number of 8 bytes, then 64 attestation subnet bits in 8 bytes.
    assert consensus.reqresp_response_bounds("phase0", _id("metadata", 1)) == (16, 16)


def test_metadata_v2_response() -> None:
    # Altair adds 4 sync committee subnet bits, which take one byte.
    assert consensus.reqresp_response_bounds("altair", _id("metadata", 2)) == (17, 17)


def test_response_protocol_not_at_fork() -> None:
    with raises(
        ConsensusError, f"{_id('blob_sidecars_by_range', 1)} is not a protocol of altair"
    ) as info:
        consensus.reqresp_response_bounds("altair", _id("blob_sidecars_by_range", 1))
    assert info.value.code == 301


def test_voluntary_exit_topic() -> None:
    # An epoch and a validator index, then the signature.
    assert consensus.gossip_topic_bound("phase0", "voluntary_exit") == 8 + 8 + 96


def test_sync_committee_topic() -> None:
    # A slot, a block root, a validator index and a signature.
    assert consensus.gossip_topic_bound("altair", "sync_committee_0") == 8 + 32 + 8 + 96


def test_topic_not_at_fork() -> None:
    with raises(ConsensusError, "sync_committee_0 is not a topic of phase0") as info:
        consensus.gossip_topic_bound("phase0", "sync_committee_0")
    assert info.value.code == 303


def test_inclusion_list_topic_from_heze() -> None:
    with raises(ConsensusError, "inclusion_list is not a topic of glamsterdam") as info:
        consensus.gossip_topic_bound("glamsterdam", "inclusion_list")
    assert info.value.code == 303


def test_voluntary_exit_topic_at_heze() -> None:
    # An epoch and a validator index, then the signature.
    assert consensus.gossip_topic_bound("hegota", "voluntary_exit") == 8 + 8 + 96


# These messages hold lists without a limit, so the specification sets a size limit on each.
#
# Aggregates, attester slashings and bids have one from Gloas, and inclusion lists from Heze.
#
# A committee has at most 2048 members, and a slot has 64 committees on mainnet and 4 on minimal.
COMMITTEES = [("mainnet", 64), ("minimal", 4)]


@pytest.mark.parametrize("fork", ["glamsterdam", "hegota"])
@pytest.mark.parametrize("name, committees", COMMITTEES)
def test_aggregate_topic_from_gloas(fork: str, name: str, committees: int) -> None:
    # An offset, the data, the signature and the committee bits come first.
    # Then come one bit for each member of every committee and an end bit, in whole bytes.
    attestation = 4 + 128 + 96 + (committees + 7) // 8 + 2048 * committees // 8 + 1
    # An offset and the signature, then the aggregator index, an offset and the selection proof.
    bound = 4 + 96 + 8 + 4 + 96 + attestation
    assert consensus.gossip_topic_bound(fork, "beacon_aggregate_and_proof", name) == bound


@pytest.mark.parametrize("fork", ["glamsterdam", "hegota"])
@pytest.mark.parametrize("name, committees", COMMITTEES)
def test_attester_slashing_topic_from_gloas(fork: str, name: str, committees: int) -> None:
    # Each attestation has an offset, the data, the signature and an index for each attester.
    attestation = 4 + 128 + 96 + 8 * 2048 * committees
    # Two offsets come before the two attestations.
    bound = 4 + 4 + 2 * attestation
    assert consensus.gossip_topic_bound(fork, "attester_slashing", name) == bound


@pytest.mark.parametrize("name", ["mainnet", "minimal"])
@pytest.mark.parametrize("fork, inclusion_bits", [("glamsterdam", 0), ("hegota", 16)])
def test_execution_payload_bid_topic_from_gloas(fork: str, inclusion_bits: int, name: str) -> None:
    # Four 32-byte values, an address, five integers, an offset and the root of the requests.
    # Heze adds 16 inclusion bits, and the commitments of 48 bytes each come last.
    # The size limit counts 4096 commitments on both presets.
    bid = 4 * 32 + 20 + 5 * 8 + 4 + 32 + inclusion_bits // 8 + 4096 * 48
    # An offset and the signature come before the bid.
    bound = 4 + 96 + bid
    assert consensus.gossip_topic_bound(fork, "execution_payload_bid", name) == bound


@pytest.mark.parametrize("name", ["mainnet", "minimal"])
def test_inclusion_list_topic_at_heze(name: str) -> None:
    # A slot, a validator index, a root and an offset take 52 bytes.
    # The transactions hold at most 8192 bytes.
    # The size limit counts 8192 transactions of one byte, each after a 4-byte offset.
    inclusion_list = 52 + 8192 * (4 + 1)
    # An offset and the signature come before the list.
    bound = 4 + 96 + inclusion_list
    assert consensus.gossip_topic_bound("hegota", "inclusion_list", name) == bound


def test_unknown_topic() -> None:
    with raises(ConsensusError, "nothing names no topic") as info:
        consensus.gossip_topic_bound("phase0", "nothing")
    assert info.value.code == 0
