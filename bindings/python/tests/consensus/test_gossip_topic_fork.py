"""A gossip message decodes at the bound of its topic at the fork that the topic's digest names."""

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError
from ethlib.networking import enr, snappy
from raising import raises

from .test_fork_digest import SEPOLIA, SEPOLIA_RECORD, SEPOLIA_ROOT
from .test_reqresp_chunk import FAR_FUTURE_EPOCH, MAINNET_DIGEST_FORKS, ROOT


def _topic(digest: bytes, name: str) -> str:
    return f"/eth2/{digest.hex()}/{name}/ssz_snappy"


def test_sepolia_record_digest() -> None:
    # A bootnode record of Sepolia holds the digest of Bellatrix.
    digest = enr.consensus_entries("phase0", enr.from_text(SEPOLIA_RECORD)).eth2.fork_digest
    payload = bytes(consensus.gossip_topic_bound("bellatrix", "voluntary_exit"))
    decoded = consensus.gossip_decode_at_topic(
        _topic(digest, "voluntary_exit"), SEPOLIA_ROOT, snappy.compress(payload), config=SEPOLIA
    )
    assert decoded == ("bellatrix", "voluntary_exit", payload)


@pytest.mark.parametrize(("start", "fork"), MAINNET_DIGEST_FORKS)
def test_each_digest_epoch(start: int, fork: str) -> None:
    # A message on the topic of each digest of the mainnet schedule has the fork of that digest.
    digest = consensus.compute_fork_digest("mainnet", ROOT, start)
    payload = bytes(consensus.gossip_topic_bound(fork, "beacon_aggregate_and_proof") // 2)
    decoded = consensus.gossip_decode_at_topic(
        _topic(digest, "beacon_aggregate_and_proof"), ROOT, snappy.compress(payload)
    )
    assert decoded == (fork, "beacon_aggregate_and_proof", payload)


def test_subnet_topic() -> None:
    # An attestation subnet topic of Altair.
    digest = consensus.compute_fork_digest("mainnet", ROOT, 74240)
    payload = bytes(64)
    decoded = consensus.gossip_decode_at_topic(
        _topic(digest, "beacon_attestation_5"), ROOT, snappy.compress(payload)
    )
    assert decoded == ("altair", "beacon_attestation_5", payload)


def test_bound_of_the_digest_fork() -> None:
    # An aggregate grows at Electra, so one payload fits under the digest of Electra alone.
    deneb = consensus.gossip_topic_bound("dencun", "beacon_aggregate_and_proof")
    electra = consensus.gossip_topic_bound("pectra", "beacon_aggregate_and_proof")
    assert deneb < electra
    payload = bytes(deneb + 1)
    data = snappy.compress(payload)
    digest = consensus.compute_fork_digest("mainnet", ROOT, 364032)
    decoded = consensus.gossip_decode_at_topic(
        _topic(digest, "beacon_aggregate_and_proof"), ROOT, data
    )
    assert decoded == ("pectra", "beacon_aggregate_and_proof", payload)
    digest = consensus.compute_fork_digest("mainnet", ROOT, 269568)
    with raises(
        ConsensusError,
        f"EthLib.Networking.Gossip.PayloadError.payloadTooLong {deneb + 1} {deneb}",
    ) as info:
        consensus.gossip_decode_at_topic(_topic(digest, "beacon_aggregate_and_proof"), ROOT, data)
    assert info.value.code == 4


def test_bound_of_a_fixed_size_message() -> None:
    # A message one byte over the bound of its topic is refused.
    digest = consensus.compute_fork_digest("mainnet", ROOT, 0)
    # A signed voluntary exit is fixed-size: an epoch (8), a validator index (8), a signature (96).
    # Its topic has no size limit of its own, so its bound is that size.
    bound = 8 + 8 + 96
    data = snappy.compress(bytes(bound + 1))
    with raises(
        ConsensusError,
        f"EthLib.Networking.Gossip.PayloadError.payloadTooLong {bound + 1} {bound}",
    ) as info:
        consensus.gossip_decode_at_topic(_topic(digest, "voluntary_exit"), ROOT, data)
    assert info.value.code == 4


def test_not_snappy() -> None:
    digest = consensus.compute_fork_digest("mainnet", ROOT, 0)
    with raises(
        ConsensusError,
        (
            "EthLib.Networking.Gossip.PayloadError.snappy "
            "(EthLib.Networking.Snappy.SnappyError.lengthMismatch 0 1)"
        ),
    ) as info:
        consensus.gossip_decode_at_topic(_topic(digest, "voluntary_exit"), ROOT, bytes(32))
    assert info.value.code == 3


def test_unknown_digest() -> None:
    assert consensus.fork_of_digest("mainnet", ROOT, bytes(4)) is None
    with raises(ConsensusError, "no epoch of the chain has the digest 0x00000000") as info:
        consensus.gossip_decode_at_topic(
            _topic(bytes(4), "beacon_block"), ROOT, snappy.compress(bytes(8))
        )
    assert info.value.code == 305


def test_unscheduled_digest() -> None:
    # Mainnet schedules neither Gloas (`glamsterdam`) nor Heze (`hegota`).
    # So no epoch but the far future one has its digest, which uses the version of Heze.
    # No slot has that epoch, so no message has that digest.
    digest = consensus.compute_fork_digest("mainnet", ROOT, FAR_FUTURE_EPOCH)
    assert consensus.fork_of_digest("mainnet", ROOT, digest) == (FAR_FUTURE_EPOCH, "hegota")
    # The topic exists at Heze and the data fits its bound, so only the digest is wrong.
    with raises(
        ConsensusError, f"only the far future epoch has the digest 0x{digest.hex()}"
    ) as info:
        consensus.gossip_decode_at_topic(
            _topic(digest, "beacon_block"), ROOT, snappy.compress(bytes(8))
        )
    assert info.value.code == 306


@pytest.mark.parametrize(
    ("start", "name", "fork"),
    [
        # The light client topics start at Altair.
        (0, "light_client_finality_update", "phase0"),
        # Fulu has no blob sidecar subnets, since its column sidecars replace them.
        (411392, "blob_sidecar_0", "fusaka"),
        # Phase 0 has 64 attestation subnets, so subnet 64 is no topic.
        (0, "beacon_attestation_64", "phase0"),
        # A name of no topic at all.
        (0, "beacon_blocks", "phase0"),
    ],
)
def test_topic_not_at_fork(start: int, name: str, fork: str) -> None:
    digest = consensus.compute_fork_digest("mainnet", ROOT, start)
    with raises(ConsensusError, f"{name} is not a topic of {fork}") as info:
        consensus.gossip_decode_at_topic(_topic(digest, name), ROOT, snappy.compress(bytes(8)))
    assert info.value.code == 303


@pytest.mark.parametrize(
    ("topic", "message", "code"),
    [
        ("/eth1/00000000/beacon_block/ssz_snappy", "TopicError.notEth2", 201),
        ("/eth2/0000000/beacon_block/ssz_snappy", 'TopicError.forkDigest "0000000/b"', 202),
        ("/eth2/00000000/beacon_block/ssz", "TopicError.encoding", 203),
        ("/eth2/00000000/beacon/block/ssz_snappy", 'TopicError.name "beacon/block"', 204),
    ],
)
def test_malformed_topic(topic: str, message: str, code: int) -> None:
    with raises(ConsensusError, f"EthLib.Networking.Gossip.{message}") as info:
        consensus.gossip_decode_at_topic(topic, ROOT, snappy.compress(bytes(8)))
    assert info.value.code == code
