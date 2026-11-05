"""The gossip topics of each fork and the subnets of messages, against the rules restated here."""

import hashlib
import random

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError
from raising import raises

PHASE0 = [
    "beacon_block",
    "beacon_aggregate_and_proof",
    *[f"beacon_attestation_{i}" for i in range(64)],
    "voluntary_exit",
    "proposer_slashing",
    "attester_slashing",
]
ALTAIR = [
    "sync_committee_contribution_and_proof",
    *[f"sync_committee_{i}" for i in range(4)],
    "light_client_finality_update",
    "light_client_optimistic_update",
]
CAPELLA = ["bls_to_execution_change"]
GLOAS = [
    "execution_payload_bid",
    "execution_payload",
    "payload_attestation_message",
    "proposer_preferences",
]


def _blobs(count: int) -> list:
    return [f"blob_sidecar_{i}" for i in range(count)]


EXPECTED = {
    "phase0": PHASE0,
    "altair": PHASE0 + ALTAIR,
    "bellatrix": PHASE0 + ALTAIR,
    "shapella": PHASE0 + ALTAIR + CAPELLA,
    "dencun": PHASE0 + ALTAIR + CAPELLA + _blobs(6),
    "pectra": PHASE0 + ALTAIR + CAPELLA + _blobs(9),
    "fusaka": PHASE0 + ALTAIR + CAPELLA + [f"data_column_sidecar_{i}" for i in range(128)],
}
EXPECTED["glamsterdam"] = EXPECTED["fusaka"] + GLOAS


@pytest.mark.parametrize("name", ["mainnet", "minimal"])
@pytest.mark.parametrize("fork", sorted(EXPECTED))
def test_topics(fork: str, name: str) -> None:
    assert consensus.gossip_topics(fork, name) == EXPECTED[fork]


@pytest.mark.parametrize(
    "fork, like",
    [("london", "phase0"), *[(f"bpo{i}", "fusaka") for i in range(1, 6)]],
)
def test_topics_of_forks_without_a_consensus_change(fork: str, like: str) -> None:
    assert consensus.gossip_topics(fork) == EXPECTED[like]


def test_topics_not_yet_specified() -> None:
    with raises(ConsensusError, "the gossip topics of hegota are not yet specified"):
        consensus.gossip_topics("hegota")


def _attestation_subnet(committees_per_slot: int, slot: int, committee_index: int) -> int:
    slots_since_epoch_start = slot % 32
    return (committees_per_slot * slots_since_epoch_start + committee_index) % 64


def test_subnet_for_attestation() -> None:
    rng = random.Random(7)
    for _ in range(200):
        committees, slot, index = rng.randrange(1, 65), rng.randrange(2**40), rng.randrange(64)
        expected = _attestation_subnet(committees, slot, index)
        assert consensus.compute_subnet_for_attestation(committees, slot, index) == expected


def test_subnet_for_attestation_overflow() -> None:
    with raises(
        ConsensusError, "subnet rejected: EthLib.Networking.Gossip.SubnetError.subnetOverflow"
    ) as caught:
        consensus.compute_subnet_for_attestation(2**63, 2, 0)
    assert caught.value.code == 105


@pytest.mark.parametrize("fork, count", [("dencun", 6), ("pectra", 9)])
def test_subnet_for_blob_sidecar(fork: str, count: int) -> None:
    for index in range(20):
        assert consensus.compute_subnet_for_blob_sidecar(fork, index) == index % count


@pytest.mark.parametrize("fork", ["shapella", "fusaka"])
def test_no_blob_sidecar_subnet(fork: str) -> None:
    with raises(
        ConsensusError, "subnet rejected: EthLib.Networking.Gossip.SubnetError.zeroSubnetCount"
    ) as caught:
        consensus.compute_subnet_for_blob_sidecar(fork, 0)
    assert caught.value.code == 101


def test_subnet_for_data_column_sidecar() -> None:
    for index in (0, 1, 127, 128, 129, 2**64 - 1):
        assert consensus.compute_subnet_for_data_column_sidecar(index) == index % 128


def _subscribed(node_id: int, epoch: int, name: str) -> list:
    # Mainnet and minimal share these values.
    epochs_per_subscription, subnets_per_node, count, prefix_bits = 256, 2, 64, 6
    node_prefix = node_id >> (256 - prefix_bits)
    node_offset = node_id % epochs_per_subscription
    period = (epoch + node_offset) // epochs_per_subscription
    seed = hashlib.sha256(period.to_bytes(8, "little")).digest()
    permuted = consensus.compute_shuffled_index(node_prefix, 1 << prefix_bits, seed, name)
    return [(permuted + index) % count for index in range(subnets_per_node)]


@pytest.mark.parametrize("name", ["mainnet", "minimal"])
def test_subscribed_subnets(name: str) -> None:
    rng = random.Random(11)
    for _ in range(50):
        node_id, epoch = rng.randrange(2**256), rng.randrange(2**40)
        expected = _subscribed(node_id, epoch, name)
        assert consensus.compute_subscribed_subnets(node_id, epoch, name) == expected


def test_subscribed_subnets_epoch_overflow() -> None:
    with raises(
        ConsensusError, "subnet rejected: EthLib.Networking.Gossip.SubnetError.epochOverflow"
    ) as caught:
        consensus.compute_subscribed_subnets(255, 2**64 - 1)
    assert caught.value.code == 103
