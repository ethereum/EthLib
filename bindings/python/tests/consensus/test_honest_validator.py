"""The duties of an honest validator against py_ecc signatures and the shuffle export."""

import hashlib
import struct

import pytest
from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from raising import raises

# Each state has every field zero except the slot and its validators, active from epoch 0.
# Every validator has the public key of the secret key 1.
GWEI = 10**9
FAR_FUTURE_EPOCH = 2**64 - 1
SLOTS_PER_EPOCH = 32
SECRET_KEY = (1).to_bytes(32, "big")
PUBKEY = G2ProofOfPossession.SkToPk(1)

_PHASE0_FIELDS = [
    ("genesis_time", 8),
    ("genesis_validators_root", 32),
    ("slot", 8),
    ("fork", 16),
    ("latest_block_header", 112),
    ("block_roots", 8192 * 32),
    ("state_roots", 8192 * 32),
    ("historical_roots", None),
    ("eth1_data", 72),
    ("eth1_data_votes", None),
    ("eth1_deposit_index", 8),
    ("validators", None),
    ("balances", None),
    ("randao_mixes", 65536 * 32),
    ("slashings", 8192 * 8),
    ("previous_epoch_attestations", None),
    ("current_epoch_attestations", None),
    ("justification_bits", 1),
    ("previous_justified_checkpoint", 40),
    ("current_justified_checkpoint", 40),
    ("finalized_checkpoint", 40),
]
_SYNC_COMMITTEE_SIZE = 512 * 48 + 48
_ALTAIR_FIELDS = [
    *_PHASE0_FIELDS[:15],
    ("previous_epoch_participation", None),
    ("current_epoch_participation", None),
    *_PHASE0_FIELDS[17:],
    ("inactivity_scores", None),
    ("current_sync_committee", _SYNC_COMMITTEE_SIZE),
    ("next_sync_committee", _SYNC_COMMITTEE_SIZE),
]


def _container(fields: list, values: dict) -> bytes:
    """The SSZ bytes of a container: its fixed part with an offset for each variable field."""
    fixed_size = sum(4 if size is None else size for _, size in fields)
    fixed, variable = b"", b""
    for name, size in fields:
        if size is None:
            fixed += struct.pack("<I", fixed_size + len(variable))
            variable += values.get(name, b"")
        else:
            fixed += values.get(name, bytes(size))
    return fixed + variable


def _validator() -> bytes:
    """A validator of 32 ether, active from epoch 0, that never exits: 121 bytes."""
    return (
        PUBKEY
        + bytes(32)
        + struct.pack("<Q", 32 * GWEI)
        + b"\x00"
        + struct.pack("<QQQQ", 0, 0, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH)
    )


def phase0_state(count: int, slot: int = 0) -> bytes:
    """A mainnet Phase 0 state of `count` validators at a slot."""
    return _container(
        _PHASE0_FIELDS,
        {
            "slot": struct.pack("<Q", slot),
            "validators": _validator() * count,
            "balances": struct.pack("<Q", 32 * GWEI) * count,
        },
    )


def altair_state(count: int, slot: int = 0) -> bytes:
    """A mainnet Altair state of `count` validators, the key in every seat of both committees."""
    committee = PUBKEY * 513
    return _container(
        _ALTAIR_FIELDS,
        {
            "slot": struct.pack("<Q", slot),
            "validators": _validator() * count,
            "balances": struct.pack("<Q", 32 * GWEI) * count,
            "previous_epoch_participation": bytes(count),
            "current_epoch_participation": bytes(count),
            "inactivity_scores": bytes(8 * count),
            "current_sync_committee": committee,
            "next_sync_committee": committee,
        },
    )


def _sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


# The expected signatures come from py_ecc, on signing roots computed here from the rule.
# The domain is the domain type, then the first 28 bytes of the root of the fork data.
# The signing root is the SHA-256 hash of the object's root and the domain.
def _domain(domain_type: bytes) -> bytes:
    """The domain of a state whose fork versions and genesis validators root are zero."""
    fork_data_root = _sha256(bytes(32) + bytes(32))
    return domain_type + fork_data_root[:28]


def _signature(object_root: bytes, domain_type: bytes) -> bytes:
    return G2ProofOfPossession.Sign(1, _sha256(object_root + _domain(domain_type)))


def _uint64_root(value: int) -> bytes:
    return struct.pack("<Q", value) + bytes(24)


def _block(slot: int) -> bytes:
    """A Phase 0 block at a slot with every other field zero and an empty body."""
    body_fixed = 96 + 72 + 32 + 5 * 4
    body = bytes(96 + 72 + 32) + struct.pack("<I", body_fixed) * 5
    return struct.pack("<QQ", slot, 0) + bytes(64) + struct.pack("<I", 8 + 8 + 64 + 4) + body


DOMAIN_BEACON_PROPOSER = bytes([0, 0, 0, 0])
DOMAIN_BEACON_ATTESTER = bytes([1, 0, 0, 0])
DOMAIN_RANDAO = bytes([2, 0, 0, 0])
DOMAIN_SELECTION_PROOF = bytes([5, 0, 0, 0])
DOMAIN_SYNC_COMMITTEE = bytes([7, 0, 0, 0])
DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF = bytes([8, 0, 0, 0])


def _sign(state: bytes, duty: str, obj: bytes, fork: str = "phase0") -> bytes:
    return consensus.get_validator_signature("mainnet", fork, state, duty, obj, SECRET_KEY)


def test_randao_reveal():
    # The reveal signs the epoch of the block's slot: slot 70 is in epoch 2.
    state = phase0_state(64, slot=70)
    assert _sign(state, "randao", _block(70)) == _signature(_uint64_root(2), DOMAIN_RANDAO)


def test_block_signature():
    state = phase0_state(64, slot=70)
    block = _block(70)
    root, _ = consensus.ssz_static("mainnet", "phase0", "BeaconBlock", block)
    assert _sign(state, "block", block) == _signature(root, DOMAIN_BEACON_PROPOSER)


def test_attestation_signature():
    # Slot 70, index 0, zero roots, source epoch 1 and target epoch 2.
    data = struct.pack("<QQ", 70, 0) + bytes(32) + struct.pack("<Q", 1) + bytes(32)
    data += struct.pack("<Q", 2) + bytes(32)
    root, _ = consensus.ssz_static("mainnet", "phase0", "AttestationData", data)
    state = phase0_state(64, slot=70)
    assert _sign(state, "attestation", data) == _signature(root, DOMAIN_BEACON_ATTESTER)


def test_selection_proof():
    state = phase0_state(64, slot=70)
    assert _sign(state, "slot", struct.pack("<Q", 70)) == _signature(
        _uint64_root(70), DOMAIN_SELECTION_PROOF
    )


def test_sync_committee_message():
    # The message signs the block root in the current epoch.
    state = altair_state(64, slot=70)
    root = bytes(range(32))
    assert _sign(state, "sync_committee_message", root, "altair") == _signature(
        root, DOMAIN_SYNC_COMMITTEE
    )


def test_sync_committee_selection_proof():
    # The selection data of slot 70 and subcommittee 3.
    data = struct.pack("<QQ", 70, 3)
    root = _sha256(_uint64_root(70) + _uint64_root(3))
    state = altair_state(64, slot=70)
    assert _sign(state, "sync_committee_selection_proof", data, "altair") == _signature(
        root, DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
    )


def test_unknown_duty():
    with raises(consensus.ValidatorDutyError, "unknown duty vote") as info:
        _sign(phase0_state(1), "vote", b"")
    assert info.value.code == 0


# The expected committees come from the shuffle export, which tests/consensus/shuffling pins.
def _expected_committee(count: int, epoch: int, slot: int) -> list:
    """The one committee of a slot, when an epoch of `count` validators has one per slot."""
    # The seed hashes the attester domain type, the epoch and a RANDAO mix, which is zero here.
    seed = _sha256(DOMAIN_BEACON_ATTESTER + struct.pack("<Q", epoch) + bytes(32))
    start = count * (slot % SLOTS_PER_EPOCH) // SLOTS_PER_EPOCH
    end = count * (slot % SLOTS_PER_EPOCH + 1) // SLOTS_PER_EPOCH
    return [
        consensus.compute_shuffled_index(position, count, seed) for position in range(start, end)
    ]


@pytest.mark.parametrize("epoch", [0, 1])
def test_committee_assignment(epoch: int):
    # 64 validators give one committee per slot, of two validators, in the current or next epoch.
    count = 64
    state = phase0_state(count)
    seen = set()
    for validator in range(count):
        assignment = consensus.get_committee_assignment(
            "mainnet", "phase0", state, epoch, validator
        )
        assert assignment is not None
        committee, index, slot = assignment
        assert validator in committee
        assert index == 0
        assert slot // SLOTS_PER_EPOCH == epoch
        assert committee == _expected_committee(count, epoch, slot)
        seen.add(validator)
    assert seen == set(range(count))


def test_no_assignment_for_an_unknown_validator():
    assert consensus.get_committee_assignment("mainnet", "phase0", phase0_state(64), 0, 64) is None


def test_assignment_after_the_next_epoch():
    with raises(consensus.ValidatorDutyError, "validator duty failed with code 5") as info:
        consensus.get_committee_assignment("mainnet", "phase0", phase0_state(64), 2, 0)
    assert info.value.code == 5


def test_one_proposer():
    state = phase0_state(64, slot=5)
    proposers = [v for v in range(64) if consensus.is_proposer("mainnet", "phase0", state, v)]
    assert len(proposers) == 1


def test_sync_committee_assignment():
    # Every validator has the key of every seat, so each serves in the current and the next period.
    state = altair_state(64, slot=70)
    assert consensus.is_assigned_to_sync_committee("mainnet", "altair", state, 2, 5)
    assert consensus.is_assigned_to_sync_committee("mainnet", "altair", state, 256, 5)
    # A period of 256 epochs: epoch 512 is two periods ahead.
    with raises(consensus.ValidatorDutyError, "validator duty failed with code 6") as info:
        consensus.is_assigned_to_sync_committee("mainnet", "altair", state, 512, 5)
    assert info.value.code == 6


def test_sync_committee_subnets():
    # A seat in each of the four subcommittees gives all four subnets.
    state = altair_state(64, slot=70)
    assert consensus.compute_subnets_for_sync_committee("mainnet", "altair", state, 5) == [
        0,
        1,
        2,
        3,
    ]


@pytest.mark.parametrize(
    "duty", ["sync_committee_message", "sync_committee_selection_proof", "contribution_and_proof"]
)
def test_no_sync_committee_duty_before_altair(duty: str):
    with raises(consensus.ValidatorDutyError, "no sync committee at phase0") as info:
        _sign(phase0_state(1), duty, bytes(32))
    assert info.value.code == 0


def test_no_sync_committee_before_altair():
    with raises(consensus.ValidatorDutyError, "no sync committee at phase0") as info:
        consensus.compute_subnets_for_sync_committee("mainnet", "phase0", phase0_state(1), 0)
    assert info.value.code == 0
