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
        assert slot // SLOTS_PER_EPOCH == epoch
        assert assignment == (_expected_committee(count, epoch, slot), 0, slot)
        seen.add(validator)
    assert seen == set(range(count))


def test_no_assignment_for_an_unknown_validator():
    assert consensus.get_committee_assignment("mainnet", "phase0", phase0_state(64), 0, 64) is None


def test_assignment_after_the_next_epoch():
    with raises(consensus.ValidatorDutyError, "validator duty failed with code 5") as info:
        consensus.get_committee_assignment("mainnet", "phase0", phase0_state(64), 2, 0)
    assert info.value.code == 5


# The last epoch that the guide accepts.
# In the epoch after it, the first slot plus the length of an epoch is 2^64.
# There the guide's 64-bit sum overflows.
LAST_EPOCH = 2**64 // SLOTS_PER_EPOCH - 2


def test_assignment_in_the_last_epoch():
    # A state in the last epoch, so that the next epoch is in range.
    state = phase0_state(64, slot=LAST_EPOCH * SLOTS_PER_EPOCH)
    assignment = consensus.get_committee_assignment("mainnet", "phase0", state, LAST_EPOCH, 0)
    assert assignment is not None
    assert assignment[2] // SLOTS_PER_EPOCH == LAST_EPOCH


def test_no_assignment_in_the_epoch_whose_slots_overflow():
    state = phase0_state(64, slot=LAST_EPOCH * SLOTS_PER_EPOCH)
    with raises(consensus.ValidatorDutyError, "validator duty failed with code 4") as info:
        consensus.get_committee_assignment("mainnet", "phase0", state, LAST_EPOCH + 1, 0)
    assert info.value.code == 4


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


# ---- Gloas ----------------------------------------------------------------------------------

# Mainnet does not schedule Gloas yet, so the tests start it at epoch 0.
GLOAS = {"GLOAS_FORK_EPOCH": "0"}
GLOAS_FORK_VERSION = bytes([7, 0, 0, 0])
DOMAIN_PTC_ATTESTER = bytes([12, 0, 0, 0])
MIN_SEED_LOOKAHEAD = 1
PTC_SIZE = 512


def gloas_state(count: int, slot: int) -> bytes:
    """An Altair state of `count` validators at a slot, upgraded fork by fork to Gloas."""
    state = altair_state(count, slot)
    for fork in ["bellatrix", "shapella", "dencun", "pectra", "fusaka", "glamsterdam"]:
        state = consensus.upgrade_state("mainnet", fork, state, verify=False, config=GLOAS)
    return state


def _fixed_end(state: bytes) -> int:
    """Where the fixed part of a state ends: the first offset, that of the historical roots."""
    return struct.unpack_from("<I", state, 8 + 32 + 8 + 16 + 112 + 2 * 8192 * 32)[0]


# The window of payload committees is the last field of a Gloas state, of a fixed size.
WINDOW_SIZE = (MIN_SEED_LOOKAHEAD + 2) * SLOTS_PER_EPOCH * PTC_SIZE * 8
# Between the lookahead of proposers and the window sit these fields:
# - the offset of the builders
# - the next builder index
# - the availability bits of 8192 slots
# - the 64 pending payments of 52 bytes
# - the offsets of the pending withdrawals, the latest bid and the expected withdrawals
BETWEEN = 4 + 8 + 8192 // 8 + 2 * SLOTS_PER_EPOCH * 52 + 3 * 4
LOOKAHEAD_SIZE = (MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH * 8


def ptc_window(state: bytes) -> list:
    """The payload committees of a Gloas state, for the previous, current and next epochs."""
    start = _fixed_end(state) - WINDOW_SIZE
    return [
        list(struct.unpack_from(f"<{PTC_SIZE}Q", state, start + i * PTC_SIZE * 8))
        for i in range((MIN_SEED_LOOKAHEAD + 2) * SLOTS_PER_EPOCH)
    ]


def proposer_lookahead(state: bytes) -> list:
    """The proposers of a Gloas state, from the start of its current epoch."""
    start = _fixed_end(state) - WINDOW_SIZE - BETWEEN - LOOKAHEAD_SIZE
    return list(struct.unpack_from(f"<{LOOKAHEAD_SIZE // 8}Q", state, start))


# A state in epoch 1, whose window holds the committees of epochs 0, 1 and 2.
GLOAS_SLOT = 40


@pytest.fixture(scope="module")
def gloas() -> bytes:
    return gloas_state(64, GLOAS_SLOT)


@pytest.mark.parametrize("epoch", [1, 2])
def test_ptc_assignment(gloas: bytes, epoch: int):
    # The guide takes the first slot of the epoch whose committee holds the validator.
    window = ptc_window(gloas)
    current = GLOAS_SLOT // SLOTS_PER_EPOCH
    slots = range(epoch * SLOTS_PER_EPOCH, (epoch + 1) * SLOTS_PER_EPOCH)
    for validator in range(64):
        expected = next(
            (
                slot
                for slot in slots
                if validator in window[(epoch - current + 1) * SLOTS_PER_EPOCH + slot % 32]
            ),
            None,
        )
        got = consensus.get_ptc_assignment(
            "mainnet", "glamsterdam", gloas, epoch, validator, config=GLOAS
        )
        assert got == expected


def test_ptc_assignment_after_the_lookahead(gloas: bytes):
    with raises(consensus.ValidatorDutyError, "validator duty failed with code 5") as info:
        consensus.get_ptc_assignment("mainnet", "glamsterdam", gloas, 3, 0, config=GLOAS)
    assert info.value.code == 5


def test_no_ptc_assignment_before_gloas():
    with raises(consensus.ValidatorDutyError, "no payload timeliness committee at fusaka") as info:
        consensus.get_ptc_assignment("mainnet", "fusaka", b"", 0, 0)
    assert info.value.code == 0


def test_upcoming_proposal_slots(gloas: bytes):
    lookahead = proposer_lookahead(gloas)
    # The proposer of the slot of the state, as the transition reads it, checks the layout.
    epoch_start = GLOAS_SLOT // SLOTS_PER_EPOCH * SLOTS_PER_EPOCH
    proposer = lookahead[GLOAS_SLOT - epoch_start]
    assert consensus.is_proposer("mainnet", "glamsterdam", gloas, proposer, GLOAS)
    for validator in range(64):
        # The guide keeps the slots of the lookahead after the slot of the state.
        expected = [
            epoch_start + offset
            for offset, chosen in enumerate(lookahead)
            if epoch_start + offset > GLOAS_SLOT and chosen == validator
        ]
        got = consensus.get_upcoming_proposal_slots(
            "mainnet", "glamsterdam", gloas, validator, config=GLOAS
        )
        assert got == expected


def test_no_upcoming_proposal_slots_before_gloas():
    with raises(consensus.ValidatorDutyError, "no payload timeliness committee at fusaka") as info:
        consensus.get_upcoming_proposal_slots("mainnet", "fusaka", b"", 0)
    assert info.value.code == 0


def _payload_attestation_data(slot: int) -> bytes:
    return bytes([9]) * 32 + struct.pack("<Q", slot) + b"\x01\x00"


def test_payload_attestation_message_signature(gloas: bytes):
    # The message is the validator index, the data and a signature; only the data is signed.
    data = _payload_attestation_data(GLOAS_SLOT)
    message = struct.pack("<Q", 3) + data + bytes(96)
    chunks = [bytes([9]) * 32, _uint64_root(GLOAS_SLOT), b"\x01" + bytes(31), bytes(32)]
    data_root = _sha256(_sha256(chunks[0] + chunks[1]) + _sha256(chunks[2] + chunks[3]))
    # The upgrade sets the fork of the state to Gloas, from the epoch of the state.
    fork_data_root = _sha256(GLOAS_FORK_VERSION + bytes(28) + bytes(32))
    domain = DOMAIN_PTC_ATTESTER + fork_data_root[:28]
    expected = G2ProofOfPossession.Sign(1, _sha256(data_root + domain))
    got = consensus.get_validator_signature(
        "mainnet", "glamsterdam", gloas, "payload_attestation_message", message, SECRET_KEY, GLOAS
    )
    assert got == expected


def test_no_payload_attestation_message_before_gloas():
    message = struct.pack("<Q", 3) + _payload_attestation_data(0) + bytes(96)
    with raises(consensus.ValidatorDutyError, "no payload timeliness committee at phase0") as info:
        _sign(phase0_state(1), "payload_attestation_message", message)
    assert info.value.code == 0


DOMAIN_PROPOSER_PREFERENCES = bytes([13, 0, 0, 0])
GAS_LIMIT = 60_000_000


def _proposer_preferences(slot: int) -> bytes:
    """Preferences of validator 3 for a slot, with bytes 9 as root and bytes 5 as fee recipient."""
    fields = struct.pack("<QQ", slot, 3) + bytes([5]) * 20 + struct.pack("<Q", GAS_LIMIT)
    return bytes([9]) * 32 + fields


def _proposer_preferences_root(slot: int) -> bytes:
    """The root of the preferences: five chunks, padded with zero chunks to eight."""
    chunks = [
        bytes([9]) * 32,
        _uint64_root(slot),
        _uint64_root(3),
        bytes([5]) * 20 + bytes(12),
        _uint64_root(GAS_LIMIT),
        bytes(32),
        bytes(32),
        bytes(32),
    ]
    while len(chunks) > 1:
        chunks = [_sha256(chunks[i] + chunks[i + 1]) for i in range(0, len(chunks), 2)]
    return chunks[0]


def test_proposer_preferences_signature():
    # The fork version of the proposal epoch is the genesis version on mainnet at epoch 0.
    expected = _signature(_proposer_preferences_root(5), DOMAIN_PROPOSER_PREFERENCES)
    assert _sign(phase0_state(1), "proposer_preferences", _proposer_preferences(5)) == expected


def test_proposer_preferences_signature_in_the_epoch_before_gloas():
    # A Fulu state signs preferences for the first slot of Gloas at the Gloas fork version.
    config = {"GLOAS_FORK_EPOCH": "1"}
    state = altair_state(1)
    for fork in ["bellatrix", "shapella", "dencun", "pectra", "fusaka"]:
        state = consensus.upgrade_state("mainnet", fork, state, verify=False, config=config)
    fork_data_root = _sha256(GLOAS_FORK_VERSION + bytes(28) + bytes(32))
    domain = DOMAIN_PROPOSER_PREFERENCES + fork_data_root[:28]
    root = _proposer_preferences_root(SLOTS_PER_EPOCH)
    expected = G2ProofOfPossession.Sign(1, _sha256(root + domain))
    got = consensus.get_validator_signature(
        "mainnet",
        "fusaka",
        state,
        "proposer_preferences",
        _proposer_preferences(SLOTS_PER_EPOCH),
        SECRET_KEY,
        config,
    )
    assert got == expected


@pytest.mark.parametrize(
    "index, error, message",
    [
        (True, consensus.ValidatorDutyError, "expected an int"),
        (2**64, consensus.ValidatorDutyError, f"expected an int below {2**64}, got {2**64}"),
        (-1, ValueError, "cannot pass a negative int to Lean"),
    ],
)
def test_validator_index_is_read_as_an_int(index, error, message):
    with raises(error, message):
        consensus.is_proposer("mainnet", "phase0", phase0_state(64), index)


def test_duty_must_be_text():
    with raises(consensus.ValidatorDutyError, "expected a str") as info:
        consensus.get_validator_signature(
            "mainnet",
            "phase0",
            phase0_state(64),
            b"randao",  # ty: ignore[invalid-argument-type]
            b"",
            bytes(32),
        )
    assert info.value.code == 0


def test_configuration_must_be_a_dict():
    with raises(consensus.ValidatorDutyError, "configuration: expected a dict") as info:
        consensus.is_proposer("mainnet", "phase0", phase0_state(64), 0, [])  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0
