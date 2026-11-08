"""Weak subjectivity periods and checkpoint staleness against the consensus-specs tables."""

import struct

import pytest
from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from raising import raises

GWEI = 10**9
FAR_FUTURE_EPOCH = 2**64 - 1

# Each state has every field zero except the validators and their balances.
#
# The mainnet sizes of the fields of a Phase 0 state, or None for a field of variable size.
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


# Every validator has the public key of the secret key 1, a valid key.
PUBKEY = G2ProofOfPossession.SkToPk(1)


def _validator(effective_balance: int) -> bytes:
    """A validator active from epoch 0 that never exits: 121 bytes."""
    return (
        PUBKEY
        + bytes(32)
        + struct.pack("<Q", effective_balance)
        + b"\x00"
        + struct.pack("<QQQQ", 0, 0, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH)
    )


# The mainnet sizes of the fields of an Altair state.
# The attestations become participation flags.
# The inactivity scores and the two sync committees follow the checkpoints.
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


def _registry(count: int, effective_balance: int) -> dict:
    """The validators and the balances of `count` equal validators."""
    return {
        "validators": _validator(effective_balance) * count,
        "balances": struct.pack("<Q", effective_balance) * count,
    }


def phase0_state(count: int, effective_balance: int, slot: int = 0, roots=None) -> bytes:
    """The SSZ bytes of a mainnet Phase 0 state with `count` equal validators."""
    # `roots` maps an index of the block roots to the root that it holds.
    values = {**_registry(count, effective_balance), "slot": struct.pack("<Q", slot)}
    if roots:
        block_roots = bytearray(8192 * 32)
        for index, root in roots.items():
            block_roots[32 * index : 32 * index + 32] = root
        values["block_roots"] = bytes(block_roots)
    return _container(_PHASE0_FIELDS, values)


def altair_state(count: int, effective_balance: int) -> bytes:
    """The SSZ bytes of a mainnet Altair state with `count` equal validators."""
    # Both sync committees hold the one key of every validator.
    return _container(
        _ALTAIR_FIELDS, {**_altair_values(count), **_registry(count, effective_balance)}
    )


def _altair_values(count: int) -> dict:
    """The fields that Altair adds, for `count` validators."""
    committee = PUBKEY * 513
    return {
        "previous_epoch_participation": bytes(count),
        "current_epoch_participation": bytes(count),
        "inactivity_scores": bytes(8 * count),
        "current_sync_committee": committee,
        "next_sync_committee": committee,
    }


# The forks after Altair in their order, by their names in Lean.
_LATER_FORKS = ["bellatrix", "shapella", "dencun", "pectra", "fusaka", "glamsterdam"]


def state_at(fork: str, count: int, effective_balance: int) -> bytes:
    """The Altair state of `count` validators, upgraded up to a later fork."""
    # The upgrades keep the validators, so a later state has the same registry.
    state = altair_state(count, effective_balance)
    for later in _LATER_FORKS[: _LATER_FORKS.index(fork) + 1]:
        state = consensus.upgrade_state("mainnet", later, state, verify=False)
    return state


# The tables give the period at the mainnet preset and configuration, with a safety decay of 10.
# Every validator is active from epoch 0, with the effective balance of the row.
#
# specs/phase0/weak-subjectivity.md: average balance in ether, validator count, period.
# The rows above 262144 validators are left out: their states take minutes to build.
PHASE0_TABLE = [
    (28, 32768, 504),
    (28, 65536, 752),
    (28, 131072, 1248),
    (28, 262144, 2241),
    (32, 32768, 665),
    (32, 65536, 1075),
    (32, 131072, 1894),
    (32, 262144, 3532),
]

# specs/electra/weak-subjectivity.md: total active balance in ether, period.
ELECTRA_TABLE = [
    (1048576, 665),
    (2097152, 1075),
    (4194304, 1894),
    (8388608, 3532),
    (16777216, 3532),
    (33554432, 3532),
]

# specs/gloas/weak-subjectivity.md: total active balance in ether, period.
# The rows above 16777216 ether are left out: their states take minutes to build.
GLOAS_TABLE = [
    (1048576, 620),
    (2097152, 911),
    (4194304, 1348),
    (8388608, 1348),
    (16777216, 1484),
]

# From Electra a validator can hold up to 2048 ether, so each row needs few validators.
MAX_EFFECTIVE_BALANCE_ELECTRA = 2048


@pytest.mark.parametrize(("balance", "count", "period"), PHASE0_TABLE)
def test_phase0_table(balance: int, count: int, period: int):
    state = phase0_state(count, balance * GWEI)
    assert consensus.compute_weak_subjectivity_period("mainnet", "phase0", state) == period


@pytest.mark.parametrize(("total", "period"), ELECTRA_TABLE)
def test_electra_table(total: int, period: int):
    count = total // MAX_EFFECTIVE_BALANCE_ELECTRA
    state = state_at("pectra", count, MAX_EFFECTIVE_BALANCE_ELECTRA * GWEI)
    assert consensus.compute_weak_subjectivity_period("mainnet", "pectra", state) == period


@pytest.mark.parametrize(("total", "period"), GLOAS_TABLE)
def test_gloas_table(total: int, period: int):
    count = total // MAX_EFFECTIVE_BALANCE_ELECTRA
    state = state_at("glamsterdam", count, MAX_EFFECTIVE_BALANCE_ELECTRA * GWEI)
    assert consensus.compute_weak_subjectivity_period("mainnet", "glamsterdam", state) == period


def test_electra_bound_is_reached():
    # The proved bound at mainnet is 256 + 10 * 65536 * (128 + 1) / (200 * 128) = 3558 epochs.
    # A total of 65536 * 129 ether less 1 Gwei has a share of 129 ether less 1 Gwei per epoch.
    # Rounded down to whole ether, the churn is 128 ether.
    # So the epochs are 10 * (65536 * 129 * 10^9 - 1) // (200 * 128 * 10^9) = 3302, by hand.
    full = MAX_EFFECTIVE_BALANCE_ELECTRA * GWEI
    count = 65536 * 129 // MAX_EFFECTIVE_BALANCE_ELECTRA
    registry = _registry(count, full)
    # The last validator holds 1 Gwei less, so the total is 65536 * 129 ether less 1 Gwei.
    last = _validator(full - 1)
    registry["validators"] = registry["validators"][:-121] + last
    state = _container(_ALTAIR_FIELDS, {**_altair_values(count), **registry})
    for later in _LATER_FORKS[: _LATER_FORKS.index("pectra") + 1]:
        state = consensus.upgrade_state("mainnet", later, state, verify=False)
    assert consensus.compute_weak_subjectivity_period("mainnet", "pectra", state) == 3558


def test_gloas_bound_is_reached():
    # The proved bound at mainnet is 1658 epochs, from the 64-bit cap 10 * t < 2^64.
    # The validators hold 1406271487 ether in all, so 10 * t is below 2^64 Gwei.
    # The exit churn is 42915 ether, the activation churn 256 and the consolidation churn 21457.
    # So the weighted churn is 50152333333333 Gwei, and 10 * t // (200 * churn) = 1402, by hand.
    full = MAX_EFFECTIVE_BALANCE_ELECTRA * GWEI
    count = 512
    state = state_at("glamsterdam", count, full)
    # The upgrades need a registry and overflow on such a total, so one validator takes it after.
    record = PUBKEY + bytes(32) + struct.pack("<Q", full)
    assert state.count(record) == count
    rest = 1406271487 - (count - 1) * MAX_EFFECTIVE_BALANCE_ELECTRA
    state = state.replace(record, PUBKEY + bytes(32) + struct.pack("<Q", rest * GWEI), 1)
    assert consensus.compute_weak_subjectivity_period("mainnet", "glamsterdam", state) == 1658


def test_no_active_validators():
    # The average balance divides by the number of active validators.
    with raises(
        consensus.WeakSubjectivityError,
        "EthLib.Consensus.WeakSubjectivityError.arith (EthLib.Base.ArithError.divisionByZero)",
    ) as info:
        consensus.compute_weak_subjectivity_period("mainnet", "phase0", phase0_state(0, 0))
    assert info.value.code == 3


# One checkpoint at epoch 10: its state is at the second slot of the epoch.
# The state holds the root of the checkpoint at the first slot of the epoch.
EPOCH = 10
ROOT = bytes(range(1, 33))
SLOT_DURATION_MS = 12000


def _checkpoint(epoch: int, root: bytes) -> bytes:
    return struct.pack("<Q", epoch) + root


def _ws_state() -> bytes:
    return phase0_state(32768, 32 * GWEI, slot=32 * EPOCH + 1, roots={32 * EPOCH: ROOT})


def _is_within(state: bytes, checkpoint: bytes, epoch: int) -> bool:
    """The check at the start of an epoch, with genesis at time 0."""
    return consensus.is_within_weak_subjectivity_period(
        "mainnet", "phase0", state, checkpoint, 0, 32 * epoch * SLOT_DURATION_MS
    )


def test_within_until_the_end_of_the_period():
    # 32768 validators of 32 ether have a period of 665 epochs.
    state = _ws_state()
    checkpoint = _checkpoint(EPOCH, ROOT)
    assert _is_within(state, checkpoint, EPOCH)
    assert _is_within(state, checkpoint, EPOCH + 665)
    assert not _is_within(state, checkpoint, EPOCH + 666)


def test_state_without_the_root_of_the_checkpoint():
    with raises(
        consensus.WeakSubjectivityError, "EthLib.Consensus.WeakSubjectivityError.blockRootMismatch"
    ) as info:
        _is_within(_ws_state(), _checkpoint(EPOCH, bytes(32)), EPOCH)
    assert info.value.code == 4


def test_state_at_another_epoch():
    # The state holds the root at the first slot of epoch 10, but the checkpoint names epoch 9.
    state = phase0_state(32768, 32 * GWEI, slot=32 * EPOCH + 1, roots={32 * (EPOCH - 1): ROOT})
    with raises(
        consensus.WeakSubjectivityError,
        "EthLib.Consensus.WeakSubjectivityError.epochMismatch 9 10",
    ) as info:
        _is_within(state, _checkpoint(EPOCH - 1, ROOT), EPOCH)
    assert info.value.code == 5


def test_time_out_of_range():
    message = f"expected an int below {2**64}, got {2**64}"
    with raises(consensus.WeakSubjectivityError, message) as info:
        consensus.is_within_weak_subjectivity_period("minimal", "phase0", b"", b"", 2**64, 0)
    assert info.value.code == 0
