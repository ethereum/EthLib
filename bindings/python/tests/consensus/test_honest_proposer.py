"""What an honest proposer computes, against values worked out in the test from the guide."""

import struct
from pathlib import Path
from typing import cast

import pytest
from eth_typing import BLSSignature
from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from ethlib.errors import ProposerError
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

GWEI = 10**9
FAR_FUTURE_EPOCH = 2**64 - 1
UNSET_DEPOSIT_REQUESTS_START_INDEX = 2**64 - 1

# The mainnet values that the Eth1 vote reads.
SECONDS_PER_SLOT = 12
SLOTS_PER_ETH1_VOTING_PERIOD = 64 * 32
FOLLOW_TIME = 14 * 2048

# Each state has every field zero except those that a test sets.
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

# The forks after Phase 0 in their order, by their names in Lean.
_LATER_FORKS = ["altair", "bellatrix", "shapella", "dencun", "pectra", "fusaka", "glamsterdam"]

PUBKEY = G2ProofOfPossession.SkToPk(1)

# Enough validators for the committees that the upgrade to Gloas draws.
ONE_COMMITTEE = [32 * GWEI] * 64


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


def _validator(effective_balance: int) -> bytes:
    """A validator active from epoch 0 that never exits: 121 bytes."""
    return (
        PUBKEY
        + bytes(32)
        + struct.pack("<Q", effective_balance)
        + b"\x00"
        + struct.pack("<QQQQ", 0, 0, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH)
    )


def eth1_data(deposit_count: int, tag: int) -> bytes:
    """Eth1 data with a deposit count, whose root and block hash repeat one byte: 72 bytes."""
    return bytes([tag]) * 32 + struct.pack("<Q", deposit_count) + bytes([tag]) * 32


def state_at(fork: str, balances: list, **values) -> bytes:
    """A mainnet state at a fork, upgraded from Phase 0, with validators of these balances."""
    fields = {
        "validators": b"".join(_validator(b) for b in balances),
        "balances": b"".join(struct.pack("<Q", b) for b in balances),
    }
    for name in ("genesis_time", "slot", "eth1_deposit_index"):
        if name in values:
            fields[name] = struct.pack("<Q", values[name])
    if "eth1_data" in values:
        fields["eth1_data"] = values["eth1_data"]
    if "votes" in values:
        fields["eth1_data_votes"] = b"".join(values["votes"])
    state = _container(_PHASE0_FIELDS, fields)
    # The upgrades keep the Eth1 data, the votes, the deposit index and the registry.
    for later in _LATER_FORKS[: _LATER_FORKS.index(fork) + 1] if fork != "phase0" else []:
        state = consensus.upgrade_state("mainnet", later, state, verify=False)
    return state


# ---- The Eth1 vote --------------------------------------------------------------------------


def expected_vote(state_eth1: bytes, votes: list, chain: list, period_start: int) -> bytes:
    """The vote of the guide, worked out here: the most voted candidate, or the default."""

    def count(data: bytes) -> int:
        return struct.unpack("<Q", data[32:40])[0]

    candidates = [
        data
        for timestamp, data in chain
        if timestamp + FOLLOW_TIME <= period_start <= timestamp + 2 * FOLLOW_TIME
        and count(data) >= count(state_eth1)
    ]
    valid = [vote for vote in votes if vote in candidates]
    if not valid:
        return candidates[-1] if candidates else state_eth1
    return max(valid, key=lambda v: (valid.count(v), -valid.index(v)))


GENESIS_TIME = 1_600_000_000
# A slot in the third voting period, so that the period starts at slot 4096.
SLOT = 2 * SLOTS_PER_ETH1_VOTING_PERIOD + 5
PERIOD_START = GENESIS_TIME + 2 * SLOTS_PER_ETH1_VOTING_PERIOD * SECONDS_PER_SLOT


def _chain(offsets: list) -> list:
    """Eth1 blocks at some times before the start of the period, with distinct data."""
    return [(PERIOD_START - offset, eth1_data(10 + i, 1 + i)) for i, offset in enumerate(offsets)]


# The candidates lie between one and two follow distances before the start of the period.
CHAIN = _chain([3 * FOLLOW_TIME, 2 * FOLLOW_TIME, FOLLOW_TIME + 7, FOLLOW_TIME, FOLLOW_TIME - 1])


@pytest.mark.parametrize("fork", ["phase0", "altair", "pectra", "glamsterdam"])
@pytest.mark.parametrize(
    "votes",
    [
        [],
        [CHAIN[2][1]],
        [CHAIN[1][1], CHAIN[2][1], CHAIN[2][1]],
        [CHAIN[2][1], CHAIN[1][1]],
        [CHAIN[0][1], CHAIN[4][1]],
    ],
)
def test_eth1_vote(fork: str, votes: list):
    state_eth1 = eth1_data(5, 0xEE)
    state = state_at(
        fork, ONE_COMMITTEE, genesis_time=GENESIS_TIME, slot=SLOT, eth1_data=state_eth1, votes=votes
    )
    vote = consensus.get_eth1_vote("mainnet", fork, state, CHAIN)
    assert vote == expected_vote(state_eth1, votes, CHAIN, PERIOD_START)


def test_eth1_vote_never_moves_the_deposit_count_back():
    # The state holds 11 deposits, so only the candidates with as many count.
    state_eth1 = eth1_data(11, 0xEE)
    state = state_at(
        "phase0", ONE_COMMITTEE, genesis_time=GENESIS_TIME, slot=SLOT, eth1_data=state_eth1
    )
    vote = consensus.get_eth1_vote(
        "mainnet", "phase0", state, CHAIN[:2] + [(CHAIN[2][0], eth1_data(4, 9))]
    )
    assert vote == CHAIN[1][1]


def test_eth1_vote_without_a_candidate_is_the_state_data():
    state_eth1 = eth1_data(5, 0xEE)
    state = state_at(
        "phase0", ONE_COMMITTEE, genesis_time=GENESIS_TIME, slot=SLOT, eth1_data=state_eth1
    )
    assert consensus.get_eth1_vote("mainnet", "phase0", state, [CHAIN[0], CHAIN[4]]) == state_eth1


def test_eth1_vote_once_the_deposits_are_in():
    # The upgrade to Electra sets the start index of the deposit requests to the unset value.
    state_eth1 = eth1_data(5, 0xEE)
    state = state_at(
        "pectra",
        ONE_COMMITTEE,
        genesis_time=GENESIS_TIME,
        slot=SLOT,
        eth1_data=state_eth1,
        eth1_deposit_index=UNSET_DEPOSIT_REQUESTS_START_INDEX,
    )
    assert consensus.get_eth1_vote("mainnet", "pectra", state, CHAIN) == state_eth1


def test_eth1_vote_overflow():
    state = state_at("phase0", ONE_COMMITTEE, genesis_time=GENESIS_TIME, slot=SLOT)
    with raises(ProposerError, "proposer step failed with code 1"):
        consensus.get_eth1_vote("mainnet", "phase0", state, [(2**64 - 1, eth1_data(1, 1))])


def test_no_eth1_vote_at_heze():
    with raises(ProposerError, "no Eth1 vote at hegota"):
        consensus.get_eth1_vote("mainnet", "hegota", b"", [])


# ---- Pending deposits ------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("deposit_count", "deposit_index", "expected"),
    [(0, 0, 0), (5, 0, 5), (40, 3, 16), (5, 5, 0), (5, 7, 0)],
)
def test_eth1_pending_deposit_count(deposit_count: int, deposit_index: int, expected: int):
    # The start index of the deposit requests is unset, so the deposit count is the limit.
    # The guide counts at most MAX_DEPOSITS = 16 of them.
    state = state_at(
        "pectra",
        ONE_COMMITTEE,
        eth1_data=eth1_data(deposit_count, 1),
        eth1_deposit_index=deposit_index,
    )
    assert consensus.get_eth1_pending_deposit_count("mainnet", "pectra", state) == expected


@pytest.mark.parametrize("fork", ["dencun", "fusaka"])
def test_no_pending_deposit_count_outside_electra(fork: str):
    with raises(ProposerError, f"no pending deposit count at {fork}"):
        consensus.get_eth1_pending_deposit_count("mainnet", fork, b"")


# ---- Custody -----------------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("balances", "indices"),
    [
        ([32 * GWEI] * 4, []),
        ([32 * GWEI] * 4, [0, 1, 2, 3]),
        ([2048 * GWEI] * 4, [0, 1]),
        ([2048 * GWEI] * 4, [0, 1, 2, 3]),
        ([2048 * GWEI, 32 * GWEI], [0, 0, 1]),
    ],
)
def test_validators_custody_requirement(balances: list, indices: list):
    state = state_at("fusaka", balances)
    # The guide: one group per 32 ether of effective balance, at least 8 and at most 128.
    total = sum(balances[index] for index in indices)
    expected = min(max(total // (32 * GWEI), 8), 128)
    got = consensus.get_validators_custody_requirement("mainnet", "fusaka", state, indices)
    assert got == expected


def test_custody_of_an_unknown_validator():
    state = state_at("fusaka", [32 * GWEI])
    with raises(ProposerError, "proposer step failed with code 2"):
        consensus.get_validators_custody_requirement("mainnet", "fusaka", state, [1])


# ---- Execution requests ------------------------------------------------------------------------

DEPOSIT = (
    bytes(range(48)) + bytes(32) + struct.pack("<Q", 32 * GWEI) + bytes(96) + struct.pack("<Q", 7)
)
WITHDRAWAL = bytes(20) + bytes([1]) * 48 + struct.pack("<Q", 0)
CONSOLIDATION = bytes(20) + bytes([2]) * 48 + bytes([3]) * 48


def requests_bytes(lists: list) -> bytes:
    """The SSZ bytes of execution requests: one offset per list, then the lists in turn."""
    fields = [(str(index), None) for index in range(len(lists))]
    return _container(fields, {str(index): data for index, data in enumerate(lists)})


@pytest.mark.parametrize(
    ("entries", "lists"),
    [
        ([], [b"", b"", b""]),
        ([b"\x00" + DEPOSIT], [DEPOSIT, b"", b""]),
        ([b"\x01" + WITHDRAWAL * 2], [b"", WITHDRAWAL * 2, b""]),
        (
            [b"\x00" + DEPOSIT, b"\x01" + WITHDRAWAL, b"\x02" + CONSOLIDATION],
            [DEPOSIT, WITHDRAWAL, CONSOLIDATION],
        ),
        ([b"\x00" + DEPOSIT, b"\x02" + CONSOLIDATION], [DEPOSIT, b"", CONSOLIDATION]),
    ],
)
def test_execution_requests(entries: list, lists: list):
    got = consensus.get_execution_requests("mainnet", "pectra", entries)
    assert got == requests_bytes(lists)


@pytest.mark.parametrize(
    ("entries", "message"),
    [
        ([b""], "proposer step failed with code 9"),
        ([b"\x03" + DEPOSIT], "proposer step failed with code 9"),
        ([b"\x00"], "proposer step failed with code 10"),
        ([b"\x01" + WITHDRAWAL, b"\x00" + DEPOSIT], "proposer step failed with code 11"),
        ([b"\x00" + DEPOSIT, b"\x00" + DEPOSIT], "proposer step failed with code 11"),
        ([b"\x00" + DEPOSIT[:-1]], "proposer step failed with code 3"),
    ],
)
def test_execution_requests_rejected(entries: list, message: str):
    with raises(ProposerError, message):
        consensus.get_execution_requests("mainnet", "pectra", entries)


# ---- The on-chain aggregate ---------------------------------------------------------------------

# The mainnet attestation of Electra: its aggregation bits, its data and its signature.
# Then one bit for each of the 64 committees of a slot.
DATA = struct.pack("<QQ", 9, 0) + bytes([7]) * 32 + struct.pack("<Q", 0) + bytes(32)
DATA += struct.pack("<Q", 1) + bytes([8]) * 32


def bitlist(bits: list) -> bytes:
    """The SSZ bytes of a bitlist: the bits from the lowest, then a closing bit."""
    value = sum(1 << i for i, bit in enumerate(bits) if bit) | (1 << len(bits))
    return value.to_bytes(len(bits) // 8 + 1, "little")


def committee_bits(committees: list) -> bytes:
    return sum(1 << c for c in committees).to_bytes(8, "little")


def attestation(bits: list, signature: bytes, committees: list) -> bytes:
    fixed = 4 + len(DATA) + 96 + 8
    return struct.pack("<I", fixed) + DATA + signature + committee_bits(committees) + bitlist(bits)


def signature(key: int) -> bytes:
    return G2ProofOfPossession.Sign(key, b"vote")


def aggregate_signatures(signatures: list) -> bytes:
    """The aggregate of py_ecc, which types its signatures as BLSSignature."""
    return G2ProofOfPossession.Aggregate(cast(list[BLSSignature], signatures))


@pytest.mark.parametrize("fork", ["pectra", "fusaka", "glamsterdam"])
def test_on_chain_aggregate(fork: str):
    # Three network aggregates, of the committees 5, 2 and 9, given out of order.
    aggregates = [
        ([True, False, True], signature(1), [5]),
        ([False, True], signature(2), [2]),
        ([True], signature(3), [9]),
    ]
    got = consensus.compute_on_chain_aggregate(
        "mainnet", fork, [attestation(*aggregate) for aggregate in aggregates]
    )
    # The guide sorts them by committee, joins their bits and aggregates their signatures.
    ordered = sorted(aggregates, key=lambda a: a[2][0])
    bits = [bit for aggregate in ordered for bit in aggregate[0]]
    joined = aggregate_signatures([aggregate[1] for aggregate in ordered])
    assert got == attestation(bits, joined, [2, 5, 9])


def test_on_chain_aggregate_reads_the_first_committee():
    # An aggregate that sets two committee bits counts for the first one.
    aggregates = [([True], signature(1), [4, 1]), ([False], signature(2), [3])]
    got = consensus.compute_on_chain_aggregate(
        "mainnet", "pectra", [attestation(*aggregate) for aggregate in aggregates]
    )
    joined = aggregate_signatures([signature(1), signature(2)])
    assert got == attestation([True, False], joined, [1, 3])


@pytest.mark.parametrize(
    ("aggregates", "message"),
    [
        ([], "proposer step failed with code 6"),
        ([attestation([True], signature(1), [])], "proposer step failed with code 7"),
        ([attestation([True], bytes(96), [1])], "proposer step failed with code 4"),
    ],
)
def test_on_chain_aggregate_rejected(aggregates: list, message: str):
    with raises(ProposerError, message):
        consensus.compute_on_chain_aggregate("mainnet", "pectra", aggregates)


def test_no_on_chain_aggregate_before_electra():
    with raises(ProposerError, "no on-chain aggregate at dencun"):
        consensus.compute_on_chain_aggregate("mainnet", "dencun", [])


# ---- The sync aggregate --------------------------------------------------------------------------

SYNC_SUBCOMMITTEE_SIZE = 512 // 4


def contribution(subcommittee: int, seats: list, signature: bytes) -> bytes:
    """A contribution of slot 70 and a zero root, with the bits of some seats."""
    bits = sum(1 << seat for seat in seats).to_bytes(SYNC_SUBCOMMITTEE_SIZE // 8, "little")
    return struct.pack("<Q", 70) + bytes(32) + struct.pack("<Q", subcommittee) + bits + signature


def test_sync_aggregate():
    # Seat 0 and seat 127 of subcommittee 2, and seat 5 of subcommittee 0.
    contributions = [(2, [0, 127], signature(1)), (0, [5], signature(2))]
    got = consensus.process_sync_committee_contributions(
        "mainnet", "altair", [contribution(*c) for c in contributions]
    )
    # Seat j of subcommittee i is seat 128 * i + j of the committee.
    bits = sum(1 << (128 * 2 + j) for j in [0, 127]) | (1 << 5)
    joined = aggregate_signatures([signature(1), signature(2)])
    assert got == bits.to_bytes(64, "little") + joined


@pytest.mark.parametrize(
    ("contributions", "code"),
    [
        ([contribution(4, [0], signature(1))], 12),
        ([contribution(1, [0], signature(1)), contribution(1, [1], signature(2))], 13),
        ([], 4),
        ([contribution(0, [0], bytes(96))], 4),
    ],
    ids=["subcommittee", "repeated", "none", "bad signature"],
)
def test_sync_aggregate_rejected(contributions: list, code: int):
    with raises(ProposerError, f"proposer step failed with code {code}") as info:
        consensus.process_sync_committee_contributions("mainnet", "altair", contributions)
    assert info.value.code == code


def test_no_sync_aggregate_before_altair():
    with raises(ProposerError, "no sync aggregate at phase0") as info:
        consensus.process_sync_committee_contributions("mainnet", "phase0", [])
    assert info.value.code == 0


def test_sync_aggregate_of_a_contribution_that_does_not_decode():
    with raises(ProposerError, "input rejected: EthLib.Serialization.Ssz.Err.scope 160 159"):
        consensus.process_sync_committee_contributions("mainnet", "altair", [bytes(159)])


# ---- The state root ------------------------------------------------------------------------------

VECTORS = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "transition" / "minimal"

# The valid block cases of the sanity vectors, each with the blocks that it applies in turn.
VALID_CASES = [
    ("phase0", "attestation"),
    ("altair", "attestation"),
    ("bellatrix", "attestation"),
    ("capella", "activate_and_partial_withdrawal_max_effective_balance"),
    ("deneb", "activate_and_partial_withdrawal_max_effective_balance"),
    ("gloas", "missed_payload_next_block_with_withdrawals_satisfying_payload"),
    ("heze", "empty_block_transition"),
]


def _read(path: Path) -> bytes:
    return snappy.decompress(path.read_bytes())


@pytest.mark.parametrize(("fork", "case"), VALID_CASES)
def test_new_state_root_is_the_root_of_each_block(fork: str, case: str):
    folder = VECTORS / fork / "sanity" / "blocks" / "pyspec_tests" / case
    state = _read(folder / "pre.ssz_snappy")
    for path in sorted(folder.glob("blocks_*.ssz_snappy")):
        signed = _read(path)
        # A signed block is the offset of its message, its signature, then the message.
        message = signed[100:]
        # The message holds its slot, its proposer and its parent root before its state root.
        root = message[48:80]
        assert consensus.compute_new_state_root("minimal", FORKS[fork], state, message) == root
        state = consensus.state_transition("minimal", FORKS[fork], state, signed)


def test_new_state_root_of_a_block_with_a_wrong_root():
    folder = (
        VECTORS / "phase0" / "sanity" / "blocks" / "pyspec_tests" / "invalid_incorrect_state_root"
    )
    state = _read(folder / "pre.ssz_snappy")
    message = _read(folder / "blocks_0.ssz_snappy")[100:]
    assert consensus.compute_new_state_root("minimal", "phase0", state, message) != message[48:80]


# From Gloas a builder deposit and a builder exit follow, with their types 3 and 4.
BUILDER_DEPOSIT = bytes([4]) * 48 + bytes(32) + struct.pack("<Q", 32 * GWEI) + bytes(96)
BUILDER_EXIT = bytes(20) + bytes([5]) * 48


def test_execution_requests_of_builders():
    entries = [b"\x02" + CONSOLIDATION, b"\x03" + BUILDER_DEPOSIT, b"\x04" + BUILDER_EXIT]
    got = consensus.get_execution_requests("mainnet", "glamsterdam", entries)
    assert got == requests_bytes([b"", b"", CONSOLIDATION, BUILDER_DEPOSIT, BUILDER_EXIT])


def test_no_builder_requests_before_gloas():
    with raises(ProposerError, "proposer step failed with code 9"):
        consensus.get_execution_requests("mainnet", "fusaka", [b"\x03" + BUILDER_DEPOSIT])
