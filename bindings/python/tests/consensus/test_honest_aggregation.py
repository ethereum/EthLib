"""The votes of an honest attester and their aggregates, against py_ecc and the guides."""

import struct
from typing import cast

import pytest
from eth_typing import BLSSignature
from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from raising import raises

from .test_honest_validator import (
    DOMAIN_BEACON_ATTESTER,
    PUBKEY,
    SECRET_KEY,
    _expected_committee,
    _sha256,
    _signature,
    altair_state,
    phase0_state,
)

DUTY_ERROR = consensus.ValidatorDutyError

# A state of 64 mainnet validators at slot 70, in epoch 2, has one committee of two in each slot.
COUNT = 64
SLOT = 70

# Attestation data of slot 70 and committee 0, with zero roots, source epoch 1 and target epoch 2.
DATA = struct.pack("<QQ", SLOT, 0) + bytes(32) + struct.pack("<Q", 1) + bytes(32)
DATA += struct.pack("<Q", 2) + bytes(32)

# The data of another vote, for another block root.
OTHER_DATA = DATA[:16] + bytes([1]) * 32 + DATA[48:]


def bitlist(bits: list) -> bytes:
    """The SSZ bytes of a bitlist: the bits from the lowest, then a closing bit."""
    value = sum(1 << i for i, bit in enumerate(bits) if bit) | (1 << len(bits))
    return value.to_bytes(len(bits) // 8 + 1, "little")


def phase0_attestation(bits: list, data: bytes, signature: bytes) -> bytes:
    """A Phase 0 attestation: the offset of its bits, its data and its signature, then its bits."""
    return struct.pack("<I", 4 + len(data) + 96) + data + signature + bitlist(bits)


def electra_attestation(bits: list, data: bytes, signature: bytes, committee: int) -> bytes:
    """An Electra attestation, whose committee bits follow its signature."""
    committee_bits = (1 << committee).to_bytes(8, "little")
    fixed = 4 + len(data) + 96 + 8
    return struct.pack("<I", fixed) + data + signature + committee_bits + bitlist(bits)


def vote(key: int) -> bytes:
    return G2ProofOfPossession.Sign(key, b"vote")


def aggregate_signatures(signatures: list) -> bytes:
    """The aggregate of py_ecc, which types its signatures as BLSSignature."""
    return G2ProofOfPossession.Aggregate(cast(list[BLSSignature], signatures))


def _attestation_root(fork: str, data: bytes) -> bytes:
    root, _ = consensus.ssz_static("mainnet", fork, "AttestationData", data)
    return root


# ---- The aggregate signature ---------------------------------------------------------------------


def test_aggregate_signature():
    attestations = [phase0_attestation([True, False], DATA, vote(key)) for key in (1, 2, 3)]
    got = consensus.get_aggregate_signature("mainnet", "phase0", attestations)
    assert got == aggregate_signatures([vote(1), vote(2), vote(3)])


@pytest.mark.parametrize(
    "attestations", [[], [phase0_attestation([True], DATA, bytes(96))]], ids=["none", "bad"]
)
def test_aggregate_signature_rejected(attestations: list):
    # The aggregate of no signature, or of bytes that are no point, fails in BLS.
    with raises(DUTY_ERROR, "validator duty failed with code 3") as info:
        consensus.get_aggregate_signature("mainnet", "phase0", attestations)
    assert info.value.code == 3


def test_aggregate_signature_of_an_attestation_that_does_not_decode():
    with raises(DUTY_ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 0 228"):
        consensus.get_aggregate_signature("mainnet", "phase0", [b""])


# ---- The attestation of a validator --------------------------------------------------------------


def _attest(validator: int, fork: str = "phase0", key: bytes = SECRET_KEY) -> bytes:
    return consensus.construct_attestation(
        "mainnet", fork, phase0_state(COUNT, SLOT), DATA, validator, key
    )


def test_attestation_of_a_validator():
    # The bits have one bit for each member of the committee, set at the seat of the validator.
    committee = _expected_committee(COUNT, 2, SLOT)
    signature = _signature(_attestation_root("phase0", DATA), DOMAIN_BEACON_ATTESTER)
    for seat, validator in enumerate(committee):
        bits = [other == seat for other in range(len(committee))]
        assert _attest(validator) == phase0_attestation(bits, DATA, signature)


def test_attestation_of_a_validator_outside_its_committee():
    outside = next(v for v in range(COUNT) if v not in _expected_committee(COUNT, 2, SLOT))
    with raises(DUTY_ERROR, "validator duty failed with code 7") as info:
        _attest(outside)
    assert info.value.code == 7


def test_no_attestation_of_one_validator_from_electra():
    with raises(DUTY_ERROR, "no attestation of one validator at pectra") as info:
        _attest(0, fork="pectra")
    assert info.value.code == 0


@pytest.mark.parametrize("key", [bytes(32), bytes([0xFF]) * 32, bytes(31)])
def test_attestation_with_a_bad_secret_key(key: bytes):
    # Zero, a scalar above the group order and a key of 31 bytes are no secret keys.
    committee = _expected_committee(COUNT, 2, SLOT)
    message = "the secret key is not a nonzero scalar below the group order"
    with raises(DUTY_ERROR, message) as info:
        _attest(committee[0], key=key)
    assert info.value.code == 0


# ---- The aggregate of attestations ---------------------------------------------------------------


def _aggregate(attestations: list, fork: str = "phase0") -> bytes:
    return consensus.construct_aggregate(
        "mainnet", fork, phase0_state(COUNT, SLOT), DATA, attestations
    )


def test_aggregate_of_attestations():
    # Two votes on the data, each with one bit, and one vote on other data that stays out.
    attestations = [
        phase0_attestation([True, False], DATA, vote(1)),
        phase0_attestation([False, True], OTHER_DATA, vote(2)),
        phase0_attestation([False, True], DATA, vote(3)),
    ]
    joined = aggregate_signatures([vote(1), vote(3)])
    assert _aggregate(attestations) == phase0_attestation([True, True], DATA, joined)


def test_aggregate_of_attestations_with_the_attestation_of_a_validator():
    # The attestation of each member of the committee: the aggregate sets every bit.
    committee = _expected_committee(COUNT, 2, SLOT)
    attestations = [_attest(validator) for validator in committee]
    signature = _signature(_attestation_root("phase0", DATA), DOMAIN_BEACON_ATTESTER)
    joined = aggregate_signatures([signature, signature])
    assert _aggregate(attestations) == phase0_attestation([True, True], DATA, joined)


@pytest.mark.parametrize(
    ("attestations", "code"),
    [
        ([], 8),
        ([phase0_attestation([True, False], OTHER_DATA, vote(1))], 8),
        ([phase0_attestation([True, False, False], DATA, vote(1))], 10),
        ([phase0_attestation([True, False], DATA, bytes(96))], 3),
    ],
    ids=["none", "other data", "three bits", "bad signature"],
)
def test_aggregate_of_attestations_rejected(attestations: list, code: int):
    with raises(DUTY_ERROR, f"validator duty failed with code {code}") as info:
        _aggregate(attestations)
    assert info.value.code == code


def test_no_aggregate_of_attestations_from_electra():
    with raises(DUTY_ERROR, "no aggregate of attestations at pectra") as info:
        _aggregate([], fork="pectra")
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("state", "data", "message"),
    [
        (b"", DATA, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 0 2687377"),
        (None, DATA[:127], "input rejected: EthLib.Serialization.Ssz.Err.scope 128 127"),
    ],
    ids=["state", "data"],
)
def test_aggregate_of_attestations_with_an_input_that_does_not_decode(
    state: bytes | None, data: bytes, message: str
):
    state = phase0_state(COUNT, SLOT) if state is None else state
    with raises(DUTY_ERROR, message):
        consensus.construct_aggregate("mainnet", "phase0", state, data, [])


# ---- Single attestations and their aggregate -----------------------------------------------------


def pectra_state(count: int, slot: int) -> bytes:
    """An Altair state of `count` validators at a slot, upgraded fork by fork to Electra."""
    state = altair_state(count, slot)
    for fork in ["bellatrix", "shapella", "dencun", "pectra"]:
        state = consensus.upgrade_state("mainnet", fork, state, verify=False)
    return state


@pytest.fixture(scope="module")
def pectra() -> bytes:
    return pectra_state(COUNT, SLOT)


def _committee(state: bytes) -> list:
    """The committee of the slot, read from the committee assignments of its validators."""
    for validator in range(COUNT):
        assignment = consensus.get_committee_assignment("mainnet", "pectra", state, 2, validator)
        if assignment is not None and assignment[2] == SLOT:
            return assignment[0]
    raise AssertionError("no committee in the slot")


# The Electra domain of a state whose current fork version is that of Electra.
ELECTRA_FORK_VERSION = bytes([5, 0, 0, 0])


def _electra_signature(root: bytes) -> bytes:
    fork_data_root = _sha256(ELECTRA_FORK_VERSION + bytes(28) + bytes(32))
    domain = DOMAIN_BEACON_ATTESTER + fork_data_root[:28]
    return G2ProofOfPossession.Sign(1, _sha256(root + domain))


def single(committee: int, attester: int, data: bytes, signature: bytes) -> bytes:
    return struct.pack("<QQ", committee, attester) + data + signature


def test_single_attestation(pectra: bytes):
    got = consensus.construct_single_attestation(
        "mainnet", "pectra", pectra, DATA, 0, 9, SECRET_KEY
    )
    signature = _electra_signature(_attestation_root("pectra", DATA))
    assert got == single(0, 9, DATA, signature)


def test_no_single_attestation_before_electra():
    with raises(DUTY_ERROR, "no single attestation at dencun") as info:
        consensus.construct_single_attestation(
            "mainnet", "dencun", phase0_state(1), DATA, 0, 0, SECRET_KEY
        )
    assert info.value.code == 0


def test_single_attestation_with_a_bad_secret_key(pectra: bytes):
    message = "the secret key is not a nonzero scalar below the group order"
    with raises(DUTY_ERROR, message) as info:
        consensus.construct_single_attestation("mainnet", "pectra", pectra, DATA, 0, 0, bytes(32))
    assert info.value.code == 0


def _aggregate_singles(state: bytes, singles: list, committee: int = 0) -> bytes:
    return consensus.construct_aggregate_of_single_attestations(
        "mainnet", "pectra", state, DATA, committee, singles
    )


def test_aggregate_of_single_attestations(pectra: bytes):
    # One vote of the second member, one on other data and one of another committee stay out.
    first, second = _committee(pectra)
    singles = [
        single(0, second, DATA, vote(1)),
        single(0, first, OTHER_DATA, vote(2)),
        single(1, first, DATA, vote(3)),
    ]
    got = _aggregate_singles(pectra, singles)
    assert got == electra_attestation([False, True], DATA, vote(1), 0)


def test_aggregate_of_the_single_attestations_of_a_committee(pectra: bytes):
    # The vote of each member, in reverse order: the bits follow the seats.
    committee = _committee(pectra)
    singles = [single(0, member, DATA, vote(key)) for key, member in enumerate(committee[::-1], 1)]
    got = _aggregate_singles(pectra, singles)
    assert got == electra_attestation(
        [True, True], DATA, aggregate_signatures([vote(1), vote(2)]), 0
    )


def test_aggregate_of_single_attestations_rejected(pectra: bytes):
    first, _ = _committee(pectra)
    outside = next(v for v in range(COUNT) if v not in _committee(pectra))
    cases = [
        ([single(64, first, DATA, vote(1))], 64, 11),
        ([], 0, 8),
        ([single(0, first, OTHER_DATA, vote(1))], 0, 8),
        ([single(0, outside, DATA, vote(1))], 0, 7),
        ([single(0, first, DATA, bytes(96))], 0, 3),
    ]
    for singles, committee, code in cases:
        with raises(DUTY_ERROR, f"validator duty failed with code {code}") as info:
            _aggregate_singles(pectra, singles, committee)
        assert info.value.code == code


def test_no_aggregate_of_single_attestations_before_electra():
    with raises(DUTY_ERROR, "no aggregate of single attestations at dencun") as info:
        consensus.construct_aggregate_of_single_attestations(
            "mainnet", "dencun", phase0_state(1), DATA, 0, []
        )
    assert info.value.code == 0


def test_aggregate_of_a_single_attestation_that_does_not_decode(pectra: bytes):
    with raises(DUTY_ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scope 240 239"):
        _aggregate_singles(pectra, [bytes(239)])


# ---- Sync committee contributions ----------------------------------------------------------------

SYNC_COMMITTEE_SIZE = 512
SUBCOMMITTEE_SIZE = SYNC_COMMITTEE_SIZE // 4
ROOT = bytes(range(32))


def sync_committee(keys: list) -> bytes:
    """The SSZ bytes of a sync committee of these keys, with a zero aggregate key."""
    return b"".join(keys) + bytes(48)


def message(slot: int, root: bytes, validator: int, signature: bytes) -> bytes:
    return struct.pack("<Q", slot) + root + struct.pack("<Q", validator) + signature


def contribution(subcommittee: int, seats: list, signature: bytes) -> bytes:
    bits = sum(1 << seat for seat in seats).to_bytes(SUBCOMMITTEE_SIZE // 8, "little")
    return struct.pack("<Q", SLOT) + ROOT + struct.pack("<Q", subcommittee) + bits + signature


# A committee with the key of every validator at the even seats, and another key at the odd seats.
OTHER_PUBKEY = G2ProofOfPossession.SkToPk(2)
MIXED = sync_committee([PUBKEY if seat % 2 == 0 else OTHER_PUBKEY for seat in range(512)])


def _contribute(messages: list, subcommittee: int = 1, committee: bytes = MIXED) -> bytes:
    return consensus.construct_sync_committee_contribution(
        "mainnet", "altair", altair_state(COUNT, SLOT), committee, ROOT, subcommittee, messages
    )


def test_sync_committee_contribution():
    # The key of the validator holds the 64 even seats of the subcommittee.
    # Messages of another slot or for another root stay out.
    messages = [
        message(SLOT, ROOT, 5, vote(1)),
        message(SLOT + 1, ROOT, 6, vote(2)),
        message(SLOT, bytes(32), 7, vote(3)),
    ]
    seats = range(0, SUBCOMMITTEE_SIZE, 2)
    # One signature for each seat that the key holds.
    joined = aggregate_signatures([vote(1)] * len(seats))
    assert _contribute(messages) == contribution(1, list(seats), joined)


def test_sync_committee_contribution_takes_the_first_message_of_a_key():
    # Every validator has the key, so the first message signs for every seat.
    messages = [message(SLOT, ROOT, 5, vote(1)), message(SLOT, ROOT, 6, vote(2))]
    joined = aggregate_signatures([vote(1)] * (SUBCOMMITTEE_SIZE // 2))
    assert _contribute(messages) == contribution(1, list(range(0, SUBCOMMITTEE_SIZE, 2)), joined)


@pytest.mark.parametrize(
    ("messages", "subcommittee", "committee", "code"),
    [
        ([message(SLOT, ROOT, 5, vote(1))], 4, MIXED, 11),
        ([], 1, MIXED, 8),
        ([message(SLOT, bytes(32), 5, vote(1))], 1, MIXED, 8),
        ([message(SLOT, ROOT, COUNT, vote(1))], 1, MIXED, 1),
        ([message(SLOT, ROOT, 5, vote(1))], 1, sync_committee([OTHER_PUBKEY] * 512), 7),
        ([message(SLOT, ROOT, 5, bytes(96))], 1, MIXED, 3),
    ],
    ids=["subcommittee", "none", "other root", "unknown validator", "no seat", "bad signature"],
)
def test_sync_committee_contribution_rejected(
    messages: list, subcommittee: int, committee: bytes, code: int
):
    with raises(DUTY_ERROR, f"validator duty failed with code {code}") as info:
        _contribute(messages, subcommittee, committee)
    assert info.value.code == code


def test_no_sync_committee_contribution_before_altair():
    with raises(DUTY_ERROR, "no sync committee at phase0") as info:
        consensus.construct_sync_committee_contribution(
            "mainnet", "phase0", phase0_state(1), MIXED, ROOT, 0, []
        )
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("committee", "root", "messages", "message"),
    [
        (MIXED[:-1], ROOT, [], "input rejected: EthLib.Serialization.Ssz.Err.scope 24624 24623"),
        (MIXED, ROOT[:31], [], "input rejected: EthLib.Serialization.Ssz.Err.scope 32 31"),
        (MIXED, ROOT, [bytes(143)], "input rejected: EthLib.Serialization.Ssz.Err.scope 144 143"),
    ],
    ids=["committee", "root", "message"],
)
def test_sync_committee_contribution_with_an_input_that_does_not_decode(
    committee: bytes, root: bytes, messages: list, message: str
):
    with raises(DUTY_ERROR, message):
        consensus.construct_sync_committee_contribution(
            "mainnet", "altair", altair_state(COUNT, SLOT), committee, root, 1, messages
        )
