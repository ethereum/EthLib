"""The Beacon API data that a validator signs or aggregates."""

from collections.abc import Sequence
from functools import cache
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus
from raising import raises

from .containers import FORKS
from .test_beacon_api_blocks import (
    ANCHOR_ROOT,
    BLOCK_ROOT,
    ENVELOPE_CASE,
    FORK_CASE,
    HEAD_ROOT,
    _store_case,
)
from .test_fork_choice import _hex, _inputs, _load, _read
from .test_honest_aggregation import (
    COUNT,
    DATA,
    OTHER_DATA,
    OTHER_PUBKEY,
    ROOT,
    SLOT,
    SUBCOMMITTEE_SIZE,
    _attestation_root,
    _committee,
    aggregate_signatures,
    contribution,
    electra_attestation,
    message,
    pectra_state,
    phase0_attestation,
    single,
    vote,
)
from .test_honest_validator import PUBKEY, altair_state, phase0_state

# Attestation data.

CASES = Path(__file__).resolve().parents[4] / "tests/consensus/fork_choice/minimal"


@cache
def _fork_case(fork: str) -> tuple[str, str, bytes, bytes, list[consensus.ForkChoiceStep]]:
    """The arguments that build the store after the steps of the ex ante case of a fork."""
    case = CASES / fork / "fork_choice/ex_ante/pyspec_tests/ex_ante_vanilla"
    steps = [step for raw in _load(case / "steps.yaml") for step in _inputs(case, raw)]
    return "minimal", FORKS[fork], _read(case, "anchor_state"), _read(case, "anchor_block"), steps


@pytest.mark.parametrize(("fork", "index"), [("deneb", "5"), ("electra", "0"), ("fulu", "0")])
def test_attestation_data_index_before_gloas(fork: str, index: str) -> None:
    # Before Electra the index is the requested committee, and in Electra and Fulu it is 0.
    data = consensus.api_attestation_data(*_fork_case(fork), 3, 5)["data"]
    assert (data["slot"], data["index"]) == ("3", index)


def test_attestation_data_at_the_slot_of_the_head() -> None:
    # The head of the case is the block at slot 1, with its payload; at its own slot the index is 0.
    data = consensus.api_attestation_data(*_store_case(), 1, 5)["data"]
    assert (data["slot"], data["index"], data["beacon_block_root"]) == ("1", "0", BLOCK_ROOT)
    assert data["target"] == {"epoch": "0", "root": ANCHOR_ROOT}


def test_attestation_data_after_the_head_signals_the_payload() -> None:
    # From Gloas, a head of an earlier slot whose payload is full gives index 1.
    # The store moves on to slot 2, 12 seconds after genesis in the minimal configuration.
    name, fork, anchor_state, anchor_block, steps = _store_case()
    later: list[consensus.ForkChoiceStep] = [*steps, ("tick", 12)]
    data = consensus.api_attestation_data(name, fork, anchor_state, anchor_block, later, 2, 5)[
        "data"
    ]
    assert (data["slot"], data["index"], data["beacon_block_root"]) == ("2", "1", BLOCK_ROOT)


def test_attestation_data_votes_for_the_head_of_two_children() -> None:
    data = consensus.api_attestation_data(*_store_case(FORK_CASE), 3, 0)["data"]
    assert data["beacon_block_root"] == HEAD_ROOT


def test_attestation_data_of_an_optimistic_head() -> None:
    message_text = f"Block {BLOCK_ROOT} is optimistic"
    with raises(consensus.ForkChoiceError, message_text) as error:
        consensus.api_attestation_data(*_store_case(), 1, 0, optimistic_roots=[_hex(BLOCK_ROOT)])
    assert error.value.code == 503


@pytest.mark.parametrize(
    ("slot", "text"),
    [(0, "Slot 0 is before the head"), (1000, "Slot 1000 is after the current slot")],
    ids=["before the head", "after the clock"],
)
def test_attestation_data_of_a_slot_out_of_range(slot: int, text: str) -> None:
    with raises(consensus.ForkChoiceError, text) as error:
        consensus.api_attestation_data(*_store_case(), slot, 0)
    assert error.value.code == 400


# Payload attestation data.


@pytest.mark.parametrize(("slot", "root"), [(0, ANCHOR_ROOT), (1, BLOCK_ROOT)])
def test_payload_attestation_data_names_the_block_of_the_slot(slot: int, root: str) -> None:
    answer = consensus.api_payload_attestation_data(
        *_store_case(ENVELOPE_CASE), slot, payload_present=True, blob_data_available=False
    )
    assert answer == {
        "version": "gloas",
        "data": {
            "beacon_block_root": root,
            "slot": str(slot),
            "payload_present": True,
            "blob_data_available": False,
        },
    }


def test_payload_attestation_data_of_an_empty_slot_is_none() -> None:
    # No block of the chain of the head is at slot 5: the answer has code 204.
    answer = consensus.api_payload_attestation_data(
        *_store_case(), 5, payload_present=False, blob_data_available=False
    )
    assert answer is None


def test_no_payload_attestation_data_before_gloas() -> None:
    text = "payload attestation data is not in a state before gloas"
    with raises(consensus.ForkChoiceError, text) as error:
        consensus.api_payload_attestation_data(
            *_fork_case("fulu"), 1, payload_present=True, blob_data_available=True
        )
    assert error.value.code == 400


# Aggregates.


def _phase0_aggregate(
    attestations: list[bytes],
    *,
    data: bytes = DATA,
    slot: int = SLOT,
    committee_index: int = 0,
    optimistic_roots: Sequence[bytes] = (),
) -> dict[str, Any]:
    return consensus.api_aggregate_attestation(
        "mainnet",
        "phase0",
        phase0_state(COUNT, SLOT),
        _attestation_root("phase0", data),
        slot,
        committee_index,
        attestations=attestations,
        optimistic_roots=optimistic_roots,
    )


def test_aggregate_of_the_matching_attestations() -> None:
    # Two votes on the data, and one on other data that stays out.
    attestations = [
        phase0_attestation([True, False], DATA, vote(1)),
        phase0_attestation([False, True], OTHER_DATA, vote(2)),
        phase0_attestation([False, True], DATA, vote(3)),
    ]
    expected = phase0_attestation([True, True], DATA, aggregate_signatures([vote(1), vote(3)]))
    assert _phase0_aggregate(attestations) == {
        "version": "phase0",
        "data": consensus.api_json("mainnet", "phase0", "Attestation", expected),
    }


@pytest.mark.parametrize(
    ("data", "slot", "committee_index"),
    [(OTHER_DATA, SLOT, 0), (DATA, SLOT + 1, 0), (DATA, SLOT, 1)],
    ids=["other data", "other slot", "other committee"],
)
def test_aggregate_with_no_match(data: bytes, slot: int, committee_index: int) -> None:
    # The only attestation has the data of slot 70 and committee 0.
    attestations = [phase0_attestation([True, False], DATA, vote(1))]
    with raises(consensus.ConsensusError, "No attestation matches the request") as error:
        _phase0_aggregate(attestations, data=data, slot=slot, committee_index=committee_index)
    assert error.value.code == 404


def test_aggregate_of_an_optimistic_block() -> None:
    # The other data votes for the block root 0x01...01, and its source and target roots are zero.
    block = bytes([1]) * 32
    attestations = [phase0_attestation([True, False], OTHER_DATA, vote(1))]
    with raises(consensus.ConsensusError, f"Block 0x{block.hex()} is optimistic") as error:
        _phase0_aggregate(attestations, data=OTHER_DATA, optimistic_roots=[block])
    assert error.value.code == 503


def test_aggregate_reads_the_list_of_its_fork() -> None:
    # Before Electra the single attestations are not read.
    attestations = [phase0_attestation([True, False], DATA, vote(1))]
    answer = consensus.api_aggregate_attestation(
        "mainnet",
        "phase0",
        phase0_state(COUNT, SLOT),
        _attestation_root("phase0", DATA),
        SLOT,
        0,
        attestations=attestations,
        singles=[single(0, 0, DATA, vote(2))],
    )
    expected = phase0_attestation([True, False], DATA, vote(1))
    assert answer["data"] == consensus.api_json("mainnet", "phase0", "Attestation", expected)


def test_aggregate_of_single_attestations() -> None:
    state = pectra_state(COUNT, SLOT)
    first, second = _committee(state)
    singles = [
        single(0, second, DATA, vote(1)),
        single(0, first, OTHER_DATA, vote(2)),
        single(1, first, DATA, vote(3)),
    ]
    answer = consensus.api_aggregate_attestation(
        "mainnet", "pectra", state, _attestation_root("pectra", DATA), SLOT, 0, singles=singles
    )
    expected = electra_attestation([False, True], DATA, vote(1), 0)
    assert answer == {
        "version": "electra",
        "data": consensus.api_json("mainnet", "pectra", "Attestation", expected),
    }


# Sync committee contributions.


def _contribution_json(subcommittee: int, seats: range, signature: bytes) -> dict[str, Any]:
    """The JSON of a contribution of slot 70 on the root, with bits set at the seats."""
    encoded = contribution(subcommittee, list(seats), signature)
    return consensus.api_json("mainnet", "altair", "SyncCommitteeContribution", encoded)


def test_contribution_of_the_matching_messages() -> None:
    # Every validator has the key of every seat, so one message sets each bit of a subcommittee.
    # Each set seat takes the signature of the first message of its key: here, the only one.
    messages = [message(SLOT, ROOT, 3, vote(1)), message(SLOT, bytes(32), 4, vote(2))]
    answer = consensus.api_sync_committee_contribution(
        "mainnet", "altair", altair_state(COUNT, SLOT), SLOT, 1, ROOT, messages=messages
    )
    signature = aggregate_signatures([vote(1)] * SUBCOMMITTEE_SIZE)
    assert answer == {"data": _contribution_json(1, range(SUBCOMMITTEE_SIZE), signature)}


def test_contribution_leaves_out_the_other_subcommittees() -> None:
    # Only the first subcommittee holds the key of the validators, so their messages count there.
    state = consensus.api_json("mainnet", "altair", "BeaconState", altair_state(COUNT, SLOT))
    keys = [PUBKEY] * SUBCOMMITTEE_SIZE + [OTHER_PUBKEY] * (3 * SUBCOMMITTEE_SIZE)
    state["current_sync_committee"]["pubkeys"] = ["0x" + key.hex() for key in keys]
    encoded = consensus.api_ssz("mainnet", "altair", "BeaconState", state)
    messages = [message(SLOT, ROOT, 3, vote(1))]
    answer = consensus.api_sync_committee_contribution(
        "mainnet", "altair", encoded, SLOT, 0, ROOT, messages=messages
    )
    signature = aggregate_signatures([vote(1)] * SUBCOMMITTEE_SIZE)
    assert answer == {"data": _contribution_json(0, range(SUBCOMMITTEE_SIZE), signature)}
    with raises(consensus.ConsensusError, "No sync committee message matches the request") as error:
        consensus.api_sync_committee_contribution(
            "mainnet", "altair", encoded, SLOT, 1, ROOT, messages=messages
        )
    assert error.value.code == 404


@pytest.mark.parametrize(
    ("slot", "subcommittee", "roots", "text", "code"),
    [
        (SLOT + 1, 1, [], f"Slot {SLOT + 1} is not the slot of the state", 400),
        (SLOT, 4, [], "Index 4 is not below 4", 400),
        (SLOT, 1, [ROOT], f"Block 0x{ROOT.hex()} is optimistic", 503),
    ],
    ids=["other slot", "no subnet", "optimistic"],
)
def test_contribution_refused(
    slot: int, subcommittee: int, roots: list[bytes], text: str, code: int
) -> None:
    with raises(consensus.ConsensusError, text) as error:
        consensus.api_sync_committee_contribution(
            "mainnet",
            "altair",
            altair_state(COUNT, SLOT),
            slot,
            subcommittee,
            ROOT,
            messages=[message(SLOT, ROOT, 3, vote(1))],
            optimistic_roots=roots,
        )
    assert error.value.code == code


def test_contribution_with_no_message() -> None:
    with raises(consensus.ConsensusError, "No sync committee message matches the request") as error:
        consensus.api_sync_committee_contribution(
            "mainnet", "altair", altair_state(COUNT, SLOT), SLOT, 1, ROOT
        )
    assert error.value.code == 404


def test_no_contribution_before_altair() -> None:
    text = "sync committee contribution is not in a state before altair"
    with raises(consensus.ConsensusError, text) as error:
        consensus.api_sync_committee_contribution(
            "mainnet", "phase0", phase0_state(COUNT, SLOT), SLOT, 1, ROOT
        )
    assert error.value.code == 400
