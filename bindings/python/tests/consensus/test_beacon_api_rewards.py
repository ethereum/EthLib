"""The Beacon API attestation rewards, on the states of the pinned rewards vectors."""

from functools import cache
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_rewards import FILES

# The slots of an epoch in each preset.
SLOTS_PER_EPOCH = {"minimal": 8, "mainnet": 32}

# The flag parts of an answer, as the vectors name their deltas.
FLAG_PARTS = {"source": "source_deltas", "target": "target_deltas", "head": "head_deltas"}

# The forks whose basic case holds validators that earned a reward for every vote.
WITH_FULL_VOTERS = ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu")


def _cases() -> list:
    """Every vendored rewards case, as its preset, fork and directory."""
    return [
        pytest.param(*pre.parent.relative_to(FILES).parts[:2], pre.parent, id=str(pre.parent))
        for pre in sorted(FILES.rglob("pre.ssz_snappy"))
    ]


@cache
def _read(path: Path) -> bytes:
    return snappy.decompress(path.read_bytes())


def _decode(data: bytes) -> tuple[list[int], list[int]]:
    """The rewards and penalties of SSZ deltas: a container of two lists of uint64."""
    start = int.from_bytes(data[0:4], "little")
    middle = int.from_bytes(data[4:8], "little")

    def amounts(chunk: bytes) -> list[int]:
        return [int.from_bytes(chunk[i : i + 8], "little") for i in range(0, len(chunk), 8)]

    return amounts(data[start:middle]), amounts(data[middle:])


def _before_rewards(preset: str, fork: str, pre: bytes) -> bytes:
    """The state that the rewards step reads: after justification and the inactivity scores."""
    state = consensus.process_epoch(preset, FORKS[fork], "justification_and_finalization", pre)
    if fork == "phase0":
        return state
    return consensus.process_epoch(preset, FORKS[fork], "inactivity_updates", state)


def _expected(preset: str, fork: str, pre: bytes) -> dict[str, tuple[list[int], list[int]]]:
    """The deltas of each kind that the rewards step computes, by the name of the vectors."""
    components = [*FLAG_PARTS.values(), "inactivity_penalty_deltas"]
    if fork == "phase0":
        components.append("inclusion_delay_deltas")
    state = _before_rewards(preset, fork, pre)
    batch = consensus.rewards_deltas_batch(preset, FORKS[fork], components, state)
    return {component: _decode(data) for component, data in zip(components, batch, strict=True)}


def _previous_epoch(preset: str, fork: str, pre: bytes) -> int:
    """The previous epoch of a state, or -1 in the first epoch."""
    state = consensus.api_json(preset, FORKS[fork], "BeaconState", pre)
    return int(state["slot"]) // SLOTS_PER_EPOCH[preset] - 1


@cache
def _state(preset: str, fork: str, case: Path) -> bytes:
    """The state of a case, taken through empty slots to the last slot of its epoch."""
    # The answer needs the last slot; empty slots change no vote and no root that the rewards read.
    pre = _read(case / "pre.ssz_snappy")
    slot = int(consensus.api_json(preset, FORKS[fork], "BeaconState", pre)["slot"])
    remaining = SLOTS_PER_EPOCH[preset] - 1 - slot % SLOTS_PER_EPOCH[preset]
    return consensus.process_slots(preset, FORKS[fork], pre, remaining) if remaining else pre


def _rewards(preset: str, fork: str, case: Path, **options: Any) -> dict[str, Any]:
    pre = _state(preset, fork, case)
    epoch = _previous_epoch(preset, fork, pre)
    return consensus.api_attestation_rewards(preset, FORKS[fork], pre, epoch, **options)


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_total_rewards_match_deltas(preset, fork, case):
    pre = _state(preset, fork, case)
    if _previous_epoch(preset, fork, pre) < 0:
        pytest.skip("the vectors of the first epoch have no previous epoch to ask for")
    total = _rewards(preset, fork, case)["data"]["total_rewards"]
    # The answer reads the state after the steps that come before the rewards in the transition.
    expected = _expected(preset, fork, pre)
    nets = {
        part: [r - p for r, p in zip(*expected[component], strict=True)]
        for part, component in FLAG_PARTS.items()
    }
    _, inactivity = expected["inactivity_penalty_deltas"]
    # An empty request names every validator, in the order of the registry.
    assert [int(entry["validator_index"]) for entry in total] == list(range(len(inactivity)))
    for index, entry in enumerate(total):
        for part, net in nets.items():
            assert int(entry[part]) == net[index], (index, part)
        assert int(entry["inactivity"]) == -inactivity[index], index
        if fork == "phase0":
            # The inclusion deltas also hold the shares the validator earned as a proposer.
            inclusion, _ = expected["inclusion_delay_deltas"]
            assert int(entry["inclusion_delay"]) <= inclusion[index], index
        else:
            assert "inclusion_delay" not in entry


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_ideal_rewards_match_full_voters(preset, fork, case):
    pre = _state(preset, fork, case)
    if _previous_epoch(preset, fork, pre) < 0:
        pytest.skip("the vectors of the first epoch have no previous epoch to ask for")
    data = _rewards(preset, fork, case)["data"]
    balances = [int(entry["effective_balance"]) for entry in data["ideal_rewards"]]
    # The balances are distinct and in increasing order.
    assert balances == sorted(set(balances))
    ideal = dict(zip(balances, data["ideal_rewards"], strict=True))
    state = consensus.api_json(preset, FORKS[fork], "BeaconState", pre)
    full = 0
    # A validator that earned a reward for every vote voted right, so it earns the ideal parts.
    # Before Altair its vote may be included later than one slot after it, which earns less.
    for entry in data["total_rewards"]:
        if all(int(entry[part]) > 0 for part in FLAG_PARTS):
            full += 1
            index = int(entry["validator_index"])
            balance = int(state["validators"][index]["effective_balance"])
            for part in (*FLAG_PARTS, "inactivity"):
                assert entry[part] == ideal[balance][part], (index, part)
            if fork == "phase0":
                assert int(entry["inclusion_delay"]) <= int(ideal[balance]["inclusion_delay"])
    # The basic case holds validators that voted right at each fork from phase 0 to Fulu.
    if case.parent.parent.name == "basic" and fork in WITH_FULL_VOTERS:
        assert full > 0


def _case(fork: str, group: str) -> Path:
    return next(FILES.glob(f"minimal/{fork}/rewards/{group}/pyspec_tests/*"))


@pytest.mark.parametrize("fork", ["phase0", "altair", "electra"])
def test_named_validators(fork):
    case = _case(fork, "basic")
    pre = _state("minimal", fork, case)
    state = consensus.api_json("minimal", FORKS[fork], "BeaconState", pre)
    pubkey = state["validators"][3]["pubkey"]
    # An index past the registry names no validator and gives no entry.
    past = str(len(state["validators"]))
    total = _rewards("minimal", fork, case, ids=[pubkey, "1", past, "1"])["data"]["total_rewards"]
    everyone = _rewards("minimal", fork, case)["data"]["total_rewards"]
    assert total == [everyone[1], everyone[3]]


@pytest.mark.parametrize("fork", ["phase0", "altair"])
def test_other_epoch_not_known(fork):
    case = _case(fork, "basic")
    pre = _state("minimal", fork, case)
    epoch = _previous_epoch("minimal", fork, pre) + 1
    message = f"Epoch {epoch} not known or required data not available"
    with raises(consensus.ConsensusError, message) as info:
        consensus.api_attestation_rewards("minimal", FORKS[fork], pre, epoch)
    assert info.value.code == 404


def test_invalid_identifier():
    case = _case("altair", "basic")
    pre = _state("minimal", "altair", case)
    epoch = _previous_epoch("minimal", "altair", pre)
    with raises(consensus.ConsensusError, "Invalid validator ID: nobody") as info:
        consensus.api_attestation_rewards("minimal", "altair", pre, epoch, ids=["nobody"])
    assert info.value.code == 400


def test_other_slot_not_known():
    case = _case("altair", "basic")
    pre = _read(case / "pre.ssz_snappy")
    # The pinned state is not at the last slot of its epoch, so it does not hold every vote yet.
    epoch = _previous_epoch("minimal", "altair", pre)
    message = f"Epoch {epoch} not known or required data not available"
    with raises(consensus.ConsensusError, message) as info:
        consensus.api_attestation_rewards("minimal", "altair", pre, epoch)
    assert info.value.code == 404
