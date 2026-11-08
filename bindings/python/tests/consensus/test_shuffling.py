"""The swap-or-not shuffle of EthLib against the shuffling vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from raising import raises

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "shuffling"
PRESETS = ("minimal", "mainnet")


def _cases() -> list:
    return [
        (preset, case)
        for preset in PRESETS
        for case in sorted((FILES / preset / "phase0" / "shuffling" / "core" / "shuffle").iterdir())
    ]


def _mapping(case: Path) -> dict:
    return YAML(typ="safe").load((case / "mapping.yaml").read_text())


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*.yaml"))
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, case", _cases(), ids=lambda value: getattr(value, "name", value))
def test_shuffle(preset, case):
    vector = _mapping(case)
    seed = bytes.fromhex(vector["seed"][2:])
    shuffled = consensus.compute_shuffled_permutation(vector["count"], seed, preset)
    assert shuffled == vector["mapping"]


@pytest.mark.parametrize("preset", PRESETS)
def test_shuffled_index(preset):
    # Each index of a small case maps on its own to its entry of the shuffled list.
    case = next(case for name, case in _cases() if name == preset and case.name.endswith("_33"))
    vector = _mapping(case)
    seed = bytes.fromhex(vector["seed"][2:])
    for index, position in enumerate(vector["mapping"]):
        assert consensus.compute_shuffled_index(index, vector["count"], seed, preset) == position


def test_index_out_of_range():
    with raises(consensus.ConsensusError, "index 5 is not below the index count 5") as info:
        consensus.compute_shuffled_index(5, 5, bytes(32))
    assert info.value.code == 201


def test_count_above_bound():
    # The bucket number of a position is 4 bytes, so a count above 2^40 fails.
    with raises(consensus.ConsensusError, "the index count 1099511627777 is above 2^40") as info:
        consensus.compute_shuffled_index(0, 2**40 + 1, bytes(32))
    assert info.value.code == 204


def test_permutation_count_above_bound():
    # The full permutation fails for the same counts, before it allocates anything.
    with raises(consensus.ConsensusError, "the index count 1099511627777 is above 2^40") as info:
        consensus.compute_shuffled_permutation(2**40 + 1, bytes(32))
    assert info.value.code == 204


def test_index_checked_first():
    # The spec asserts the index before it shuffles, so this index error comes first.
    count = 2**40 + 1
    with raises(consensus.ConsensusError, f"index {count} is not below the index count {count}"):
        consensus.compute_shuffled_index(count, count, bytes(32))


def test_count_at_bound():
    assert consensus.compute_shuffled_index(2**40 - 1, 2**40, bytes(32)) < 2**40


def test_seed_length():
    with raises(consensus.ConsensusError, "expected 32 bytes, got 31") as info:
        consensus.compute_shuffled_permutation(5, bytes(31))
    assert info.value.code == 0
