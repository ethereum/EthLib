"""The swap-or-not shuffle of EthLib against the shuffling vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus

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
    with pytest.raises(consensus.ConsensusError, match="not below the index count") as info:
        consensus.compute_shuffled_index(5, 5, bytes(32))
    assert info.value.code == 1


def test_seed_length():
    with pytest.raises(consensus.ConsensusError, match="a seed is 32 bytes") as info:
        consensus.compute_shuffled_permutation(5, bytes(31))
    assert info.value.code == 0
