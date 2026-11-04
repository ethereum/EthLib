"""The beacon containers of EthLib against the ssz_static vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "ssz_static"

# Each fork of the beacon chain up to Fulu, as consensus-specs names it, with its name in Lean.
FORKS = {
    "phase0": "phase0",
    "altair": "altair",
    "bellatrix": "bellatrix",
    "capella": "shapella",
    "deneb": "dencun",
    "electra": "pectra",
    "fulu": "fusaka",
}

# Each container that EthLib defines, with the first fork that has it.
CONTAINERS = {
    "Withdrawal": "capella",
    "ExecutionPayload": "bellatrix",
}


def _cases() -> list:
    """Every vendored case, as its preset, fork, container and directory."""
    cases = []
    for roots in sorted(FILES.rglob("roots.yaml")):
        case = roots.parent
        preset, fork, _, container = case.relative_to(FILES).parts[:4]
        cases.append((preset, fork, container, case))
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*") if path.name != "SHA256SUMS"
                               and path.is_file())
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_every_case_is_a_known_container():
    assert {container for _, _, container, _ in _cases()} == set(CONTAINERS)


@pytest.mark.parametrize(
    "preset, fork, container, case", _cases(),
    ids=lambda value: value.relative_to(FILES).as_posix() if isinstance(value, Path) else None,
)
def test_case(preset, fork, container, case):
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    root = YAML(typ="safe").load((case / "roots.yaml").read_text())["root"]
    got_root, encoded = consensus.ssz_static(preset, FORKS[fork], container, data)
    assert "0x" + got_root.hex() == root
    assert encoded == data


@pytest.mark.parametrize("container, first", CONTAINERS.items())
def test_no_container_before_its_fork(container, first):
    forks = list(FORKS)
    for fork in forks[:forks.index(first)]:
        with pytest.raises(SszError):
            consensus.ssz_static("minimal", FORKS[fork], container, b"")


def test_truncated_bytes_are_rejected():
    # A withdrawal has a fixed size, so one byte less encodes no withdrawal.
    preset, fork, container, case = next(c for c in _cases() if c[2] == "Withdrawal")
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    with pytest.raises(SszError):
        consensus.ssz_static(preset, FORKS[fork], container, data[:-1])


def test_unknown_container():
    with pytest.raises(SszError):
        consensus.ssz_static("minimal", "fusaka", "NoSuchContainer", b"")
