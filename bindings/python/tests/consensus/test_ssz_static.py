"""The beacon containers of EthLib against the ssz_static vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy

from .containers import CONTAINERS, FORKS

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "ssz_static"


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
    assert len(entries) == sum(
        1 for path in FILES.rglob("*") if path.name != "SHA256SUMS" and path.is_file()
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_every_case_is_a_known_container():
    assert {container for _, _, container, _ in _cases()} == set(CONTAINERS)


@pytest.mark.parametrize(
    "preset, fork, container, case",
    _cases(),
    ids=lambda value: value.relative_to(FILES).as_posix() if isinstance(value, Path) else None,
)
def test_case(preset, fork, container, case):
    _check(preset, fork, container, case)


def _check(preset, fork, container, case):
    """Decode a case in Lean, then compare its root and its bytes encoded again."""
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    root = YAML(typ="safe").load((case / "roots.yaml").read_text())["root"]
    got_root, encoded = consensus.ssz_static(preset, FORKS[fork], container, data)
    assert "0x" + got_root.hex() == root
    assert encoded == data


@pytest.mark.parametrize("container", CONTAINERS)
def test_no_container_outside_its_forks(container):
    first, dropped = CONTAINERS[container]
    forks = list(FORKS)
    end = forks.index(dropped) if dropped else len(forks)
    for fork in forks[: forks.index(first)] + forks[end:]:
        with pytest.raises(SszError):
            consensus.ssz_static("minimal", FORKS[fork], container, b"")


def test_every_fork_of_a_container_has_cases():
    found = {(fork, container) for _, fork, container, _ in _cases()}
    forks = list(FORKS)
    for container, (first, dropped) in CONTAINERS.items():
        end = forks.index(dropped) if dropped else len(forks)
        for fork in forks[forks.index(first) : end]:
            assert (fork, container) in found, (fork, container)


def test_truncated_bytes_are_rejected():
    # A withdrawal has a fixed size, so one byte less encodes no withdrawal.
    preset, fork, container, case = next(c for c in _cases() if c[2] == "Withdrawal")
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    with pytest.raises(SszError):
        consensus.ssz_static(preset, FORKS[fork], container, data[:-1])


def test_mainnet_state_reads_on_the_main_thread():
    # The Phase 0 mainnet state with every list empty, built field by field: the size of each
    # fixed field, or None for a list, which is a 4-byte offset to the end of the fixed part.
    # Its 65,536 RANDAO mixes must read without a stack that grows with them.
    sizes = [
        8,
        32,
        8,
        16,
        112,
        8192 * 32,
        8192 * 32,
        None,
        72,
        None,
        8,
        None,
        None,
        65536 * 32,
        8192 * 8,
        None,
        None,
        1,
        40,
        40,
        40,
    ]
    end = sum(4 if size is None else size for size in sizes)
    data = b"".join(end.to_bytes(4, "little") if size is None else bytes(size) for size in sizes)
    _, encoded = consensus.ssz_static("mainnet", "phase0", "BeaconState", data)
    assert encoded == data


def test_unknown_container():
    with pytest.raises(SszError):
        consensus.ssz_static("minimal", "fusaka", "NoSuchContainer", b"")


# The release archives that hold every case, one for each preset.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}


def _within(container: str, fork: str) -> bool:
    """Whether a container that EthLib defines exists at a fork."""
    if container not in CONTAINERS:
        return False
    first, dropped = CONTAINERS[container]
    forks = list(FORKS)
    end = forks.index(dropped) if dropped else len(forks)
    return forks.index(first) <= forks.index(fork) < end


def _archive_cases() -> list:
    """Every case of the archives for a container that EthLib defines, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        root = archives.unpack(name, *(f"tests/{preset}/{fork}/ssz_static" for fork in FORKS))
        base = root / "tests" / preset
        for fork in FORKS:
            for roots in sorted((base / fork / "ssz_static").glob("*/*/*/roots.yaml")):
                case = roots.parent
                container = case.relative_to(base / fork / "ssz_static").parts[0]
                if _within(container, fork):
                    cases.append(
                        pytest.param(
                            preset,
                            fork,
                            container,
                            case,
                            id=f"{preset}/{case.relative_to(base).as_posix()}",
                            marks=pytest.mark.archive(name),
                        )
                    )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no ssz_static case of a known container")
    return cases


@pytest.mark.parametrize("preset, fork, container, case", _archive_cases())
def test_archive_case(preset, fork, container, case):
    _check(preset, fork, container, case)


@pytest.mark.parametrize(
    "preset",
    [pytest.param(preset, marks=pytest.mark.archive(name)) for preset, name in ARCHIVES.items()],
)
def test_vendored_cases_are_copies(preset):
    # Each vendored file is the file of the release, byte for byte.
    name = ARCHIVES[preset]
    root = archives.unpack(name, *(f"tests/{preset}/{fork}/ssz_static" for fork in FORKS))
    vendored = [path for path in (FILES / preset).rglob("*") if path.is_file()]
    assert vendored
    for path in vendored:
        assert path.read_bytes() == (root / "tests" / path.relative_to(FILES)).read_bytes(), path
