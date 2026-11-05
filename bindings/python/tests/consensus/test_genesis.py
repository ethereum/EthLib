"""The genesis of EthLib against the genesis vectors."""

import hashlib
from pathlib import Path

import archives
import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "genesis"

# The forks at which EthLib runs each handler of the genesis runner.
HANDLERS = {
    "initialization": ("phase0",),
    "validity": ("phase0",),
}

# The release archive that holds the cases; the mainnet archive has none.
ARCHIVE = "consensus-specs/v1.7.0-beta.4/minimal"


def runs(fork: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a genesis handler at a fork."""
    return fork in HANDLERS.get(handler, ())


def _load(path: Path):
    """The content of a YAML file."""
    return YAML(typ="safe").load(path.read_text())


def run_case(preset: str, fork: str, handler: str, case: Path) -> None:
    """Run one case: build the genesis state, or tell whether a state launches the chain."""
    if handler == "validity":
        state = snappy.decompress((case / "genesis.ssz_snappy").read_bytes())
        assert consensus.is_valid_genesis_state(preset, FORKS[fork], state) == _load(
            case / "is_valid.yaml")
        return
    eth1 = _load(case / "eth1.yaml")
    count = _load(case / "meta.yaml")["deposits_count"]
    deposits = [snappy.decompress((case / f"deposits_{index}.ssz_snappy").read_bytes())
                for index in range(count)]
    state = consensus.initialize_genesis(preset, FORKS[fork],
                                         bytes.fromhex(eth1["eth1_block_hash"][2:]),
                                         eth1["eth1_timestamp"], deposits)
    assert state == snappy.decompress((case / "state.ssz_snappy").read_bytes())


def _cases(base: Path, marks=()) -> list:
    """Every case under a directory of presets, as its preset, fork, handler and directory."""
    cases = []
    for manifest in sorted(path for path in base.rglob("*")
                           if path.is_dir() and path.parent.name == "pyspec_tests"):
        preset, fork, runner, handler = manifest.relative_to(base).parts[:4]
        if runner == "genesis" and runs(fork, handler):
            cases.append(pytest.param(preset, fork, handler, manifest, marks=marks,
                                      id=manifest.relative_to(base).as_posix()))
    return cases


def _archive_cases() -> list:
    """Every genesis case of the archive at a fork that EthLib runs, when the cache is set."""
    if archives.CACHE is None:
        return []
    paths = [f"tests/minimal/{fork}/genesis/{handler}" for handler, forks in HANDLERS.items()
             for fork in forks]
    base = archives.unpack(ARCHIVE, *paths) / "tests"
    cases = _cases(base, marks=pytest.mark.archive(ARCHIVE))
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archive holds no genesis case")
    return cases


@pytest.mark.parametrize(("preset", "fork", "handler", "case"), _cases(FILES))
def test_case(preset: str, fork: str, handler: str, case: Path) -> None:
    run_case(preset, fork, handler, case)


@pytest.mark.parametrize(("preset", "fork", "handler", "case"), _archive_cases())
def test_archive_case(preset: str, fork: str, handler: str, case: Path) -> None:
    run_case(preset, fork, handler, case)


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*") if path.is_file()
                               and path.name != "SHA256SUMS")
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name
