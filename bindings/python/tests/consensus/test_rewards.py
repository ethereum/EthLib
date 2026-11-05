"""The reward and penalty deltas of EthLib against the rewards vectors."""

import hashlib
from pathlib import Path

import pytest

import archives
from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "rewards"

# The forks at which EthLib runs the cases.
SPECIFIED = ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas")

# The groups of cases of the vectors.
HANDLERS = ("basic", "leak", "inactivity_scores", "random")

# The deltas that a case holds before Altair; from Altair it has no inclusion delay deltas.
COMPONENTS = (
    "source_deltas",
    "target_deltas",
    "head_deltas",
    "inclusion_delay_deltas",
    "inactivity_penalty_deltas",
)

# The release archives that hold the cases.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}


def runs(fork: str) -> bool:
    """Whether EthLib runs the rewards cases at a fork."""
    return fork in SPECIFIED


def run_case(preset: str, fork: str, case: Path) -> None:
    """Check each deltas file of a case against the deltas that EthLib computes."""
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    checked = 0
    for component in COMPONENTS:
        expected = case / f"{component}.ssz_snappy"
        if expected.exists():
            got = consensus.rewards_deltas(preset, FORKS[fork], component, pre)
            assert got == snappy.decompress(expected.read_bytes()), component
            checked += 1
    assert checked == (5 if fork == "phase0" else 4)


def _cases() -> list:
    """Every vendored case, as its preset, fork and directory."""
    cases = []
    for pre in sorted(FILES.rglob("pre.ssz_snappy")):
        case = pre.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


def _archive_cases() -> list:
    """Every case of the archives at a fork that EthLib runs, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [f"tests/{preset}/{fork}/rewards" for fork in SPECIFIED]
        base = archives.unpack(name, *paths) / "tests" / preset
        for pre in sorted(base.glob("*/rewards/*/pyspec_tests/*/pre.ssz_snappy")):
            case = pre.parent
            fork = case.relative_to(base).parts[0]
            if runs(fork):
                cases.append(
                    pytest.param(
                        preset,
                        fork,
                        case,
                        id=f"{preset}/{case.relative_to(base).as_posix()}",
                        marks=pytest.mark.archive(name),
                    )
                )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no rewards case that EthLib runs")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1 for path in FILES.rglob("*") if path.is_file() and path.name != "SHA256SUMS"
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_case(preset, fork, case):
    assert runs(fork)
    run_case(preset, fork, case)


@pytest.mark.parametrize("preset, fork, case", _archive_cases())
def test_archive_case(preset, fork, case):
    run_case(preset, fork, case)


def _pre(fork: str) -> bytes:
    """The state before a vendored minimal case at a fork."""
    case = next(FILES.glob(f"minimal/{fork}/rewards/*/pyspec_tests/*"))
    return snappy.decompress((case / "pre.ssz_snappy").read_bytes())


def test_inclusion_delay_from_altair():
    # From Altair, the inclusion delay is no longer a kind of deltas.
    with raises(consensus.TransitionError, "no deltas inclusion_delay_deltas at altair") as info:
        consensus.rewards_deltas(
            "minimal", FORKS["altair"], "inclusion_delay_deltas", _pre("altair")
        )
    assert info.value.code == 0


def test_unknown_component():
    with raises(consensus.TransitionError, "no deltas no_such_deltas at phase0") as info:
        consensus.rewards_deltas("minimal", FORKS["phase0"], "no_such_deltas", _pre("phase0"))
    assert info.value.code == 0
