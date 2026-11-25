"""The fork upgrades of EthLib against the fork vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork"

# The forks whose upgrade EthLib holds, each from the fork before it.
UPGRADES = ("altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze")

# The release archives that hold the cases.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}


def runs(fork: str) -> bool:
    """Whether EthLib runs the upgrade cases of a fork."""
    return fork in UPGRADES


def run_case(preset: str, fork: str, case) -> None:
    """Run one case: the upgraded state must be the post state."""
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    meta = YAML(typ="safe").load((case / "meta.yaml").read_text())
    assert meta["fork"] == fork
    # Setting 2 marks placeholder signatures, which the case must not check.
    verify = meta.get("bls_setting", 0) != 2
    config_file = case / "config.yaml"
    config = (
        replacements(YAML(typ="safe").load(config_file.read_text()), preset)
        if config_file.exists()
        else None
    )
    got = consensus.upgrade_state(preset, FORKS[fork], pre, verify, config)
    assert got == snappy.decompress((case / "post.ssz_snappy").read_bytes())


def _cases() -> list:
    """Every vendored case, as its preset, fork and directory."""
    cases = []
    for pre in sorted(FILES.rglob("pre.ssz_snappy")):
        case = pre.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


def _archive_cases() -> list:
    """Every upgrade case of the archives that EthLib runs, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [f"tests/{preset}/{fork}/fork/fork" for fork in UPGRADES]
        base = archives.unpack(name, *paths) / "tests" / preset
        for path in paths:
            for pre in sorted((base / path.split("/", 2)[2]).rglob("pre.ssz_snappy")):
                case = pre.parent
                fork = case.relative_to(base).parts[0]
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
        raise LookupError("the archives hold no fork case that EthLib runs")
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


@archives.parametrize("preset, fork, case", _archive_cases)
def test_archive_case(preset, fork, case):
    run_case(preset, fork, case)


def test_no_upgrade_to_phase0():
    with raises(consensus.TransitionError, "no upgrade to phase0") as info:
        consensus.upgrade_state("minimal", "phase0", b"")
    assert info.value.code == 0


def test_undecodable_state():
    with raises(
        consensus.TransitionError,
        "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 10441 0",
    ) as info:
        consensus.upgrade_state("minimal", "glamsterdam", b"")
    assert info.value.code == 0


def test_heze_upgrades_with_an_unset_start_index():
    case = FILES / "minimal/heze/fork/fork/pyspec_tests/fork_base_state"
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    preset = consensus.preset("minimal")
    # The fixed fields and offsets of the Gloas state that come before eth1_deposit_index.
    roots = preset["SLOTS_PER_HISTORICAL_ROOT"]
    processed_at = 8 + 32 + 8 + 16 + 112 + 2 * 32 * roots + 4 + 72 + 4
    # Then the fields up to deposit_requests_start_index: two offsets, the RANDAO mixes and the
    # slashings, two offsets, the justification bits and three checkpoints, an offset, the two
    # sync committees, the latest block hash, two withdrawal indices and an offset.
    committee = preset["SYNC_COMMITTEE_SIZE"] * 48 + 48
    start_at = processed_at + 8 + 8 + 32 * preset["EPOCHS_PER_HISTORICAL_VECTOR"]
    start_at += 8 * preset["EPOCHS_PER_SLASHINGS_VECTOR"] + 8 + 1 + 3 * 40 + 4
    start_at += 2 * committee + 32 + 16 + 4
    processed = int.from_bytes(pre[processed_at : processed_at + 8], "little")
    assert int.from_bytes(pre[start_at : start_at + 8], "little") == processed
    # A network that starts at Fulu or later never sets the start index: it stays 2^64 - 1.
    unset = pre[:start_at] + (2**64 - 1).to_bytes(8, "little") + pre[start_at + 8 :]
    # Heze drops both indices, so the upgrade succeeds and gives the same state.
    upgraded = consensus.upgrade_state("minimal", "hegota", pre)
    assert consensus.upgrade_state("minimal", "hegota", unset) == upgraded
