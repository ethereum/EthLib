"""The fork upgrades of EthLib against the fork vectors of consensus-specs."""

import archives
import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_data_column import replacements

# The forks whose upgrade EthLib holds, each from the fork before it.
UPGRADES = ("gloas",)

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
    config = (replacements(YAML(typ="safe").load(config_file.read_text()), preset)
              if config_file.exists() else None)
    got = consensus.upgrade_state(preset, FORKS[fork], pre, verify, config)
    assert got == snappy.decompress((case / "post.ssz_snappy").read_bytes())


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
                cases.append(pytest.param(preset, fork, case,
                                          id=f"{preset}/{case.relative_to(base).as_posix()}",
                                          marks=pytest.mark.archive(name)))
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no fork case that EthLib runs")
    return cases


@pytest.mark.parametrize("preset, fork, case", _archive_cases())
def test_archive_case(preset, fork, case):
    run_case(preset, fork, case)


def test_no_upgrade_to_fulu():
    with pytest.raises(consensus.TransitionError) as info:
        consensus.upgrade_state("minimal", "fusaka", b"")
    assert info.value.code == 0


def test_undecodable_state():
    with pytest.raises(consensus.TransitionError) as info:
        consensus.upgrade_state("minimal", "glamsterdam", b"")
    assert info.value.code == 0
