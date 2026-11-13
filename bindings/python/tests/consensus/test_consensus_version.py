"""The consensus version of each fork against the ConsensusVersion schema of the Beacon API."""

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError
from raising import raises

# The enum ConsensusVersion of beacon-node-oapi.yaml, ethereum/beacon-APIs at 7911555e.
SCHEMA = ["phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas"]
# Every fork of the timeline, in the order of the Lean type, with its consensus version.
TIMELINE = [
    *(
        (fork, None)
        for fork in (
            "frontier",
            "homestead",
            "daoFork",
            "tangerineWhistle",
            "spuriousDragon",
            "byzantium",
            "constantinople",
            "petersburg",
            "istanbul",
            "muirGlacier",
        )
    ),
    ("phase0", "phase0"),
    ("berlin", "phase0"),
    ("london", "phase0"),
    ("altair", "altair"),
    ("arrowGlacier", "altair"),
    ("grayGlacier", "altair"),
    ("bellatrix", "bellatrix"),
    ("paris", "bellatrix"),
    ("shapella", "capella"),
    ("dencun", "deneb"),
    ("pectra", "electra"),
    ("fusaka", "fulu"),
    ("bpo1", "fulu"),
    ("bpo2", "fulu"),
    ("bpo3", "fulu"),
    ("bpo4", "fulu"),
    ("bpo5", "fulu"),
    ("glamsterdam", "gloas"),
    ("hegota", None),
]


@pytest.mark.parametrize(("fork", "version"), TIMELINE)
def test_consensus_version(fork: str, version: str | None):
    assert consensus.consensus_version(fork) == version


def test_every_version_is_named():
    # The versions of the timeline, in order, are the enum of the schema.
    versions = [version for _, version in TIMELINE if version is not None]
    assert list(dict.fromkeys(versions)) == SCHEMA


@pytest.mark.parametrize("version", SCHEMA)
def test_first_fork(version: str):
    fork = consensus.consensus_version_fork(version)
    assert consensus.consensus_version(fork) == version
    forks = [name for name, _ in TIMELINE]
    earlier = forks[: forks.index(fork)]
    assert all(consensus.consensus_version(name) != version for name in earlier)


@pytest.mark.parametrize("name", ["Deneb", "DENEB", " deneb", "deneb ", "heze", "", "dencun"])
def test_unknown_version(name: str):
    with raises(ConsensusError, f"no consensus version {name}"):
        consensus.consensus_version_fork(name)


def test_unknown_fork():
    with raises(ConsensusError, "no fork named deneb"):
        consensus.consensus_version("deneb")
