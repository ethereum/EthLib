"""The custody functions of EthLib against the Fulu networking vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "networking"
CASES = FILES / "mainnet" / "fulu" / "networking"


def _cases(handler: str) -> list:
    return sorted((CASES / handler / "pyspec_tests").iterdir())


def _meta(case: Path) -> dict:
    return YAML(typ="safe").load((case / "meta.yaml").read_text())


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*.yaml"))
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("case", _cases("get_custody_groups"), ids=lambda case: case.name)
def test_get_custody_groups(case):
    meta = _meta(case)
    groups = consensus.get_custody_groups(int(meta["node_id"]), meta["custody_group_count"])
    assert groups == meta["result"]


@pytest.mark.parametrize(
    "case", _cases("compute_columns_for_custody_group"), ids=lambda case: case.name
)
def test_compute_columns_for_custody_group(case):
    meta = _meta(case)
    assert consensus.compute_columns_for_custody_group(meta["custody_group"]) == meta["result"]


def test_too_many_groups():
    with pytest.raises(consensus.ConsensusError, match="exceeds the number of groups") as info:
        consensus.get_custody_groups(0, 129)
    assert info.value.code == 1


def test_group_out_of_range():
    with pytest.raises(consensus.ConsensusError, match="not below the number of groups") as info:
        consensus.compute_columns_for_custody_group(128)
    assert info.value.code == 2


def test_unknown_name():
    with pytest.raises(consensus.ConsensusError) as info:
        consensus.compute_columns_for_custody_group(0, "nonexistent")
    assert info.value.code == 0
