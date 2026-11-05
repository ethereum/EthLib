"""The custody functions of EthLib against the Fulu networking vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.cryptography import _native
from raising import raises

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "networking"

# The presets whose Fulu cases the directory holds.
PRESETS = ("mainnet", "minimal")


def _cases(handler: str) -> list:
    """Each case of a handler, with the preset it runs on."""
    params = []
    for preset in PRESETS:
        suite = FILES / preset / "fulu" / "networking" / handler / "pyspec_tests"
        params += [
            pytest.param(preset, case, id=f"{preset}-{case.name}")
            for case in sorted(suite.iterdir())
        ]
    return params


def _meta(case: Path) -> dict:
    return YAML(typ="safe").load((case / "meta.yaml").read_text())


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*.yaml"))
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_counts():
    # Each preset has 11 cases of the first handler and 5 of the second.
    for handler, count in (("get_custody_groups", 11), ("compute_columns_for_custody_group", 5)):
        found = [case.values[0] for case in _cases(handler)]
        assert [found.count(preset) for preset in PRESETS] == [count, count], handler


@pytest.mark.parametrize(("preset", "case"), _cases("get_custody_groups"))
def test_get_custody_groups(preset, case):
    meta = _meta(case)
    node_id = int(meta["node_id"])
    groups = consensus.get_custody_groups(node_id, meta["custody_group_count"], preset)
    assert groups == meta["result"]


@pytest.mark.parametrize(("preset", "case"), _cases("compute_columns_for_custody_group"))
def test_compute_columns_for_custody_group(preset, case):
    meta = _meta(case)
    columns = consensus.compute_columns_for_custody_group(meta["custody_group"], preset)
    assert columns == meta["result"]


def test_too_many_groups():
    with raises(
        consensus.ConsensusError, "custody group count 129 exceeds the number of groups"
    ) as info:
        consensus.get_custody_groups(0, 129)
    assert info.value.code == 1


def test_group_out_of_range():
    with raises(
        consensus.ConsensusError, "custody group 128 is not below the number of groups"
    ) as info:
        consensus.compute_columns_for_custody_group(128)
    assert info.value.code == 2


def test_unknown_name():
    with raises(consensus.ConsensusError, "no configuration is named nonexistent") as info:
        consensus.compute_columns_for_custody_group(0, "nonexistent")
    assert info.value.code == 0


OUT_OF_RANGE = [-1, 2**64, 2**64 + 1]


@pytest.mark.parametrize(
    "value, message",
    [
        (-1, "can't convert negative int to unsigned"),
        (2**64, "int too big to convert"),
        (2**64 + 1, "int too big to convert"),
    ],
)
def test_native_rejects_out_of_range(value, message):
    # The extension raises instead of reducing the value modulo 2^64.
    with raises(OverflowError, message):
        _native.consensus_get_custody_groups("mainnet", bytes(32), value)
    with raises(OverflowError, message):
        _native.consensus_compute_columns_for_custody_group("mainnet", value)


def test_native_rejects_non_integer():
    with raises(TypeError, "an integer is required"):
        _native.consensus_get_custody_groups("mainnet", bytes(32), "4")  # ty: ignore[invalid-argument-type]
    with raises(TypeError, "an integer is required"):
        _native.consensus_compute_columns_for_custody_group("mainnet", "0")  # ty: ignore[invalid-argument-type]


@pytest.mark.parametrize("value", OUT_OF_RANGE)
def test_wrapper_rejects_out_of_range(value):
    with raises(OverflowError, "node_id or custody_group_count is out of range"):
        consensus.get_custody_groups(0, value)
    with raises(OverflowError, "custody_group is out of range"):
        consensus.compute_columns_for_custody_group(value)
