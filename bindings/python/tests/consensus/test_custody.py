"""The custody functions of EthLib against the Fulu networking vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
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
    ) as caught:
        consensus.get_custody_groups(0, 129)
    assert caught.value.code == 1


def test_group_out_of_range():
    with raises(
        consensus.ConsensusError, "custody group 128 is not below the number of groups"
    ) as caught:
        consensus.compute_columns_for_custody_group(128)
    assert caught.value.code == 2


def test_unknown_name():
    with raises(consensus.ConsensusError, "no configuration is named nonexistent") as caught:
        consensus.compute_columns_for_custody_group(0, "nonexistent")
    assert caught.value.code == 0


@pytest.mark.parametrize("value", [2**64, 2**64 + 1])
def test_count_out_of_range(value):
    # Lean reads a 64-bit number, and rejects a larger one instead of reducing it modulo 2^64.
    message = f"expected an int below {2**64}, got {value}"
    with raises(consensus.ConsensusError, message) as caught:
        consensus.get_custody_groups(0, value)
    assert caught.value.code == 0
    with raises(consensus.ConsensusError, message) as caught:
        consensus.compute_columns_for_custody_group(value)
    assert caught.value.code == 0


def test_node_id_out_of_range():
    with raises(
        consensus.ConsensusError, f"expected an int below {2**256}, got {2**256}"
    ) as caught:
        consensus.get_custody_groups(2**256, 4)
    assert caught.value.code == 0


def test_negative_numbers():
    with raises(ValueError, "cannot pass a negative int to Lean"):
        consensus.get_custody_groups(-1, 4)
    with raises(ValueError, "cannot pass a negative int to Lean"):
        consensus.compute_columns_for_custody_group(-1)


@pytest.mark.parametrize("value", ["4", True, False])
def test_non_integer(value):
    with raises(consensus.ConsensusError, "expected an int") as caught:
        consensus.get_custody_groups(0, value)
    assert caught.value.code == 0
    with raises(consensus.ConsensusError, "expected an int") as caught:
        consensus.get_custody_groups(value, 4)
    assert caught.value.code == 0
    with raises(consensus.ConsensusError, "expected an int") as caught:
        consensus.compute_columns_for_custody_group(value)
    assert caught.value.code == 0


@pytest.mark.parametrize(("preset", "case"), _cases("get_custody_groups"))
def test_get_custody_column_bits(preset, case):
    # Column `i` is bit `i mod 8` of byte `i / 8`, as in an SSZ bitvector.
    meta = _meta(case)
    node_id, count = int(meta["node_id"]), meta["custody_group_count"]
    bits = consensus.get_custody_column_bits(node_id, count, preset)
    columns = {
        column
        for group in consensus.get_custody_groups(node_id, count, preset)
        for column in consensus.compute_columns_for_custody_group(group, preset)
    }
    assert len(bits) == 16
    assert {i for i in range(128) if bits[i // 8] >> (i % 8) & 1} == columns


def test_custody_column_bits_of_too_many_groups():
    with raises(
        consensus.ConsensusError, "custody group count 129 exceeds the number of groups"
    ) as caught:
        consensus.get_custody_column_bits(0, 129)
    assert caught.value.code == 1
