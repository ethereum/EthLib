"""The upgrade of Fulu attestations and attester slashings to Gloas, on the ssz_static vectors."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "ssz_static"

# The containers whose Gloas form replaces their lists with progressive lists.
UPGRADED = ("Attestation", "IndexedAttestation", "AttesterSlashing")


def _cases() -> list:
    """Every vendored Fulu case of an upgraded container, as its preset, container and directory."""
    cases = []
    for preset_dir in sorted(path for path in FILES.iterdir() if path.is_dir()):
        for container in UPGRADED:
            base = preset_dir / "fulu" / "ssz_static" / container
            for case in sorted(base.glob("*/case_*")):
                cases.append((preset_dir.name, container, case))
    return cases


def test_cases_cover_each_container():
    assert {container for _, container, _ in _cases()} == set(UPGRADED)


@pytest.mark.parametrize(
    "preset, container, case",
    _cases(),
    ids=lambda value: value.relative_to(FILES).as_posix() if isinstance(value, Path) else None,
)
def test_upgrade_keeps_the_bytes_and_changes_the_root(preset, container, case):
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    fulu_root = YAML(typ="safe").load((case / "roots.yaml").read_text())["root"]
    root, upgraded = consensus.upgrade_operation(preset, container, data)
    # A progressive list or container encodes as the type it replaces, by EIP-7916 and EIP-7495.
    # So an upgrade that keeps every field and element keeps the bytes.
    assert upgraded == data
    # Its root does change: a progressive list and a progressive container merkleize otherwise.
    assert "0x" + root.hex() != fulu_root
    assert (root, upgraded) == consensus.ssz_static(preset, FORKS["gloas"], container, upgraded)


@pytest.mark.parametrize(
    "container, error",
    [
        # The aggregation bits of this case take its last byte, so they are left with none.
        ("Attestation", "emptyEncoding"),
        # The indices then end with 7 of the 8 bytes of a validator index.
        ("IndexedAttestation", "scopeUndivided 79 8"),
        ("AttesterSlashing", "scopeUndivided 63 8"),
    ],
)
def test_truncated_input_is_rejected(container, error):
    case = FILES / "mainnet" / "fulu" / "ssz_static" / container / "ssz_random" / "case_0"
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    with raises(SszError, f"input rejected: EthLib.Serialization.Ssz.Err.{error}"):
        consensus.upgrade_operation("mainnet", container, data[:-1])


def test_indices_above_the_fulu_limit_are_rejected():
    # The minimal preset bounds the indices at 2048 * 4 = 8192 at Fulu, and Gloas has no bound.
    # The fixed part is the offset of the indices, the data of 128 bytes and the signature of 96.
    data = (228).to_bytes(4, "little") + bytes(224) + bytes(8 * 8193)
    consensus.ssz_static("minimal", FORKS["gloas"], "IndexedAttestation", data)
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err.overLimit 8192 8193"):
        consensus.upgrade_operation("minimal", "IndexedAttestation", data)


def test_indices_at_the_fulu_limit_are_kept():
    data = (228).to_bytes(4, "little") + bytes(224) + bytes(8 * 8192)
    _, upgraded = consensus.upgrade_operation("minimal", "IndexedAttestation", data)
    assert upgraded == data


@pytest.mark.parametrize("container", ["SingleAttestation", "AttestationData", "NoSuchContainer"])
def test_other_containers_have_no_upgrade(container):
    with raises(SszError, f"no upgrade of {container} to Gloas"):
        consensus.upgrade_operation("mainnet", container, b"")


def test_unknown_preset_is_rejected():
    with raises(SszError, "no preset is named testnet"):
        consensus.upgrade_operation("testnet", "Attestation", b"")
