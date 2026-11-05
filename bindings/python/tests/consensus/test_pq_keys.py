"""The containers of the EIP-8450 key registry against vectors of an independent SSZ."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "pq_keys"

CONTAINERS = {
    "PQKeyMaterial",
    "PQKeyRegistration",
    "PQKeyPossession",
    "SignedPQKeyRegistration",
    "ValidatorPQKeyMaterial",
    "ValidatorPQKeyChangeEpochs",
    "BuilderPQKeyMaterial",
    "BuilderPQKeyChangeEpochs",
    "PQKeyRegistrations",
}


def _cases() -> list:
    """Every case, as its container and directory."""
    return [
        (case.parent.parent.name, case.parent)
        for case in sorted((FILES / "ssz").rglob("data.yaml"))
    ]


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    pinned = {
        path
        for path in FILES.rglob("*")
        if path.is_file() and path.name not in ("SHA256SUMS", "README.md")
    }
    assert {FILES / name for _, name in entries} == pinned
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_every_container_has_cases():
    assert {container for container, _ in _cases()} == CONTAINERS


@pytest.mark.parametrize(
    "container, case",
    _cases(),
    ids=lambda value: value.relative_to(FILES).as_posix() if isinstance(value, Path) else None,
)
def test_case(container, case):
    data = YAML(typ="safe").load((case / "data.yaml").read_text())
    serialized = bytes.fromhex(data["serialized"].removeprefix("0x"))
    if data["root"] is None:
        with pytest.raises(SszError):
            consensus.pq_keys_ssz(container, serialized)
        return
    root, encoded = consensus.pq_keys_ssz(container, serialized)
    assert "0x" + root.hex() == data["root"]
    assert encoded == serialized


def test_unknown_container_is_rejected():
    with pytest.raises(SszError):
        consensus.pq_keys_ssz("BeaconState", b"")
