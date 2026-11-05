"""The points of the embedded trusted setup lie in the subgroup of order r."""

import re
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.cryptography import bls

ROOT = Path(__file__).resolve().parents[4]
DATA = ROOT / "EthLib" / "Cryptography" / "Kzg" / "TrustedSetupData.lean"
NOT_IN_G1 = (
    ROOT
    / "tests"
    / "cryptography"
    / "bls"
    / "deserialization_G1"
    / "deserialization_fails_not_in_G1"
    / "data.yaml"
)

# The arrays of the embedded setup, with their lengths in the KZG constants.
ARRAYS = {"g1LagrangeHex": 4096, "g1MonomialHex": 4096, "g2MonomialHex": 65}


def points(name: str) -> list[bytes]:
    """The compressed points of one array of the embedded setup, read from the Lean file."""
    match = re.search(rf"def {name} : Array String := #\[(.*?)\]", DATA.read_text(), re.S)
    assert match, f"no array {name} in {DATA}"
    return [bytes.fromhex(h) for h in re.findall(r'"([0-9a-f]+)"', match.group(1))]


@pytest.mark.parametrize("name", ARRAYS)
def test_length(name: str) -> None:
    assert len(points(name)) == ARRAYS[name]


@pytest.mark.parametrize("name", ARRAYS)
def test_in_subgroup(name: str) -> None:
    # Decoding checks the curve and the subgroup, and gives back the canonical encoding.
    decode = bls.decode_g2 if name.startswith("g2") else bls.decode_g1
    for i, point in enumerate(points(name)):
        assert decode(point) == point, f"{name}[{i}]"


def test_not_in_subgroup_rejected() -> None:
    # A point on the curve outside the subgroup fails, so the check above is not empty.
    pubkey = YAML(typ="safe", pure=True).load(NOT_IN_G1.read_text())["input"]["pubkey"]
    with pytest.raises(bls.BlsError, match="point not in subgroup") as error:
        bls.decode_g1(bytes.fromhex(pubkey))
    assert error.value.code == 7
