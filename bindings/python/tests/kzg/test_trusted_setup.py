"""The points of the embedded trusted setup match the pinned setup file and lie in the subgroup."""

import json
import re
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib.cryptography import bls
from raising import raises

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

# The setup file of the mainnet presets, from which the embedded setup was taken.
SETUP_ARCHIVE = "consensus-specs@aa16bb4c/trusted_setup_4096.json"

# The list of the setup file that each array of the embedded setup holds.
FILE_LISTS = {
    "g1LagrangeHex": "g1_lagrange",
    "g1MonomialHex": "g1_monomial",
    "g2MonomialHex": "g2_monomial",
}


def points(name: str) -> list[bytes]:
    """The compressed points of one array of the embedded setup, read from the Lean file."""
    match = re.search(rf"def {name} : Array String := #\[(.*?)\]", DATA.read_text(), re.S)
    assert match, f"no array {name} in {DATA}"
    return [bytes.fromhex(h) for h in re.findall(r'"([0-9a-f]+)"', match.group(1))]


@pytest.mark.parametrize("name", ARRAYS)
def test_length(name: str) -> None:
    assert len(points(name)) == ARRAYS[name]


def setup_file() -> dict[str, list[str]]:
    """The lists of the pinned setup file, by their keys."""
    return json.loads(archives.download(SETUP_ARCHIVE).read_bytes())


@pytest.mark.archive(SETUP_ARCHIVE)
def test_setup_file_lists() -> None:
    # The file holds the three lists and nothing else, so no list of it goes unchecked.
    assert set(setup_file()) == set(FILE_LISTS.values())


@pytest.mark.archive(SETUP_ARCHIVE)
@pytest.mark.parametrize("name", ARRAYS)
def test_matches_setup_file(name: str) -> None:
    # The file writes each point as hex with the prefix 0x.
    listed = setup_file()[FILE_LISTS[name]]
    assert all(point.startswith("0x") for point in listed)
    assert points(name) == [bytes.fromhex(point[2:]) for point in listed]


def test_header_names_pinned_digest() -> None:
    # The header of the embedded setup gives the SHA-256 of the file that the test reads.
    pin = archives.fetch_archives.load(archives.REPO)[SETUP_ARCHIVE]
    assert f"SHA-256 `{pin.sha256}`" in DATA.read_text()


@pytest.mark.parametrize("name", ARRAYS)
def test_in_subgroup(name: str) -> None:
    # Decoding checks the curve and the subgroup, and gives back the canonical encoding.
    decode = bls.decode_g2 if name.startswith("g2") else bls.decode_g1
    for i, point in enumerate(points(name)):
        assert decode(point) == point, f"{name}[{i}]"


def test_not_in_subgroup_rejected() -> None:
    # A point on the curve outside the subgroup fails, so the check above is not empty.
    pubkey = YAML(typ="safe", pure=True).load(NOT_IN_G1.read_text())["input"]["pubkey"]
    with raises(bls.BlsError, "point not in subgroup") as error:
        bls.decode_g1(bytes.fromhex(pubkey))
    assert error.value.code == 7
