"""The embedded trusted setup matches the pinned file, lies in the subgroup, and its bases agree."""

import json
import re
from pathlib import Path

import pytest
from py_ecc import optimized_bls12_381
from py_ecc.bls.g2_primitives import G2_to_signature
from ruamel.yaml import YAML

import archives
from ethlib.cryptography import bls, kzg
from raising import raises

from . import fixtures

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
SETUP_ARCHIVE = "consensus-specs@36888ee8/trusted_setup_4096.json"

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


def _bit_reverse(index: int, bits: int) -> int:
    """The `bits`-bit reversal of `index`."""
    out = 0
    for _ in range(bits):
        out = (out << 1) | (index & 1)
        index >>= 1
    return out


def _roots_of_unity_brp() -> list[int]:
    """The roots of unity of the blob domain, in bit-reversed order."""
    width = kzg.FIELD_ELEMENTS_PER_BLOB
    omega = fixtures._root_of_unity(width)
    roots = [pow(omega, i, fixtures.BLS_MODULUS) for i in range(width)]
    return [roots[_bit_reverse(i, width.bit_length() - 1)] for i in range(width)]


def test_lagrange_sum_is_generator() -> None:
    # The Lagrange basis polynomials sum to 1, so the 4096 Lagrange points sum to [1]_1.
    lagrange = points("g1LagrangeHex")
    monomial = points("g1MonomialHex")
    total = lagrange[0]
    for point in lagrange[1:]:
        total = bls.g1_add(total, point)
    assert total == monomial[0]


@pytest.mark.parametrize("degree", (0, 1, 2, 3, 7, 64, 512, 2048, 4095))
def test_lagrange_matches_monomial_basis(degree: int) -> None:
    # Committing to the evaluations of X^degree in Lagrange form reproduces [tau^degree]_1.
    domain = _roots_of_unity_brp()
    blob = b"".join(pow(w, degree, fixtures.BLS_MODULUS).to_bytes(32, "big") for w in domain)
    assert kzg.blob_to_kzg_commitment(blob) == points("g1MonomialHex")[degree]


def test_monomial_pairing_powers() -> None:
    # Every G2 monomial step and sampled G1 monomial steps share the same secret tau.
    g1 = points("g1MonomialHex")
    g2 = points("g2MonomialHex")
    for i in range(len(g2) - 1):
        assert bls.pairing(g1[0], g2[i + 1]) == bls.pairing(g1[1], g2[i]), f"g2[{i}]"
    for i in (0, 1, 2, 63, 64, 511, 2047, 4094):
        assert bls.pairing(g1[i], g2[1]) == bls.pairing(g1[i + 1], g2[0]), f"g1[{i}]"


def test_anchored_at_generators() -> None:
    # Every check above is unchanged when the whole setup is scaled, so pin its first points.
    assert points("g1MonomialHex")[0] == fixtures.G1
    assert points("g2MonomialHex")[0] == G2_to_signature(optimized_bls12_381.G2)
