"""The address of a private key, against the definition of the Yellow Paper."""

import json
import random
from pathlib import Path

import pytest
from py_ecc.secp256k1 import secp256k1 as reference

from ethlib.cryptography import secp256k1
from ethlib.cryptography.keccak import keccak256
from raising import raises

N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


# Appendix F of the Yellow Paper: the last 20 bytes of the Keccak-256 hash of `x || y`.
# `py_ecc` computes `d G` independently, and EthLib's Keccak-256 is pinned by its own vectors.
#
# File: Paper.tex
# Repository: ethereum/yellowpaper
# Commit: efc5f9a1f356cba376c978eedb63cb0363c2aa85
def expected_address(d: int) -> bytes:
    """The address of Appendix F, from an independent scalar multiplication."""
    x, y = reference.privtopub(d.to_bytes(32, "big"))
    return keccak256(x.to_bytes(32, "big") + y.to_bytes(32, "big"))[12:]


# The smallest and largest keys, then keys drawn with a fixed seed.
_rng = random.Random(5)
KEYS = [1, 2, N - 1] + [_rng.randrange(1, N) for _ in range(20)]


@pytest.mark.parametrize("d", KEYS)
def test_address(d: int) -> None:
    assert secp256k1.address(d.to_bytes(32, "big")) == expected_address(d)


def test_address_of_key_one() -> None:
    # The key 1 has the public key G, so its address is the hash of G: pin it byte for byte.
    assert secp256k1.address((1).to_bytes(32, "big")).hex() == (
        "7e5f4552091a69125d5dfcb7b8c2659029395bdf"
    )


def test_address_rejects_zero() -> None:
    with raises(ValueError, "private key is zero"):
        secp256k1.address(bytes(32))


def test_address_rejects_n() -> None:
    with raises(ValueError, "bad private key: not below the group order n"):
        secp256k1.address(N.to_bytes(32, "big"))


# The key-address test of ethereum/tests.
#
# File: BasicTests/keyaddrtest.json
# Repository: ethereum/tests
# Commit: c67e485ff8b5be9abc8ad15345ec21aa22e290d9
# Licence: MIT (keyaddr/README.md)
KEYADDR = json.loads((Path(__file__).resolve().parent / "keyaddr" / "keyaddrtest.json").read_text())


@pytest.mark.parametrize("case", KEYADDR, ids=lambda c: c["seed"])
def test_keyaddr(case: dict) -> None:
    # The field `sig_of_emptystring` is not read: the file does not name the hash it signs, and no
    # candidate hash recovers the address (keyaddr/README.md).
    assert len(KEYADDR) == 2
    assert secp256k1.address(bytes.fromhex(case["key"])).hex() == case["addr"]
