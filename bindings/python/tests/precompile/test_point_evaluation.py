"""The point evaluation precompile against the `verify_kzg_proof` vectors of this repository.

Each vector of `tests/cryptography/kzg/verify_kzg_proof` becomes a 192-byte call:

    versioned_hash: 32 | z: 32 | y: 32 | commitment: 48 | proof: 48

The versioned hash is `0x01` followed by the last 31 bytes of SHA-256 of the commitment, as in EIP-4844.

A proof that verifies gives the two words `FIELD_ELEMENTS_PER_BLOB` and `BLS_MODULUS`.
A proof that fails, or an input that does not decode, makes the call fail.
"""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.precompiles import run

VECTORS = Path(__file__).parents[4] / "tests" / "cryptography" / "kzg" / "verify_kzg_proof"

CASES = sorted(path.name for path in VECTORS.iterdir() if path.is_dir())

BLS_MODULUS = 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001

SUCCESS = (4096).to_bytes(32, "big") + BLS_MODULUS.to_bytes(32, "big")


def versioned_hash(commitment: bytes) -> bytes:
    return b"\x01" + hashlib.sha256(commitment).digest()[1:]


def call_data(name: str) -> tuple[bytes, bool | None]:
    """The call data built from the vector, and whether its proof verifies."""
    data = YAML(typ="safe").load((VECTORS / name / "data.yaml").read_text())
    fields = {key: bytes.fromhex(value[2:]) for key, value in data["input"].items()}
    commitment = fields["commitment"]
    return (versioned_hash(commitment) + fields["z"] + fields["y"] + commitment + fields["proof"],
            data["output"])


def test_found_vectors() -> None:
    assert len(CASES) == 122


@pytest.mark.parametrize("name", CASES)
def test_vector(name: str) -> None:
    data, verifies = call_data(name)
    if verifies:
        assert run(0x0A, data, 50000) == SUCCESS
    else:
        with pytest.raises(ValueError):
            run(0x0A, data, 50000)


def test_versioned_hash_mismatch() -> None:
    # Flip the version byte of a call whose proof verifies.
    data, _ = call_data("verify_kzg_proof_case_correct_proof_0_0")
    with pytest.raises(ValueError, match="versionedHashMismatch"):
        run(0x0A, b"\x02" + data[1:], 50000)


def test_out_of_gas() -> None:
    data, _ = call_data("verify_kzg_proof_case_correct_proof_0_0")
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x0A, data, 49999)


@pytest.mark.parametrize("size", [0, 191, 193])
def test_invalid_length(size: int) -> None:
    with pytest.raises(ValueError, match="invalidInputLength"):
        run(0x0A, bytes(size), 50000)
