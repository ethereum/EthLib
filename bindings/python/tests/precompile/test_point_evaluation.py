"""The point evaluation precompile against the `verify_kzg_proof` vectors of this repository."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.precompiles import run
from raising import raises

from .forks import ends

# Each vector of `tests/cryptography/kzg/verify_kzg_proof` becomes a 192-byte call:
#
#     versioned_hash: 32 | z: 32 | y: 32 | commitment: 48 | proof: 48
#
# The versioned hash is `0x01`, then the last 31 bytes of SHA-256 of the commitment (EIP-4844).
#
# A proof that verifies gives the two words `FIELD_ELEMENTS_PER_BLOB` and `BLS_MODULUS`.
# A proof that fails, or an input that does not decode, makes the call fail.
# The test checks that the call fails with the error that names the reason.

# The fork that adds the precompile, dencun, and the latest fork: no fork in between changes it.
FORKS = ends("dencun")

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
    return (
        versioned_hash(commitment) + fields["z"] + fields["y"] + commitment + fields["proof"],
        data["output"],
    )


def test_found_vectors() -> None:
    assert len(CASES) == 122


# The error of the Lean specification for each kind of failing vector of the right length.
ERROR = {
    "invalid_commitment": "invalidCommitment",
    "invalid_z": "invalidFieldElement",
    "invalid_y": "invalidFieldElement",
    "invalid_proof": "invalidProof",
    "incorrect_proof": "proofRejected",
}


def error(variant: str) -> str:
    """The message of a failed call, from the variant of its error."""
    return (
        "EthLib.Execution.Evm.Precompiles.PrecompileError.pointEvaluation\n  "
        f"(EthLib.Execution.Evm.Precompiles.PointEvaluation.PointEvaluationError.{variant})"
    )


def expected_error(name: str, data: bytes) -> str:
    """The error of the Lean specification for a vector whose call fails."""
    if len(data) != 192:
        return f"invalidInputLength {len(data)}"
    (variant,) = [variant for kind, variant in ERROR.items() if f"_case_{kind}_" in name]
    return variant


@pytest.mark.parametrize("name", CASES)
@pytest.mark.parametrize("fork", FORKS)
def test_vector(fork: str, name: str) -> None:
    data, verifies = call_data(name)
    if verifies:
        assert run(fork, 0x0A, data, 50000) == SUCCESS
    else:
        with raises(ValueError, error(expected_error(name, data))):
            run(fork, 0x0A, data, 50000)


@pytest.mark.parametrize("fork", FORKS)
def test_versioned_hash_mismatch(fork: str) -> None:
    # Flip the version byte of a call whose proof verifies.
    data, _ = call_data("verify_kzg_proof_case_correct_proof_0_0")
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.pointEvaluation\n  "
            "(EthLib.Execution.Evm.Precompiles.PointEvaluation.PointEvaluationError.versionedHashMismatch)"
        ),
    ):
        run(fork, 0x0A, b"\x02" + data[1:], 50000)


@pytest.mark.parametrize("fork", FORKS)
def test_out_of_gas(fork: str) -> None:
    data, _ = call_data("verify_kzg_proof_case_correct_proof_0_0")
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.pointEvaluation\n  "
            "(EthLib.Execution.Evm.Precompiles.PointEvaluation.PointEvaluationError.outOfGas "
            "50000 49999)"
        ),
    ):
        run(fork, 0x0A, data, 49999)
    # The gas is checked before the call data is decoded.
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.pointEvaluation\n  "
            "(EthLib.Execution.Evm.Precompiles.PointEvaluation.PointEvaluationError.outOfGas "
            "50000 49999)"
        ),
    ):
        run(fork, 0x0A, bytes(192), 49999)


@pytest.mark.parametrize("size", [0, 191, 193])
@pytest.mark.parametrize("fork", FORKS)
def test_invalid_length(fork: str, size: int) -> None:
    with raises(ValueError, error(f"invalidInputLength {size}")):
        run(fork, 0x0A, bytes(size), 50000)
