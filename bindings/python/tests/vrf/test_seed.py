"""Test-vector generators: `secret` and `evaluate`, the leaf secrets and outputs of a seed."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import keccak, vrf

from . import fixtures as F

# The secret and the output at each index, by the name of the index.
CASES = {
    "zero": (0, F.SECRET_ZERO, F.OUTPUT_SEED_ZERO),
    "last": (0xFFFF_FFFF, F.SECRET_LAST, F.OUTPUT_SEED_LAST),
}


@pytest.mark.parametrize("name", CASES)
def test_secret(name: str) -> None:
    index, secret, _ = CASES[name]
    assert vrf.secret(F.SEED, index) == secret
    write_case(
        "vrf",
        "secret",
        f"secret_{name}",
        {
            "input": {"seed": hex_str(F.SEED), "index": index},
            "output": hex_str(secret),
        },
    )


@pytest.mark.parametrize("name", CASES)
def test_evaluate(name: str) -> None:
    index, _, output = CASES[name]
    assert vrf.evaluate(F.SEED, index) == output
    write_case(
        "vrf",
        "evaluate",
        f"evaluate_{name}",
        {
            "input": {"seed": hex_str(F.SEED), "index": index},
            "output": hex_str(output),
        },
    )


@pytest.mark.parametrize("index", [0, 1, 0x0102_0304, 0xFFFF_FFFF])
def test_secret_reads_index_little_endian(index: int) -> None:
    # The secret hashes the prefix, the seed, then the index on 4 bytes, least significant first.
    expected = keccak.keccak256(b"PQ_VRF_SECRET" + F.SEED + index.to_bytes(4, "little"))
    assert vrf.secret(F.SEED, index) == expected


def test_rejects_bad_arguments() -> None:
    # The seed is exactly 32 bytes, and the index is below 2^32.
    with pytest.raises(ValueError, match="seed: expected 32 bytes, got 31"):
        vrf.secret(F.SEED[:31], 0)
    with pytest.raises(OverflowError):
        vrf.evaluate(F.SEED, 1 << 32)
