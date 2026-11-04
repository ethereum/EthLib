"""Known answers of the SHA-256 precompile.

The messages and digests are the NIST vectors of `tests/sha256`.
The price is `60 + 12 * ceil(len / 32)`.
It comes from `GasCosts.PRECOMPILE_SHA256_BASE` and `GasCosts.PRECOMPILE_SHA256_PER_WORD`.

Repository: ethereum/execution-specs
Commit: e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e
Path: src/ethereum/forks/frontier/vm/gas.py
"""

import pytest

from ethlib.precompiles import sha256 as precompile
from sha256 import fixtures as F


def price(size: int) -> int:
    """The price worked out by hand: a base of 60, and 12 per started 32-byte word."""
    return 60 + 12 * ((size + 31) // 32)


def test_output_size() -> None:
    assert precompile.SHA256_PRECOMPILE_OUTPUT_BYTES == 32


@pytest.mark.parametrize("size, cost", [
    (0, 60), (1, 72), (31, 72), (32, 72), (33, 84), (64, 84), (65, 96), (1024, 444),
])
def test_gas_boundaries(size: int, cost: int) -> None:
    assert precompile.gas_cost(bytes(size)) == cost


@pytest.mark.parametrize("i", range(len(F.VECTORS)))
def test_exact_price(i: int) -> None:
    # Exactly the price succeeds, and returns the published digest.
    message, digest = F.VECTORS[i]
    assert precompile.gas_cost(message) == price(len(message))
    assert precompile.sha256(message, price(len(message))) == digest


@pytest.mark.parametrize("i", range(len(F.VECTORS)))
def test_one_gas_short(i: int) -> None:
    # One gas below the price runs out of gas.
    message, _ = F.VECTORS[i]
    with pytest.raises(ValueError, match="out of gas"):
        precompile.sha256(message, price(len(message)) - 1)


def test_surplus_gas() -> None:
    message, digest = F.VECTORS[0]
    assert precompile.sha256(message, 2**64 - 1) == digest


def test_rejects_gas_above_64_bits() -> None:
    with pytest.raises(OverflowError):
        precompile.sha256(b"", 2**64)


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        precompile.sha256("abc", 72)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        precompile.gas_cost("abc")  # type: ignore[arg-type]
