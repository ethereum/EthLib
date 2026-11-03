"""Known answers of the IDENTITY precompile.

The price is `15 + 3 * ceil(len / 32)`, from `GasCosts.PRECOMPILE_IDENTITY_BASE` and
`GasCosts.PRECOMPILE_IDENTITY_PER_WORD` in execution-specs, `forks/amsterdam/vm/gas.py`.

The cases `identity_4_insufficient_gas` and `identity_4_exact_gas` of
`tests/frontier/identity_precompile/test_identity.py` in execution-specs, at commit
fd9298410ec7218838c8348f69c1eb633f1797dc, call the precompile with 32 bytes of `0xff`.
With 17 gas the call fails, and with 18 gas it succeeds.
"""

import pytest

from ethlib.precompiles import identity as precompile


def price(size: int) -> int:
    """The price worked out by hand: a base of 15, and 3 for each started 32-byte word."""
    return 15 + 3 * ((size + 31) // 32)


@pytest.mark.parametrize("size, cost", [
    (0, 15), (1, 18), (31, 18), (32, 18), (33, 21), (37, 21), (64, 21), (65, 24), (1024, 111),
])
def test_gas_boundaries(size: int, cost: int) -> None:
    assert precompile.gas_cost(bytes(size)) == cost


def test_execution_specs_exact_gas() -> None:
    data = b"\xff" * 32
    assert precompile.identity(data, 18) == data


def test_execution_specs_insufficient_gas() -> None:
    with pytest.raises(ValueError, match="out of gas: price 18, gas 17"):
        precompile.identity(b"\xff" * 32, 17)


SIZES = [0, 1, 31, 32, 33, 63, 64, 65, 1000]


def message(size: int) -> bytes:
    """Bytes `i % 251`, so that a reordered or truncated output fails the comparison."""
    return bytes(i % 251 for i in range(size))


@pytest.mark.parametrize("size", SIZES)
def test_exact_price(size: int) -> None:
    # Exactly the price succeeds, and returns the call data byte for byte.
    data = message(size)
    assert precompile.gas_cost(data) == price(size)
    out = precompile.identity(data, price(size))
    assert out == data and len(out) == size


@pytest.mark.parametrize("size", SIZES)
def test_one_gas_short(size: int) -> None:
    # One gas below the price runs out of gas.
    data = message(size)
    with pytest.raises(ValueError, match="out of gas"):
        precompile.identity(data, price(size) - 1)


def test_zero_gas() -> None:
    with pytest.raises(ValueError, match="out of gas: price 15, gas 0"):
        precompile.identity(b"", 0)


def test_surplus_gas() -> None:
    assert precompile.identity(b"\x00\x01\xfe\xff", 2**64 - 1) == b"\x00\x01\xfe\xff"


def test_rejects_gas_outside_64_bits() -> None:
    with pytest.raises(OverflowError):
        precompile.identity(b"", 2**64)
    with pytest.raises(OverflowError):
        precompile.identity(b"", -1)


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        precompile.identity(bytearray(b"abc"), 18)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        precompile.identity(b"abc", 18.0)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        precompile.gas_cost("abc")  # type: ignore[arg-type]
