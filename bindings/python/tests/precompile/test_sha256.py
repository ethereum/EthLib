"""Known answers of the SHA-256 precompile, on the NIST vectors of `tests/sha256`."""

import pytest

from ethlib.precompiles import price, run
from sha256 import fixtures as F

from .forks import FORKS, ends

ADDRESS = 0x02


def cost(size: int) -> int:
    """The price of Appendix E of the Yellow Paper: 60, and 12 per started 32-byte word."""
    return 60 + 12 * ((size + 31) // 32)


@pytest.mark.parametrize(
    "size, expected",
    [
        (0, 60),
        (1, 72),
        (31, 72),
        (32, 72),
        (33, 84),
        (64, 84),
        (65, 96),
        (1024, 444),
    ],
)
@pytest.mark.parametrize("fork", FORKS)
def test_gas_boundaries(fork: str, size: int, expected: int) -> None:
    assert price(fork, ADDRESS, bytes(size)) == expected


@pytest.mark.parametrize("i", range(len(F.VECTORS)))
@pytest.mark.parametrize("fork", ends("frontier"))
def test_exact_price(fork: str, i: int) -> None:
    # Exactly the price succeeds, and returns the published digest.
    message, digest = F.VECTORS[i]
    assert price(fork, ADDRESS, message) == cost(len(message))
    assert run(fork, ADDRESS, message, cost(len(message))) == digest


@pytest.mark.parametrize("i", range(len(F.VECTORS)))
@pytest.mark.parametrize("fork", ends("frontier"))
def test_one_gas_short(fork: str, i: int) -> None:
    # One gas below the price runs out of gas.
    message, _ = F.VECTORS[i]
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, ADDRESS, message, cost(len(message)) - 1)


def test_surplus_gas() -> None:
    message, digest = F.VECTORS[0]
    assert run("bpo2", ADDRESS, message, 2**64 - 1) == digest
