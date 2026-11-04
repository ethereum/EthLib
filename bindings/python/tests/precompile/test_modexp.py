"""The MODEXP precompile against the examples of EIP-198 and the prices of EIP-7883."""

import pytest

from ethlib.precompiles import run
from ethlib.precompiles.modexp import gas_cost

# The examples and prices come from `EIPS/eip-198.md` and `EIPS/eip-7883.md` in `ethereum/EIPs`,
# at commit `0ce679f4654ba4d120c97113626f320475e22fa9`, under CC0-1.0.

# The modulus of the first two examples of EIP-198.
P = 2**256 - 2**32 - 977


def word(value: int) -> bytes:
    return value.to_bytes(32, "big")


def call(base: bytes, exponent: bytes, modulus: bytes) -> bytes:
    """The call data for three operands, each with its length."""
    lengths = word(len(base)) + word(len(exponent)) + word(len(modulus))
    return lengths + base + exponent + modulus


# The worked examples of EIP-198, Specification, with the price of EIP-7883.
EXAMPLE_1 = word(1) + word(32) + word(32) + bytes([3]) + word(P - 1) + word(P)
EXAMPLE_2 = word(0) + word(32) + word(32) + word(P - 1) + word(P)
EXAMPLE_3 = word(0) + word(32) + word(2**256 - 1) + word(2**256 - 2) + word(2**256 - 3)
EXAMPLE_4 = word(1) + word(2) + word(32) + bytes([3, 0xFF, 0xFF]) + word(2**255) + bytes([7])
EXAMPLE_5 = word(1) + word(2) + word(32) + bytes([3, 0xFF, 0xFF, 0x80])


@pytest.mark.parametrize("data, gas, output", [
    # 3^(p - 1) mod p is 1, by Fermat's little theorem. The price is 16 * 255.
    (EXAMPLE_1, 4080, word(1)),
    # No byte is read as the base, so the base is 0.
    (EXAMPLE_2, 4080, word(0)),
    # The trailing byte 07 is ignored.
    (EXAMPLE_4, 500, word(pow(3, 65535, 2**255))),
    # The 31 missing bytes of the modulus read as zeros, so the modulus is still 2^255.
    (EXAMPLE_5, 500, word(pow(3, 65535, 2**255))),
    # Empty call data: every length is 0, and the output is empty.
    (b"", 500, b""),
    # A zero modulus gives zero bytes, and 1 mod 1 is 0, on the length of the modulus.
    (word(0) + word(0) + word(1) + bytes([0]), 500, bytes(1)),
    (word(0) + word(0) + word(1) + bytes([1]), 500, bytes(1)),
    (word(0) + word(0) + word(2) + bytes([0, 1]), 500, bytes(2)),
])
def test_examples(data: bytes, gas: int, output: bytes) -> None:
    assert run(0x05, data, gas) == output


def test_example_1_one_gas_short() -> None:
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x05, EXAMPLE_1, 4079)


@pytest.mark.parametrize("gas", [0, 10**9])
def test_example_3_length_too_large(gas: int) -> None:
    # EIP-7823 bounds each length by 1024 bytes, before any gas is charged.
    with pytest.raises(ValueError, match="lengthTooLarge"):
        run(0x05, EXAMPLE_3, gas)


@pytest.mark.parametrize("exponent, iterations", [
    # EIP-198: the index of the highest bit, "1 -> 0, 2 -> 1, 3 -> 1, 255 -> 7, 256 -> 8".
    # EIP-7883 raises the count to at least 1.
    (bytes([1]), 1), (bytes([2]), 1), (bytes([3]), 1), (bytes([255]), 7), (bytes([1, 0]), 8),
])
def test_iteration_count(exponent: bytes, iterations: int) -> None:
    # A 1024-byte modulus has the complexity 2 * (1024 / 8)^2, above the minimum price.
    assert gas_cost(call(b"", exponent, bytes(1024))) == 32768 * iterations


@pytest.mark.parametrize("size, exponent, price", [
    # The column "EIP-7883 Pricing" of EIP-7883, Test Cases.
    (64, bytes([2]), 500), (64, bytes([3]), 500), (64, bytes([1, 0, 1]), 2048),
    (128, bytes([2]), 512), (128, bytes([3]), 512), (128, bytes([1, 0, 1]), 8192),
    (256, bytes([2]), 2048), (256, bytes([3]), 2048), (256, bytes([1, 0, 1]), 32768),
    (512, bytes([2]), 8192), (512, bytes([3]), 8192), (512, bytes([1, 0, 1]), 131072),
    (1024, bytes([2]), 32768), (1024, bytes([3]), 32768), (1024, bytes([1, 0, 1]), 524288),
])
def test_nagydani_prices(size: int, exponent: bytes, price: int) -> None:
    # The base and the modulus of each `modexp_nagydani_*` case have the same length.
    assert gas_cost(call(bytes(size), exponent, bytes(size))) == price
