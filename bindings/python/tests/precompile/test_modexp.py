"""The MODEXP precompile against the examples of EIP-198 and the prices of EIP-2565 and EIP-7883."""

import pytest

from ethlib.precompiles import price, run

from .forks import since

# The examples and prices of EIP-198, EIP-2565 and EIP-7883.
#
# Files: EIPS/eip-198.md, EIPS/eip-2565.md, EIPS/eip-7883.md
# Repository: ethereum/EIPs
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445
# Licence: CC0-1.0

# Byzantium adds MODEXP, Berlin changes its price (EIP-2565), and Fusaka changes the price again
# and bounds the lengths (EIP-7883 and EIP-7823).
FORKS = since("byzantium")
EIP_198_FORKS = since("byzantium", "berlin")
EIP_2565_FORKS = since("berlin", "fusaka")
EIP_7883_FORKS = since("fusaka")

# The modulus of the first two examples of EIP-198.
P = 2**256 - 2**32 - 977


def word(value: int) -> bytes:
    return value.to_bytes(32, "big")


def call(base: bytes, exponent: bytes, modulus: bytes) -> bytes:
    """The call data for three operands, each with its length."""
    lengths = word(len(base)) + word(len(exponent)) + word(len(modulus))
    return lengths + base + exponent + modulus


# The worked examples of EIP-198, Specification.
EXAMPLE_1 = word(1) + word(32) + word(32) + bytes([3]) + word(P - 1) + word(P)
EXAMPLE_2 = word(0) + word(32) + word(32) + word(P - 1) + word(P)
EXAMPLE_3 = word(0) + word(32) + word(2**256 - 1) + word(2**256 - 2) + word(2**256 - 3)
EXAMPLE_4 = word(1) + word(2) + word(32) + bytes([3, 0xFF, 0xFF]) + word(2**255) + bytes([7])
EXAMPLE_5 = word(1) + word(2) + word(32) + bytes([3, 0xFF, 0xFF, 0x80])

# More gas than any of the examples costs, at any fork.
AMPLE_GAS = 10**6


@pytest.mark.parametrize("data, output", [
    # 3^(p - 1) mod p is 1, by Fermat's little theorem.
    (EXAMPLE_1, word(1)),
    # No byte is read as the base, so the base is 0.
    (EXAMPLE_2, word(0)),
    # The trailing byte 07 is ignored.
    (EXAMPLE_4, word(pow(3, 65535, 2**255))),
    # The 31 missing bytes of the modulus read as zeros, so the modulus is still 2^255.
    (EXAMPLE_5, word(pow(3, 65535, 2**255))),
    # Empty call data: every length is 0, and the output is empty.
    (b"", b""),
    # A zero modulus gives zero bytes, and 1 mod 1 is 0, on the length of the modulus.
    (word(0) + word(0) + word(1) + bytes([0]), bytes(1)),
    (word(0) + word(0) + word(1) + bytes([1]), bytes(1)),
    (word(0) + word(0) + word(2) + bytes([0, 1]), bytes(2)),
])
@pytest.mark.parametrize("fork", FORKS)
def test_examples(fork: str, data: bytes, output: bytes) -> None:
    assert run(fork, 0x05, data, AMPLE_GAS) == output


@pytest.mark.parametrize("fork, cost", [
    # The highest bit of the exponent p - 1 is bit 255, so 255 iterations at every fork.
    # EIP-198: the complexity of 32 bytes is 32^2, and the price is 1024 * 255 / 20.
    *((fork, 13056) for fork in EIP_198_FORKS),
    # EIP-2565: four 8-byte words give the complexity 4^2, and the price is 16 * 255 / 3.
    *((fork, 1360) for fork in EIP_2565_FORKS),
    # EIP-7883: 32 bytes have the complexity 16, and the price is 16 * 255.
    *((fork, 4080) for fork in EIP_7883_FORKS),
])
def test_example_1_price(fork: str, cost: int) -> None:
    assert price(fork, 0x05, EXAMPLE_1) == cost
    assert run(fork, 0x05, EXAMPLE_1, cost) == word(1)
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x05, EXAMPLE_1, cost - 1)


@pytest.mark.parametrize("gas", [0, 10**9])
@pytest.mark.parametrize("fork", EIP_7883_FORKS)
def test_example_3_length_too_large(fork: str, gas: int) -> None:
    # EIP-7823 bounds each length by 1024 bytes, before any gas is charged.
    with pytest.raises(ValueError, match="lengthTooLarge"):
        run(fork, 0x05, EXAMPLE_3, gas)


@pytest.mark.parametrize("fork", since("byzantium", "fusaka"))
def test_example_3_before_fusaka(fork: str) -> None:
    # Before EIP-7823, a modulus of 2^256 - 1 bytes is priced far above any gas, so the call
    # runs out of gas.
    assert price(fork, 0x05, EXAMPLE_3) > 2**64
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x05, EXAMPLE_3, 2**64 - 1)


@pytest.mark.parametrize("fork", since("frontier", "byzantium"))
def test_absent_before_byzantium(fork: str) -> None:
    with pytest.raises(ValueError, match="no precompile at address 5"):
        run(fork, 0x05, EXAMPLE_1, AMPLE_GAS)


@pytest.mark.parametrize("exponent, iterations", [
    # EIP-198: the index of the highest bit, "1 -> 0, 2 -> 1, 3 -> 1, 255 -> 7, 256 -> 8".
    # EIP-7883 raises the count to at least 1.
    (bytes([1]), 1), (bytes([2]), 1), (bytes([3]), 1), (bytes([255]), 7), (bytes([1, 0]), 8),
])
@pytest.mark.parametrize("fork", EIP_7883_FORKS)
def test_iteration_count(fork: str, exponent: bytes, iterations: int) -> None:
    # A 1024-byte modulus has the complexity 2 * (1024 / 8)^2, above the minimum price.
    assert price(fork, 0x05, call(b"", exponent, bytes(1024))) == 32768 * iterations


# The `modexp_nagydani_*` cases: the length of the base and of the modulus, and the exponent.
# Then the prices of EIP-198 and EIP-2565 (EIP-2565, Test Cases) and of EIP-7883 (EIP-7883,
# Test Cases).
NAGYDANI = [
    (64, bytes([2]), 204, 200, 500),
    (64, bytes([3]), 204, 200, 500),
    (64, bytes([1, 0, 1]), 3276, 341, 2048),
    (128, bytes([2]), 665, 200, 512),
    (128, bytes([3]), 665, 200, 512),
    (128, bytes([1, 0, 1]), 10649, 1365, 8192),
    (256, bytes([2]), 1894, 341, 2048),
    (256, bytes([3]), 1894, 341, 2048),
    (256, bytes([1, 0, 1]), 30310, 5461, 32768),
    (512, bytes([2]), 5580, 1365, 8192),
    (512, bytes([3]), 5580, 1365, 8192),
    (512, bytes([1, 0, 1]), 89292, 21845, 131072),
    (1024, bytes([2]), 17868, 5461, 32768),
    (1024, bytes([3]), 17868, 5461, 32768),
    (1024, bytes([1, 0, 1]), 285900, 87381, 524288),
]


@pytest.mark.parametrize("size, exponent, eip198, eip2565, eip7883", NAGYDANI)
@pytest.mark.parametrize("fork", FORKS)
def test_nagydani_prices(
    fork: str, size: int, exponent: bytes, eip198: int, eip2565: int, eip7883: int
) -> None:
    # Only the lengths and the exponent enter the price, so zero bytes stand in for the base and
    # the modulus of each case.
    if fork in EIP_198_FORKS:
        expected = eip198
    elif fork in EIP_2565_FORKS:
        expected = eip2565
    else:
        expected = eip7883
    assert price(fork, 0x05, call(bytes(size), exponent, bytes(size))) == expected
