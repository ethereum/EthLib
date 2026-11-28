"""The MODEXP precompile against its EIPs and the EIP-7883 vectors of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.precompiles import price, run
from raising import raises

from .forks import since

# The examples and prices of EIP-198, EIP-2565 and EIP-7883.
#
# Files: EIPS/eip-198.md, EIPS/eip-2565.md, EIPS/eip-7883.md
# Repository: ethereum/EIPs
# Commit: b055feec322fbc37e9d77a393a50b3ff56b31c92
# Licence: CC0-1.0

# Byzantium adds MODEXP, and Berlin changes its price (EIP-2565).
# Fusaka changes the price again and bounds the lengths (EIP-7883 and EIP-7823).
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


@pytest.mark.parametrize(
    "data, output",
    [
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
    ],
)
@pytest.mark.parametrize("fork", FORKS)
def test_examples(fork: str, data: bytes, output: bytes) -> None:
    assert run(fork, 0x05, data, AMPLE_GAS) == output


@pytest.mark.parametrize(
    "fork, cost",
    [
        # The highest bit of the exponent p - 1 is bit 255, so 255 iterations at every fork.
        # EIP-198: the complexity of 32 bytes is 32^2, and the price is 1024 * 255 / 20.
        *((fork, 13056) for fork in EIP_198_FORKS),
        # EIP-2565: four 8-byte words give the complexity 4^2, and the price is 16 * 255 / 3.
        *((fork, 1360) for fork in EIP_2565_FORKS),
        # EIP-7883: 32 bytes have the complexity 16, and the price is 16 * 255.
        *((fork, 4080) for fork in EIP_7883_FORKS),
    ],
)
def test_example_1_price(fork: str, cost: int) -> None:
    assert price(fork, 0x05, EXAMPLE_1) == cost
    assert run(fork, 0x05, EXAMPLE_1, cost) == word(1)
    with raises(
        ValueError,
        "EthLib.Execution.Evm.Precompiles.PrecompileError.modexp "
        "(EthLib.Execution.Evm.Precompiles.Modexp.ModexpError.outOfGas "
        f"(cost := {cost}) (gas := {cost - 1}))",
    ):
        run(fork, 0x05, EXAMPLE_1, cost - 1)


@pytest.mark.parametrize("gas", [0, 10**9])
@pytest.mark.parametrize("fork", EIP_7883_FORKS)
def test_example_3_length_too_large(fork: str, gas: int) -> None:
    # EIP-7823 bounds each length by 1024 bytes, before any gas is charged.
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.modexp "
            "(EthLib.Execution.Evm.Precompiles.Modexp.ModexpError.lengthTooLarge "
            "(field := EthLib.Execution.Evm.Precompiles.Modexp.LengthField.modulus) "
            "(length := "
            "115792089237316195423570985008687907853269984665640564039457584007913129639935))"
        ),
    ):
        run(fork, 0x05, EXAMPLE_3, gas)


# The prices of example 3: a modulus of x = 2^256 - 1 bytes, and an exponent of 2^256 - 2.
# The highest bit of the exponent has the index 255.
# EIP-198: mult_complexity(x) = x^2 // 16 + 480 * x - 199680 above 1024 bytes, times 255, over 20.
# EIP-2565: ceil(x / 8)^2, times 255, over 3, and at least 200.
EXAMPLE_3_LENGTH = 2**256 - 1
EXAMPLE_3_EIP_198_PRICE = (EXAMPLE_3_LENGTH**2 // 16 + 480 * EXAMPLE_3_LENGTH - 199680) * 255 // 20
EXAMPLE_3_EIP_2565_PRICE = max(200, ((EXAMPLE_3_LENGTH + 7) // 8) ** 2 * 255 // 3)


@pytest.mark.parametrize("fork", since("byzantium", "fusaka"))
def test_example_3_before_fusaka(fork: str) -> None:
    # Before EIP-7823, a modulus of 2^256 - 1 bytes is priced far above any gas.
    # So the call runs out of gas.
    assert price(fork, 0x05, EXAMPLE_3) > 2**64
    cost = EXAMPLE_3_EIP_198_PRICE if fork in EIP_198_FORKS else EXAMPLE_3_EIP_2565_PRICE
    with raises(
        ValueError,
        "EthLib.Execution.Evm.Precompiles.PrecompileError.modexp "
        "(EthLib.Execution.Evm.Precompiles.Modexp.ModexpError.outOfGas "
        f"(cost := {cost}) (gas := {2**64 - 1}))",
    ):
        run(fork, 0x05, EXAMPLE_3, 2**64 - 1)


# Exponent lengths that no call could pay to read: 2^32 bytes, and the largest 32-byte length.
HUGE_EXPONENT_LENGTHS = [2**32, 2**256 - 1]


@pytest.mark.parametrize("length", HUGE_EXPONENT_LENGTHS)
@pytest.mark.parametrize(
    "fork, cost",
    [
        # EIP-198: an empty base and modulus have the complexity 0, so the price is 0.
        *((fork, 0) for fork in EIP_198_FORKS),
        # EIP-2565: no 8-byte word gives the complexity 0, raised to the least price, 200.
        *((fork, 200) for fork in EIP_2565_FORKS),
    ],
)
def test_empty_base_and_modulus_before_fusaka(fork: str, cost: int, length: int) -> None:
    # Before EIP-7823, the call is cheap whatever the exponent length, and returns nothing.
    data = word(0) + word(length) + word(0)
    assert price(fork, 0x05, data) == cost
    assert run(fork, 0x05, data, cost) == b""


@pytest.mark.parametrize("length", HUGE_EXPONENT_LENGTHS)
@pytest.mark.parametrize("fork", EIP_7883_FORKS)
def test_empty_base_and_modulus_from_fusaka(fork: str, length: int) -> None:
    # EIP-7823, from Fusaka like EIP-7883, rejects the exponent length before any gas is charged.
    with raises(
        ValueError,
        "EthLib.Execution.Evm.Precompiles.PrecompileError.modexp "
        "(EthLib.Execution.Evm.Precompiles.Modexp.ModexpError.lengthTooLarge "
        "(field := EthLib.Execution.Evm.Precompiles.Modexp.LengthField.exponent) "
        f"(length := {length}))",
    ):
        run(fork, 0x05, word(0) + word(length) + word(0), 2**64 - 1)


@pytest.mark.parametrize("fork", since("frontier", "byzantium"))
def test_absent_before_byzantium(fork: str) -> None:
    with raises(ValueError, f"no precompile at address 5 at fork {fork}"):
        run(fork, 0x05, EXAMPLE_1, AMPLE_GAS)


@pytest.mark.parametrize(
    "exponent, iterations",
    [
        # EIP-198: the index of the highest bit, "1 -> 0, 2 -> 1, 3 -> 1, 255 -> 7, 256 -> 8".
        # EIP-7883 raises the count to at least 1.
        (bytes([1]), 1),
        (bytes([2]), 1),
        (bytes([3]), 1),
        (bytes([255]), 7),
        (bytes([1, 0]), 8),
    ],
)
@pytest.mark.parametrize("fork", EIP_7883_FORKS)
def test_iteration_count(fork: str, exponent: bytes, iterations: int) -> None:
    # A 1024-byte modulus has the complexity 2 * (1024 / 8)^2, above the minimum price.
    assert price(fork, 0x05, call(b"", exponent, bytes(1024))) == 32768 * iterations


# The `modexp_nagydani_*` cases: the length of the base and of the modulus, and the exponent.
# Then the prices of EIP-198 and EIP-2565 (EIP-2565, Test Cases).
# Then the price of EIP-7883 (EIP-7883, Test Cases).
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
    # Only the lengths and the exponent enter the price.
    # So zero bytes stand in for the base and the modulus of each case.
    if fork in EIP_198_FORKS:
        expected = eip198
    elif fork in EIP_2565_FORKS:
        expected = eip2565
    else:
        expected = eip7883
    assert price(fork, 0x05, call(bytes(size), exponent, bytes(size))) == expected


# The MODEXP calls of the EIP-7883 tests, with their outputs and their prices.
# They include exponents of 33 to 216 bytes and operands of 1024 bytes.
#
# File: tests/osaka/eip7883_modexp_gas_increase/vector/vectors.json
# Repository: ethereum/execution-specs
# Commit: 391d8a05d5cb182542ac7e7330c858b6ee03f990
# Licence: CC0-1.0
VECTORS = json.loads(
    (Path(__file__).resolve().parent / "execution_specs" / "modexp_vectors.json").read_text()
)


def eip_price(data: bytes, eip7883: bool) -> int:
    """The price of a call by the formula of EIP-2565, or of EIP-7883 when `eip7883` is set."""
    base, exponent, modulus = (
        int.from_bytes(data[i : i + 32].ljust(32, b"\0"), "big") for i in (0, 32, 64)
    )
    head_bytes = data[96 + base : 96 + base + min(32, exponent)].ljust(min(32, exponent), b"\0")
    head = int.from_bytes(head_bytes, "big")
    # EIP-198: the index of the highest bit of the head, plus 8 per exponent byte past 32.
    # EIP-7883 doubles the 8, raises the complexity and the least price, and drops the divisor.
    per_byte = 16 if eip7883 else 8
    iterations = max(head.bit_length() - 1, 0) + per_byte * max(exponent - 32, 0)
    words = (max(base, modulus) + 7) // 8
    if eip7883:
        complexity = 16 if max(base, modulus) <= 32 else 2 * words**2
        return max(500, complexity * max(iterations, 1))
    return max(200, words**2 * max(iterations, 1) // 3)


@pytest.mark.parametrize("vector", VECTORS, ids=[v["Name"] for v in VECTORS])
def test_execution_specs_vector_prices(vector: dict) -> None:
    # The prices of the file agree with the formulas of the EIPs.
    data = bytes.fromhex(vector["Input"])
    assert eip_price(data, eip7883=False) == vector["GasOld"]
    assert eip_price(data, eip7883=True) == vector["GasNew"]


@pytest.mark.parametrize("vector", VECTORS, ids=[v["Name"] for v in VECTORS])
@pytest.mark.parametrize("fork", (*EIP_2565_FORKS, *EIP_7883_FORKS))
def test_execution_specs_vectors(fork: str, vector: dict) -> None:
    data = bytes.fromhex(vector["Input"])
    cost = vector["GasOld"] if fork in EIP_2565_FORKS else vector["GasNew"]
    assert price(fork, 0x05, data) == cost
    assert run(fork, 0x05, data, cost) == bytes.fromhex(vector["Expected"])


def eip198_price(length: int) -> int:
    """The EIP-198 price of a base of `length` bytes, an empty exponent and an empty modulus."""
    if length <= 64:
        complexity = length**2
    elif length <= 1024:
        complexity = length**2 // 4 + 96 * length - 3072
    else:
        complexity = length**2 // 16 + 480 * length - 199680
    return complexity // 20


def eip2565_price(length: int) -> int:
    """The EIP-2565 price of a base of `length` bytes, an empty exponent and an empty modulus."""
    return max(200, ((length + 7) // 8) ** 2 // 3)


@pytest.mark.parametrize(
    "length, at_least_2_64",
    [
        # 2^33 bytes is not enough: at Berlin it costs (2^30)^2 / 3, below 2^64.
        (2**33, False),
        # From 2^37 bytes, the price is at least 2^64 at every fork before Fusaka.
        (2**37, True),
        (2**64, True),
        (2**256 - 1, True),
    ],
)
@pytest.mark.parametrize("fork", since("byzantium", "fusaka"))
def test_huge_base_price(fork: str, length: int, at_least_2_64: bool) -> None:
    # An empty exponent has one iteration, so the price is the complexity over the divisor.
    data = word(length) + word(0) + word(0)
    cost = eip198_price(length) if fork in EIP_198_FORKS else eip2565_price(length)
    assert price(fork, 0x05, data) == cost
    assert (cost >= 2**64) == at_least_2_64
