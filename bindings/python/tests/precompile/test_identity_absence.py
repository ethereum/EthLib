"""IDENTITY and the addresses without a precompile, against the cases of execution-specs."""

# The IDENTITY cases are the precompile calls of three tests in these two files.
#
# File: tests/frontier/identity_precompile/test_identity.py
# File: tests/frontier/identity_precompile/test_identity_returndatasize.py
#
# The absence cases are those of `test_precompile_absence`.
#
# File: tests/frontier/precompiles/test_precompile_absence.py
#
# Repository: ethereum/execution-specs
# Commit: e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e
# Licence: CC0-1.0
#
# The cases were read from the `pytest.param` lists of those files, without running anything.

import pytest

from ethlib.errors import PrecompileError
from ethlib.precompiles import price, run

from .forks import since

IDENTITY = 0x04


def word(value: int) -> bytes:
    return value.to_bytes(32, "big")


ONES = word(2**256 - 1)

# Each case: its id, the call data, the gas that the call passes, and whether the call succeeds.
# A test stores the words of its tuple in memory from offset 0, then passes `args_size` bytes.
# None of these calls sends value, so the precompile gets the gas of the call, with no stipend.
CALLS = [
    ("identity_0", word(1), 0xFF, True),
    ("identity_1", b"", 0x1F4, True),
    # 0x25 = 37 bytes: the word 0xF34578907F, then 5 zero bytes of fresh memory.
    ("identity_2", word(0xF34578907F) + bytes(5), 0x1F4, True),
    ("identity_4", ONES, 0x64, True),
    ("identity_4_insufficient_gas", ONES, 0x11, False),
    ("identity_4_exact_gas", ONES, 0x12, True),
    # 0xF4240 = 1,000,000 bytes, of which only the first word was written.
    ("identity_5", ONES + bytes(0xF4240 - 32), 0x258, False),
    ("identity_6", ONES, 0x258, True),
]

# The price of each call data length of the cases, from Appendix E of the Yellow Paper:
# 15 gas, and 3 for each word or part of a word.
PRICES = {0: 15, 32: 18, 37: 21, 0xF4240: 93_765}

# The tests of these files run from Byzantium on.
FORKS = since("byzantium")


@pytest.mark.parametrize("fork", FORKS)
@pytest.mark.parametrize(
    ("data", "gas", "succeeds"), [c[1:] for c in CALLS], ids=[c[0] for c in CALLS]
)
def test_identity_call(fork: str, data: bytes, gas: int, succeeds: bool) -> None:
    assert price(fork, IDENTITY, data) == PRICES[len(data)]
    if succeeds:
        assert run(fork, IDENTITY, data, gas) == data
    else:
        with pytest.raises(PrecompileError) as error:
            run(fork, IDENTITY, data, gas)
        assert error.value.code != 0


@pytest.mark.parametrize("fork", FORKS)
@pytest.mark.parametrize("size", [0, 16, 32])
def test_identity_return_size(fork: str, size: int) -> None:
    # The return data has the size of the input, whatever room the caller gives it.
    data = bytes.fromhex("112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00")[:size]
    assert run(fork, IDENTITY, data, 10**6) == data


# The precompiles that execution-specs gives each fork, in its fork definitions.
#
# File: packages/testing/src/execution_testing/forks/forks/forks.py
# Files: the EIP modules beside it, under eips/
ACTIVE = {
    "byzantium": set(range(0x01, 0x09)),
    "istanbul": set(range(0x01, 0x0A)),
    "dencun": set(range(0x01, 0x0B)),
    "pectra": set(range(0x01, 0x12)),
    "fusaka": set(range(0x01, 0x12)) | {0x100},
}

# The highest address that the absence test calls.
UPPER_BOUND = 0x101


def active(fork: str) -> set[int]:
    """The precompiles of a fork: those of the latest fork of the table at or before it."""
    return next(ACTIVE[f] for f in reversed(since("byzantium", fork) + (fork,)) if f in ACTIVE)


@pytest.mark.parametrize("fork", FORKS)
@pytest.mark.parametrize("size", [0, 31, 32], ids=["empty_calldata", "31_bytes", "32_bytes"])
def test_precompile_absence(fork: str, size: int) -> None:
    # The test calls each address from 1 to 0x101 with no gas.
    # An address without a precompile is an empty account, which EthLib reports as code 0.
    # A precompile runs: it succeeds, as MODEXP does for free before Berlin, or fails with its
    # own error code.
    for address in range(1, UPPER_BOUND + 1):
        try:
            run(fork, address, bytes(size), 0)
            code = None
        except PrecompileError as error:
            code = error.code
        assert (code == 0) == (address not in active(fork)), (address, code)
