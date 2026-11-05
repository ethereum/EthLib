"""The immediate bytes of DUPN, SWAPN and EXCHANGE, through the bindings."""

import pytest

from ethlib.errors import EvmError
from ethlib.execution.evm import immediate_depths
from raising import raises

DUPN, SWAPN, EXCHANGE = 0xE6, 0xE7, 0xE8

# The cases of EIP-8024, "Test Cases", "Assembly/Disassembly", that decode an immediate byte.
# Each case is the opcode, its immediate byte, and the depths, or None for INVALID.
#
# File: EIPS/eip-8024.md
# Repository: ethereum/EIPs
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445
# Licence: CC0-1.0
EIP_8024 = [
    (DUPN, 0x80, (17,)),
    (SWAPN, 0xDB, (108,)),
    (SWAPN, 0x5B, None),
    (DUPN, 0x60, None),
    (DUPN, 0x5F, None),
    (EXCHANGE, 0x9D, (2, 3)),
    (EXCHANGE, 0x2F, (1, 19)),
    (EXCHANGE, 0x50, (14, 16)),
    (EXCHANGE, 0x51, (14, 15)),
    (EXCHANGE, 0x52, None),
]


# The reference decoders of EIP-8024, "Specification", from the same file, with `assert`
# turned into a return of None.
def decode_single(x: int) -> tuple[int, ...] | None:
    if not (0 <= x <= 90 or 128 <= x <= 255):
        return None
    return ((x + 145) % 256,)


def decode_pair(x: int) -> tuple[int, ...] | None:
    if not (0 <= x <= 81 or 128 <= x <= 255):
        return None
    k = x ^ 143
    q, r = divmod(k, 16)
    if q < r:
        return q + 1, r + 1
    return r + 1, 29 - q


def _depths(opcode: int, immediate: int) -> tuple[int, ...] | None:
    try:
        return immediate_depths(opcode, immediate)
    except EvmError:
        return None


@pytest.mark.parametrize("opcode,immediate,expected", EIP_8024)
def test_eip_case(opcode: int, immediate: int, expected) -> None:
    assert _depths(opcode, immediate) == expected


@pytest.mark.parametrize(
    "opcode,decode", [(DUPN, decode_single), (SWAPN, decode_single), (EXCHANGE, decode_pair)]
)
def test_every_byte_as_the_eip(opcode: int, decode) -> None:
    for immediate in range(256):
        assert _depths(opcode, immediate) == decode(immediate), immediate


def test_other_opcode_rejected() -> None:
    # DUP1 carries no immediate byte.
    with raises(EvmError, "byte 128 encodes no depth of opcode 128"):
        immediate_depths(0x80, 0x80)
