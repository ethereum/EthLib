"""The EVM stack instructions and the price of memory, through the bindings."""

import pytest

from ethlib.errors import EvmError
from ethlib.execution.evm import extend_memory, memory_gas_cost, word_op

OPCODES = {
    "MOD": 0x06, "SDIV": 0x05, "SMOD": 0x07, "ADDMOD": 0x08, "EXP": 0x0A, "SIGNEXTEND": 0x0B,
    "LT": 0x10, "SLT": 0x12, "SGT": 0x13, "BYTE": 0x1A, "SHL": 0x1B, "SHR": 0x1C, "SAR": 0x1D,
}

MAX = 2**256 - 1
INT_MIN = 2**255


def signed(value: int) -> int:
    """The word of a signed integer in two's complement."""
    return value % 2**256


# The test cases of EIP-145, "Test Cases", in `EIPS/eip-145.md` of `ethereum/EIPs`
# at commit `0ce679f4654ba4d120c97113626f320475e22fa9`, under CC0-1.0.
# Each case is the opcode, the shift, the value and the result.
EIP_145 = [
    ("SHL", 0x0,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000001),
    ("SHL", 0x1,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000002),
    ("SHL", 0xff,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x8000000000000000000000000000000000000000000000000000000000000000),
    ("SHL", 0x100,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHL", 0x101,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHL", 0x0,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SHL", 0x1,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe),
    ("SHL", 0xff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x8000000000000000000000000000000000000000000000000000000000000000),
    ("SHL", 0x100,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHL", 0x1,
     0x0000000000000000000000000000000000000000000000000000000000000000,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHL", 0x1,
     0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe),
    ("SHR", 0x0,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000001),
    ("SHR", 0x1,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHR", 0x1,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0x4000000000000000000000000000000000000000000000000000000000000000),
    ("SHR", 0xff,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0x0000000000000000000000000000000000000000000000000000000000000001),
    ("SHR", 0x100,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHR", 0x101,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHR", 0x0,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SHR", 0x1,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SHR", 0xff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x0000000000000000000000000000000000000000000000000000000000000001),
    ("SHR", 0x100,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SHR", 0x1,
     0x0000000000000000000000000000000000000000000000000000000000000000,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SAR", 0x0,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000001),
    ("SAR", 0x1,
     0x0000000000000000000000000000000000000000000000000000000000000001,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SAR", 0x1,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0xc000000000000000000000000000000000000000000000000000000000000000),
    ("SAR", 0xff,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SAR", 0x100,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SAR", 0x101,
     0x8000000000000000000000000000000000000000000000000000000000000000,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SAR", 0x0,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SAR", 0x1,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SAR", 0xff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SAR", 0x100,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    ("SAR", 0x1,
     0x0000000000000000000000000000000000000000000000000000000000000000,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SAR", 0xfe,
     0x4000000000000000000000000000000000000000000000000000000000000000,
     0x0000000000000000000000000000000000000000000000000000000000000001),
    ("SAR", 0xf8,
     0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x000000000000000000000000000000000000000000000000000000000000007f),
    ("SAR", 0xfe,
     0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x0000000000000000000000000000000000000000000000000000000000000001),
    ("SAR", 0xff,
     0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x0000000000000000000000000000000000000000000000000000000000000000),
    ("SAR", 0x100,
     0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
     0x0000000000000000000000000000000000000000000000000000000000000000),
]


@pytest.mark.parametrize("op, shift, value, result", EIP_145)
def test_eip_145(op: str, shift: int, value: int, result: int) -> None:
    # The shift is on top of the stack, and the value below it.
    assert word_op(OPCODES[op], shift, value) == result


@pytest.mark.parametrize("op, operands, result", [
    # A divisor of 0 gives 0.
    ("MOD", (7, 0), 0),
    # -2^255 / -1 overflows to -2^255.
    ("SDIV", (INT_MIN, MAX), INT_MIN),
    # -7 / 2 rounds toward 0, to -3.
    ("SDIV", (signed(-7), 2), signed(-3)),
    # -7 mod 2 takes the sign of the dividend, so -1.
    ("SMOD", (signed(-7), 2), signed(-1)),
    # (2^256 - 1) + 2 = 2^256 + 1, and 2^256 + 1 mod 3 = 2, where wrapping first would give 1.
    ("ADDMOD", (MAX, 2, 3), 2),
    # 2^256 wraps to 0.
    ("EXP", (2, 256), 0),
    # 0x7f has sign bit 0 in one byte, so it stays 0x7f.
    ("SIGNEXTEND", (0, 0x127F), 0x7F),
    # 0xff has sign bit 1 in one byte, so it becomes -1.
    ("SIGNEXTEND", (0, 0xFF), MAX),
    # A byte index above 31 leaves the value.
    ("SIGNEXTEND", (32, 0xFF), 0xFF),
    # -1 is below 0 as a signed word.
    ("SLT", (MAX, 0), 1),
    # 2^256 - 1 is above 0 as an unsigned word.
    ("LT", (MAX, 0), 0),
    # -2^255 is the smallest signed word.
    ("SGT", (INT_MIN, MAX), 0),
    # Byte 31 is the least significant.
    ("BYTE", (31, 0xABCD), 0xCD),
    # Byte 32 is out of range.
    ("BYTE", (32, MAX), 0),
])
def test_edge_cases(op: str, operands: tuple, result: int) -> None:
    assert word_op(OPCODES[op], *operands) == result


def test_opcode_outside_the_table() -> None:
    # JUMP depends on more than its operands.
    with pytest.raises(EvmError) as info:
        word_op(0x56, 0)
    assert info.value.code == 0


@pytest.mark.parametrize("size, cost", [
    # One word costs 3, and 1024 words cost 3 * 1024 + 1024^2 / 512 = 5120.
    (32, 3),
    (32 * 1024, 5120),
])
def test_memory_gas_cost(size: int, cost: int) -> None:
    assert memory_gas_cost(size) == cost


@pytest.mark.parametrize("current, ranges, result", [
    # An empty memory grows by one word, at the price of one word.
    (0, [(0, 32)], (3, 32)),
    # One byte past a word grows memory by a whole word.
    (32, [(32, 1)], (3, 32)),
])
def test_extend_memory(current: int, ranges: list, result: tuple) -> None:
    assert extend_memory(current, ranges) == result


def test_raw_lengths() -> None:
    # The extension takes whole words and whole ranges, so a shorter input is rejected.
    from ethlib.cryptography import _native

    with pytest.raises(ValueError):
        _native.evm_word_op(0x01, b"\x01", bytes(32), bytes(32))
    with pytest.raises(ValueError):
        _native.evm_extend_memory_cost(b"\x00", bytes(63))
