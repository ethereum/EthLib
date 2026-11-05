"""The words of EVM stack instructions, the price of EVM memory and created addresses."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

_WORD = 2**256


def _word(value: int) -> bytes:
    """The 32 big-endian bytes of a word, which must be below 2^256."""
    if not 0 <= value < _WORD:
        raise OverflowError("a word must be in [0, 2^256)")
    return value.to_bytes(32, "big")


def _number(n: int) -> bytes:
    """The shortest big-endian bytes of a non-negative integer."""
    if n < 0:
        raise OverflowError("a size cannot be negative")
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")


def immediate_depths(opcode: int, immediate: int) -> tuple[int, ...]:
    """The depths that the immediate byte of DUPN, SWAPN or EXCHANGE encodes, by EIP-8024."""
    return tuple(_native.evm_immediate_depths(opcode, immediate))


def word_op(opcode: int, *operands: int) -> int:
    """The word that an opcode pushes, at a fork that has it, for operands missing ones as 0."""
    if len(operands) > 3:
        raise ValueError("an instruction takes at most 3 operands")
    words = [_word(x) for x in operands] + [bytes(32)] * (3 - len(operands))
    return int.from_bytes(_native.evm_word_op(opcode, *words), "big")


def memory_gas_cost(size: int) -> int:
    """The price of a memory of `size` bytes."""
    return int.from_bytes(_native.evm_memory_gas_cost(_number(size)), "big")


def extend_memory(current_size: int, ranges: list[tuple[int, int]]) -> tuple[int, int]:
    """The price of growing a memory for the ranges `(start, size)`, and the bytes it grows by."""
    data = b"".join(_word(start) + _word(size) for start, size in ranges)
    size = _number(current_size)
    cost = int.from_bytes(_native.evm_extend_memory_cost(size, data), "big")
    expand_by = int.from_bytes(_native.evm_extend_memory_expand_by(size, data), "big")
    return cost, expand_by


def create_address(sender: bytes, nonce: int) -> bytes:
    """The address of the contract that `sender` creates with CREATE at `nonce`."""
    return _native.evm_create_address(sender, _number(nonce))


def create2_address(sender: bytes, salt: bytes, init_code: bytes) -> bytes:
    """The address of the contract that `sender` creates with CREATE2."""
    return _native.evm_create2_address(sender, salt, init_code)


__all__ = [
    "immediate_depths",
    "word_op",
    "memory_gas_cost",
    "extend_memory",
    "create_address",
    "create2_address",
]
