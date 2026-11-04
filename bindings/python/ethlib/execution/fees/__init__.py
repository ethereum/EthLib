"""The base fee of EIP-1559 and the blob base fee of EIP-4844 and EIP-7918."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def _number(n: int) -> bytes:
    """The shortest big-endian bytes of a non-negative integer."""
    if n < 0:
        raise ValueError("a fee quantity cannot be negative")
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")


def _int(data: bytes) -> int:
    return int.from_bytes(data, "big")


def calculate_base_fee_per_gas(
    parent_gas_limit: int, parent_gas_used: int, parent_base_fee_per_gas: int
) -> int:
    """The base fee per gas of a block, from its parent."""
    args = (parent_gas_limit, parent_gas_used, parent_base_fee_per_gas)
    return _int(_native.fees_base_fee_per_gas(*map(_number, args)))


def fake_exponential(factor: int, numerator: int, denominator: int) -> int:
    """`factor * e^(numerator / denominator)` of EIP-4844, and 0 for a denominator of 0."""
    args = (factor, numerator, denominator)
    return _int(_native.fees_fake_exponential(*map(_number, args)))


def get_base_fee_per_blob_gas(fork: str, excess_blob_gas: int) -> int:
    """The base fee per blob gas at an excess, under the blob schedule of a fork."""
    return _int(_native.fees_base_fee_per_blob_gas(fork.encode(), _number(excess_blob_gas)))


def calc_excess_blob_gas(
    fork: str,
    parent_excess_blob_gas: int,
    parent_blob_gas_used: int,
    parent_base_fee_per_gas: int,
) -> int:
    """The excess blob gas of a block at a fork, from its parent."""
    args = (parent_excess_blob_gas, parent_blob_gas_used, parent_base_fee_per_gas)
    return _int(_native.fees_excess_blob_gas(fork.encode(), *map(_number, args)))


def calculate_data_fee(fork: str, excess_blob_gas: int, transaction: bytes) -> int:
    """The fee of the blobs of a transaction, decoded at a fork, at an excess blob gas."""
    return _int(_native.fees_blob_data_fee(fork.encode(), _number(excess_blob_gas), transaction))


__all__ = [
    "calculate_base_fee_per_gas",
    "fake_exponential",
    "get_base_fee_per_blob_gas",
    "calc_excess_blob_gas",
    "calculate_data_fee",
]
