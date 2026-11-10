"""The extra data that the DAO Fork asks of its first ten blocks, on headers built by hand."""

import pytest

from ethlib.execution import blocks
from ethlib.serialization import rlp

# The chain starts the fork at block 5, so the ten blocks are 5 to 14.
DAO_BLOCK = 5
DAO_EXTRA_DATA = b"dao-hard-fork"


def _scalar(value: int) -> bytes:
    # A scalar is its big-endian bytes with no leading zero, so zero is the empty string.
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def _header(number: int, extra_data: bytes, base_fee: int | None = None) -> bytes:
    # A Homestead header: 15 fields, with every hash, address, bloom and nonce zero.
    # From London a 16th field, the base fee, follows.
    london = [] if base_fee is None else [_scalar(base_fee)]
    return rlp.encode(
        [
            bytes(32),  # parent hash
            bytes(32),  # ommers hash
            bytes(20),  # coinbase
            bytes(32),  # state root
            bytes(32),  # transactions root
            bytes(32),  # receipts root
            bytes(256),  # bloom
            _scalar(131072),  # difficulty
            _scalar(number),
            _scalar(5000),  # gas limit
            b"",  # gas used
            _scalar(1),  # timestamp
            extra_data,
            bytes(32),  # mix hash
            bytes(8),  # nonce
            *london,
        ]
    )


@pytest.mark.parametrize(
    ("number", "extra_data", "valid"),
    [
        pytest.param(DAO_BLOCK - 1, b"other", True, id="before-window"),
        pytest.param(DAO_BLOCK, DAO_EXTRA_DATA, True, id="first-block-right-data"),
        pytest.param(DAO_BLOCK, b"other", False, id="first-block-other-data"),
        pytest.param(DAO_BLOCK + 9, DAO_EXTRA_DATA, True, id="last-block-right-data"),
        pytest.param(DAO_BLOCK + 9, b"other", False, id="last-block-other-data"),
        pytest.param(DAO_BLOCK + 10, b"other", True, id="after-window"),
    ],
)
def test_dao_extra_data_valid(number: int, extra_data: bytes, valid: bool) -> None:
    """A header from the fork block on, for ten blocks, needs the extra data; others pass."""
    header = _header(number, extra_data)
    assert blocks.dao_extra_data_valid(DAO_BLOCK, "homestead", header) is valid


@pytest.mark.parametrize(
    ("fork", "valid"),
    [
        pytest.param("grayGlacier", False, id="last-fork-before-paris"),
        pytest.param("paris", True, id="paris"),
    ],
)
def test_dao_extra_data_ends_at_paris(fork: str, valid: bool) -> None:
    """From Paris the rule ends, so the fork block passes with other extra data."""
    header = _header(DAO_BLOCK, b"other", base_fee=7)
    assert blocks.dao_extra_data_valid(DAO_BLOCK, fork, header) is valid
