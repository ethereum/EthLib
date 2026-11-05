"""Block headers, blocks and receipts of the execution layer, at each fork."""

from ...errors import BlockError
from ...serialization import rlp

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def header_hash(fork: str, header: bytes) -> bytes:
    """The Keccak-256 hash of a header, which must hold exactly the fields of the fork."""
    return _native.block_header_hash(fork, header)


def reencode(fork: str, block: bytes) -> bytes:
    """The RLP bytes of a block, decoded at the fork and encoded again."""
    return _native.block_reencode(fork, block)


def transactions_root(fork: str, block: bytes) -> bytes:
    """The transactions root of the transactions of a block, decoded at the fork."""
    return _native.block_transactions_root(fork, block)


def withdrawals_root(fork: str, block: bytes) -> bytes:
    """The withdrawals root of the withdrawals of a block, decoded at a fork from Shapella."""
    return _native.block_withdrawals_root(fork, block)


def deposit_requests(logs: bytes) -> bytes:
    """The data of the deposit requests of logs, given as the RLP list of the logs, in order."""
    return _native.block_deposit_requests(logs)


def requests_hash(requests: bytes) -> bytes:
    """The requests hash of request lists, given as an RLP list of byte strings."""
    return _native.block_requests_hash(requests)


def block_access_list_hash(block_access_list: bytes) -> bytes:
    """The hash of a block access list in RLP form, from Glamsterdam on."""
    return _native.block_access_list_hash(block_access_list)


def check_block_access_list(block_access_list: bytes, gas_limit: int) -> None:
    """Check the order and the size of a block access list, and raise BlockError if it fails."""
    _native.block_access_list_check(block_access_list, gas_limit)


def receipt_reencode(fork: str, receipt: bytes) -> bytes:
    """The bytes of a receipt, decoded at the fork and encoded again."""
    return _native.receipt_reencode(fork, receipt)


def make_receipts(fork: str, results: bytes) -> tuple[bytes, list[bytes]]:
    """The receipts root and the receipts of a block, from the RLP list of its results."""
    root, receipts = rlp.decode(_native.block_make_receipts(fork, results))
    return root, receipts


def receipt_logs_bloom(fork: str, receipt: bytes) -> bytes:
    """The 256-byte logs Bloom filter of the logs of a receipt, decoded at the fork."""
    return _native.receipt_logs_bloom(fork, receipt)


def validate_size(fork: str, block: bytes) -> None:
    """Check the RLP size of a block, from Fusaka, and raise BlockError if it is too large."""
    _native.block_validate_size(fork, block)


def validate_header(parent_fork: str, fork: str, parent: bytes, header: bytes) -> None:
    """Check a header against its parent at any fork, and raise BlockError if it fails."""
    _native.block_validate_header(parent_fork, fork, parent, header)


def check_header(parent_fork: str, fork: str, parent: bytes, header: bytes) -> None:
    """Check a header against its parent, every check but the proof of work."""
    _native.block_check_header(parent_fork, fork, parent, header)


__all__ = ["header_hash", "reencode", "transactions_root", "withdrawals_root",
           "deposit_requests", "requests_hash", "block_access_list_hash",
           "check_block_access_list", "make_receipts", "receipt_reencode", "receipt_logs_bloom",
           "validate_size", "validate_header", "check_header", "BlockError"]
