"""Block headers, blocks and receipts of the execution layer, at each fork."""

import json
from collections.abc import Sequence

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


# A blob schedule that a chain sets itself: activation time, target, maximum, update fraction.
BlobSchedule = tuple[int, int, int, int]


def _blob_schedules(schedules: Sequence[BlobSchedule]) -> bytes:
    # Each integer crosses as its minimal big-endian bytes, in one RLP list per schedule.
    return rlp.encode([[v.to_bytes((v.bit_length() + 7) // 8, "big") for v in schedule]
                       for schedule in schedules])


def validate_header(parent_fork: str, fork: str, parent: bytes, header: bytes,
                    blob_schedules: Sequence[BlobSchedule] = ()) -> None:
    """Check a header against its parent at any fork, and raise BlockError if it fails."""
    _native.block_validate_header(parent_fork, fork, parent, header,
                                  _blob_schedules(blob_schedules))


def check_header(parent_fork: str, fork: str, parent: bytes, header: bytes,
                 blob_schedules: Sequence[BlobSchedule] = ()) -> None:
    """Check a header against its parent, every check but the proof of work."""
    _native.block_check_header(parent_fork, fork, parent, header,
                               _blob_schedules(blob_schedules))


def dao_extra_data_valid(dao_block: int, fork: str, header: bytes) -> bool:
    """Whether a header has the extra data of the DAO Fork, on a chain that starts it at `dao_block`."""
    return _native.block_dao_extra_data_valid(dao_block, fork, header)


# A recent block of a chain: its fork, its header and the headers of its ommers.
RecentBlock = tuple[str, bytes, Sequence[bytes]]


def state_transition(config: dict, state: bytes, recent: Sequence[RecentBlock], fork: str,
                     block: bytes, check_seal: bool = True) -> tuple[bytes, list]:
    """Run a block on a chain, and return the state root and the accounts after it."""
    # Each header is already RLP, so it enters the list of the recent blocks as a raw item.
    items = [[name.encode(), rlp.decode(header), [rlp.decode(o) for o in ommers]]
             for name, header, ommers in recent]
    root, accounts = rlp.decode(_native.state_transition(
        json.dumps(config).encode(), state, rlp.encode(items), fork, block, check_seal))
    return root, accounts


__all__ = ["header_hash", "reencode", "transactions_root", "withdrawals_root",
           "deposit_requests", "requests_hash", "block_access_list_hash",
           "check_block_access_list", "make_receipts", "receipt_reencode", "receipt_logs_bloom",
           "validate_size", "validate_header", "check_header", "dao_extra_data_valid",
           "state_transition", "BlobSchedule", "RecentBlock", "BlockError"]
