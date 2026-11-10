"""Block headers, blocks and receipts of the execution layer, at each fork."""

from collections.abc import Sequence

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import BlockError
from ethlib.serialization import rlp


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


def deposit_requests(deposit_contract: bytes, logs: bytes) -> bytes:
    """The data of the deposit requests of logs, from the deposit contract at this address."""
    return _native.block_deposit_requests(deposit_contract, logs)


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


def validate_header(
    parent_fork: str,
    fork: str,
    parent: bytes,
    header: bytes,
    blob_schedules: Sequence[BlobSchedule] = (),
) -> None:
    """Check a header against its parent at any fork, and raise BlockError if it fails."""
    _native.block_validate_header(parent_fork, fork, parent, header, list(blob_schedules))


def check_header(
    parent_fork: str,
    fork: str,
    parent: bytes,
    header: bytes,
    blob_schedules: Sequence[BlobSchedule] = (),
) -> None:
    """Check a header against its parent, every check but the proof of work."""
    _native.block_check_header(parent_fork, fork, parent, header, list(blob_schedules))


def dao_extra_data_valid(dao_block: int, fork: str, header: bytes) -> bool:
    """Whether a header has the DAO Fork extra data, on a chain that starts it at `dao_block`."""
    return _native.block_dao_extra_data_valid(dao_block, fork, header)


# A recent block of a chain: its fork, its header and the headers of its ommers.
RecentBlock = tuple[str, bytes, Sequence[bytes]]


def state_transition(
    config: dict,
    state: bytes,
    recent: Sequence[RecentBlock],
    fork: str,
    block: bytes,
    check_seal: bool = True,
) -> tuple[bytes, list]:
    """Run a block on a chain, and return the state root and the accounts after it."""
    items = [(name, header, list(ommers)) for name, header, ommers in recent]
    root, accounts = rlp.decode(
        _native.state_transition(config, state, items, fork, block, check_seal)
    )
    return root, accounts


# The base fee of the first block of London, by EIP-1559.
INITIAL_BASE_FEE = 1_000_000_000


def genesis_block(
    fork: str,
    state: bytes,
    *,
    coinbase: bytes,
    difficulty: int,
    gas_limit: int,
    timestamp: int,
    extra_data: bytes,
    mix_hash: bytes,
    nonce: bytes,
    base_fee: int = INITIAL_BASE_FEE,
    excess_blob_gas: int = 0,
    slot_number: int = 0,
) -> bytes:
    """The genesis block at a fork of a chain with the header fields it chooses and its state."""
    params = (
        coinbase,
        difficulty,
        gas_limit,
        timestamp,
        extra_data,
        mix_hash,
        nonce,
        base_fee,
        excess_blob_gas,
        slot_number,
    )
    return _native.genesis_block(fork, params, state)


__all__ = [
    "header_hash",
    "reencode",
    "transactions_root",
    "withdrawals_root",
    "deposit_requests",
    "requests_hash",
    "block_access_list_hash",
    "check_block_access_list",
    "make_receipts",
    "receipt_reencode",
    "receipt_logs_bloom",
    "validate_size",
    "validate_header",
    "check_header",
    "dao_extra_data_valid",
    "state_transition",
    "genesis_block",
    "INITIAL_BASE_FEE",
    "BlobSchedule",
    "RecentBlock",
    "BlockError",
]
