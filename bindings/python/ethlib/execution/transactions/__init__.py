"""Transactions of the execution layer, at each fork."""

from typing import NamedTuple

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import TransactionError


def tx_type(fork: str, tx: bytes) -> int:
    """The EIP-2718 type of a transaction, or 0 for a legacy transaction."""
    return _native.tx_type(fork, tx)


def tx_hash(fork: str, tx: bytes) -> bytes:
    """The Keccak-256 hash of a transaction."""
    return _native.tx_hash(fork, tx)


def recover_sender(fork: str, tx: bytes) -> bytes:
    """The address of the sender that the signature of a transaction recovers."""
    return _native.tx_recover_sender(fork, tx)


def intrinsic_gas(fork: str, tx: bytes) -> int:
    """The intrinsic gas of a transaction, without the call data floor of EIP-7623."""
    return _native.tx_intrinsic_gas(fork, tx)


def network_check(fork: str, network: bytes) -> bytes:
    """Check the network form of a blob transaction, and return the transaction alone."""
    return _native.tx_network_check(fork, network)


class Checked(NamedTuple):
    """The sender and the intrinsic gas of a transaction that passes the checks."""

    sender: bytes
    intrinsic_gas: int


def check(fork: str, chain_id: int, tx: bytes) -> Checked:
    """Check a transaction alone, on the chain `chain_id`."""
    return Checked(*_native.tx_check(fork, chain_id, tx))


class Settlement(NamedTuple):
    """Where the wei of the gas limit of a transaction go, once it has run."""

    gas_used: int
    sender_refund: int
    priority_fee: int
    burned: int


class Included(NamedTuple):
    """The sender, the price per gas and the blob gas of a transaction that may enter its block."""

    sender: bytes
    gas_price: int
    blob_gas_used: int


def check_in_block(
    fork: str,
    chain_id: int,
    tx: bytes,
    state: bytes,
    *,
    gas_limit: int,
    gas_used: int,
    blob_gas_used: int,
    base_fee: int,
    excess_blob_gas: int,
) -> Included:
    """Check that a transaction may enter its block, against a state in the form of `state_root`."""
    return Included(
        *_native.tx_check_in_block(
            fork,
            chain_id,
            tx,
            state,
            gas_limit,
            gas_used,
            blob_gas_used,
            base_fee,
            excess_blob_gas,
        )
    )


class Run(NamedTuple):
    """What one transaction leaves, with the accounts of the state after it."""

    state_root: bytes
    logs_hash: bytes
    gas_used: int
    succeeded: bool
    # Each account is its address, nonce, balance and code, then its storage slots with values.
    accounts: list[tuple[bytes, int, int, bytes, list[tuple[bytes, int]]]]


def run(fork: str, chain_id: int, tx: bytes, state: bytes, env: bytes) -> Run:
    """Run one transaction on a state in the form of `state_root`, in a block that `env` encodes."""
    return Run(*_native.tx_run(fork, chain_id, tx, state, env))


def settle(fork: str, tx: bytes, base_fee: int, gas_left: int, refund_counter: int) -> Settlement:
    """Settle the gas of a transaction, from its gas left and its refund counter."""
    return Settlement(*_native.tx_settle(fork, tx, base_fee, gas_left, refund_counter))


__all__ = [
    "Checked",
    "Included",
    "Run",
    "Settlement",
    "check",
    "check_in_block",
    "intrinsic_gas",
    "network_check",
    "recover_sender",
    "run",
    "settle",
    "tx_hash",
    "tx_type",
    "TransactionError",
]
