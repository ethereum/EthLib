"""Transactions of the execution layer, at each fork."""

from typing import NamedTuple

from ...errors import TransactionError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


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
    raw = _native.tx_check(fork, chain_id, tx)
    return Checked(raw[:20], int.from_bytes(raw[20:28], "big"))


__all__ = [
    "Checked",
    "check",
    "intrinsic_gas",
    "network_check",
    "recover_sender",
    "tx_hash",
    "tx_type",
    "TransactionError",
]
