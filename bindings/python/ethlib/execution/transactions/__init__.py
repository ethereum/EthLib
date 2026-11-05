"""Transactions of the execution layer, at each fork."""

from typing import NamedTuple

from ...errors import TransactionError
from ...serialization import rlp

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


class Settlement(NamedTuple):
    """Where the wei of the gas limit of a transaction go, once it has run."""

    gas_used: int
    sender_refund: int
    priority_fee: int
    burned: int


def _number(value: int) -> bytes:
    return value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")


class Included(NamedTuple):
    """The sender, the price per gas and the blob gas of a transaction that may enter its block."""

    sender: bytes
    gas_price: int
    blob_gas_used: int


def check_in_block(
    fork: str, chain_id: int, tx: bytes, state: bytes, *, gas_limit: int, gas_used: int,
    blob_gas_used: int, base_fee: int, excess_blob_gas: int,
) -> Included:
    """Check that a transaction may enter its block, against a state in the form of `state_root`."""
    raw = _native.tx_check_in_block(
        fork, chain_id, tx, state, *map(_number, (gas_limit, gas_used, blob_gas_used, base_fee,
                                                  excess_blob_gas)))
    return Included(raw[:20], int.from_bytes(raw[20:52], "big"), int.from_bytes(raw[52:60], "big"))


class Run(NamedTuple):
    """What one transaction leaves, with the accounts of the state after it."""

    state_root: bytes
    logs_hash: bytes
    gas_used: int
    succeeded: bool
    accounts: list


def run(fork: str, chain_id: int, tx: bytes, state: bytes, env: bytes) -> Run:
    """Run one transaction on a state in the form of `state_root`, in a block that `env` encodes."""
    root, logs, gas_used, succeeded, accounts = rlp.decode(
        _native.tx_run(fork, chain_id, tx, state, env))
    return Run(root, logs, int.from_bytes(gas_used, "big"), succeeded == b"\x01", accounts)


def settle(fork: str, tx: bytes, base_fee: int, gas_left: int, refund_counter: int) -> Settlement:
    """Settle the gas of a transaction, from its gas left and its refund counter."""
    raw = _native.tx_settle(fork, tx, _number(base_fee), _number(gas_left), _number(refund_counter))
    return Settlement(*(int.from_bytes(raw[i:i + 64], "big") for i in range(0, 256, 64)))


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
