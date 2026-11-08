"""The typed results and arguments of the transaction checks, the settlement and the run."""

import pytest

from ethlib.cryptography.secp256k1 import address
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

from .test_check_order import KEY, OTHER, STATE, _fee_market, _int

# A transfer of 1 wei at a price of at most 10 per gas, of which 1 goes to the beneficiary.
TX = _fee_market(1, 21_000)

COINBASE = b"\x22" * 20

# The ten fields of a block that a run reads, with a base fee of 1 and no hashes before.
ENV = rlp.encode(
    [COINBASE, _int(30_000_000), _int(1), _int(1), b"", _int(1), bytes(32), b"", [], b""]
)


def test_check() -> None:
    assert transactions.check("pectra", 1, TX) == (address(KEY), 21_000)


def test_check_in_block() -> None:
    # The price per gas is the base fee plus the priority fee of 1, below the cap of 10.
    included = transactions.check_in_block(
        "pectra",
        1,
        TX,
        STATE,
        gas_limit=30_000_000,
        gas_used=0,
        blob_gas_used=0,
        base_fee=1,
        excess_blob_gas=0,
    )
    assert included == (address(KEY), 2, 0)


def test_settle() -> None:
    # The call data floor of EIP-7623 charges the whole 21000, though 1000 gas is left.
    # At a price of 2 + 1, the beneficiary gets 1 wei per gas, and 2 wei per gas are burned.
    settled = transactions.settle("pectra", TX, base_fee=2, gas_left=1_000, refund_counter=0)
    assert settled == (21_000, 0, 21_000, 42_000)


def test_run() -> None:
    run = transactions.run("pectra", 1, TX, STATE, ENV)
    assert (run.gas_used, run.succeeded) == (21_000, True)
    accounts = {entry[0]: entry for entry in run.accounts}
    # The sender pays the wei sent and 2 wei per gas, and its nonce goes up.
    assert accounts[address(KEY)] == (address(KEY), 1, 10**18 - 1 - 2 * 21_000, b"", [])
    assert accounts[OTHER] == (OTHER, 0, 1, b"", [])


@pytest.mark.parametrize(
    "chain_id, message",
    [
        (True, "expected an int"),
        (2**64, f"expected an int below {2**64}, got {2**64}"),
    ],
)
def test_chain_id_must_fit(chain_id: int, message: str) -> None:
    with raises(transactions.TransactionError, message) as info:
        transactions.check("pectra", chain_id, TX)
    assert info.value.code == 0


def test_fork_is_a_str() -> None:
    with raises(transactions.TransactionError, "expected a str") as info:
        transactions.check(b"pectra", 1, TX)  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0


def test_numbers_are_not_negative() -> None:
    with raises(ValueError, "cannot pass a negative int to Lean"):
        transactions.settle("pectra", TX, base_fee=-1, gas_left=0, refund_counter=0)
