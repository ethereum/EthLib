"""A sender must hold the whole maximum fee of a transaction, even past 2^256."""

# A product of a fee field and a gas amount can reach 2^256, the size of a word.
# Reduced modulo 2^256 it would be small, and the balance below would cover it.
# EIP-1559 requires a balance of at least the gas limit times the maximum fee per gas.
# EIP-4844 adds the blob gas times the maximum fee per blob gas, both over unbounded integers.
# So the transaction must fail with the cost in full, which these cases compute from those rules.
#
# The official fixtures hold such a product only for the gas price of a legacy transaction.

import pytest

from ethlib.cryptography.secp256k1 import address
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

from .expected_errors import FIRST_FORK_OF_TYPE, FORKS
from .test_set_code_nonce import AUTHORIZATION, KEY, OTHER, _int, _signed
from .test_typed import ENV

# The sender holds 1 ether, with nonce 0 and no code.
BALANCE = 10**18
STATE = rlp.encode([[address(KEY), b"", _int(BALANCE), b"", []]])

# The forks of each type, from its first fork: 2 by EIP-1559, 3 by EIP-4844, 4 by EIP-7702.
FEE_MARKET = FORKS[FORKS.index(FIRST_FORK_OF_TYPE[2]) :]
BLOB = FORKS[FORKS.index(FIRST_FORK_OF_TYPE[3]) :]
SET_CODE = FORKS[FORKS.index(FIRST_FORK_OF_TYPE[4]) :]

# The gas of each transaction, above its intrinsic gas at every fork.
# It is below the cap of 2^24 that EIP-7825 sets from Fusaka.
GAS = 2**20

# The blob gas of one blob, by EIP-4844.
GAS_PER_BLOB = 2**17

# One versioned hash, of version 0x01 as EIP-4844 asks.
BLOB_HASH = b"\x01" + bytes(31)

# Two maximum fees per gas whose product with the gas is 2^256, then 2^256 + 2^20.
# Reduced modulo 2^256, these products are 0 and 2^20 wei, which the balance covers.
MAX_FEES = [2**236, 2**236 + 1]


def _common(max_fee: int) -> list[bytes | list]:
    """Chain 1, nonce 0, no priority fee, the gas, a call of no value and no data to another."""
    return [_int(1), b"", b"", _int(max_fee), _int(GAS), OTHER, b"", b"", []]


def _run(fork: str, tx: bytes) -> transactions.Run:
    # A base fee and a blob base fee of 1, in a block of 30 million gas.
    return transactions.run(fork, 1, tx, STATE, ENV)


def _refused(cost: int) -> pytest.RaisesExc[transactions.TransactionError]:
    return raises(
        transactions.TransactionError,
        f"insufficientBalance (balance := {BALANCE}) (cost := {cost})",
    )


@pytest.mark.parametrize("max_fee", MAX_FEES)
@pytest.mark.parametrize("fork", FEE_MARKET)
def test_fee_market(fork: str, max_fee: int) -> None:
    assert GAS * max_fee >= 2**256 and GAS * max_fee % 2**256 <= BALANCE
    with _refused(GAS * max_fee):
        _run(fork, _signed(2, _common(max_fee)))


@pytest.mark.parametrize("max_fee", MAX_FEES)
@pytest.mark.parametrize("fork", SET_CODE)
def test_set_code(fork: str, max_fee: int) -> None:
    # One authorization, which the check of a transaction does not recover.
    with _refused(GAS * max_fee):
        _run(fork, _signed(4, _common(max_fee) + [[AUTHORIZATION]]))


@pytest.mark.parametrize("max_fee", MAX_FEES)
@pytest.mark.parametrize("fork", BLOB)
def test_blob_gas_fee(fork: str, max_fee: int) -> None:
    # One blob at 1 per blob gas, so the product of the gas and the maximum fee carries the cost.
    tx = _signed(3, _common(max_fee) + [_int(1), [BLOB_HASH]])
    with _refused(GAS * max_fee + GAS_PER_BLOB):
        _run(fork, tx)


@pytest.mark.parametrize("fork", BLOB)
def test_blob_fee_of_exactly_2_256(fork: str) -> None:
    # A maximum fee of 10 per gas, and one blob at 2^239 per blob gas: 2^256 for the blob gas.
    max_fee_per_blob_gas = 2**239
    blob_fee = GAS_PER_BLOB * max_fee_per_blob_gas
    assert blob_fee == 2**256
    tx = _signed(3, _common(10) + [_int(max_fee_per_blob_gas), [BLOB_HASH]])
    with _refused(GAS * 10 + blob_fee):
        _run(fork, tx)


@pytest.mark.parametrize("fork", BLOB)
def test_blob_fee_one_below(fork: str) -> None:
    # A blob fee of 2^256 - 2^17 fits a word, and is refused at its own cost.
    # Its sum with the gas fee of 10 * 2^20 passes 2^256, so a wrapped sum would be small.
    max_fee_per_blob_gas = 2**239 - 1
    tx = _signed(3, _common(10) + [_int(max_fee_per_blob_gas), [BLOB_HASH]])
    with _refused(GAS * 10 + GAS_PER_BLOB * max_fee_per_blob_gas):
        _run(fork, tx)


@pytest.mark.parametrize("fork", FEE_MARKET)
def test_fee_market_within_balance(fork: str) -> None:
    # The control: the same transaction at a maximum fee of 10 per gas runs.
    assert _run(fork, _signed(2, _common(10))).succeeded
