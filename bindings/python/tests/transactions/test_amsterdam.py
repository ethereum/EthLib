"""The intrinsic gas and the checks of a transaction at Glamsterdam, against the EIP texts."""

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import address, sign
from ethlib.execution import transactions
from ethlib.serialization import rlp

CHAIN_ID = 1
KEY = bytes(31) + b"\x01"
SENDER = address(KEY)
OTHER = b"\x11" * 20


def _int(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _fee_market(
    to: bytes, value: int = 0, data: bytes = b"", gas: int = 10**6, access_list: list | None = None
) -> bytes:
    """A signed type 2 transaction of the sender on chain 1."""
    fields = [
        _int(CHAIN_ID),
        b"",
        _int(1),
        _int(10),
        _int(gas),
        to,
        _int(value),
        data,
        access_list or [],
    ]
    signature = sign(KEY, keccak256(b"\x02" + rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return b"\x02" + rlp.encode(fields + [_int(v), r.lstrip(b"\0"), s.lstrip(b"\0")])


# The reference cases of EIP-2780, "Transaction reference cases": the intrinsic part.
@pytest.mark.parametrize(
    "to, value, intrinsic",
    [
        (SENDER, 1, 12_000),  # ETH transfer to self
        (OTHER, 0, 15_000),  # no transfer to another account
        (OTHER, 1, 21_000),  # ETH transfer to another account
        (b"", 0, 24_000),  # create transaction
        (b"", 1, 24_000),  # create transaction with value
    ],
)
def test_eip2780_reference_cases(to: bytes, value: int, intrinsic: int) -> None:
    tx = _fee_market(to, value)
    assert transactions.intrinsic_gas("glamsterdam", tx) == intrinsic
    assert transactions.check("glamsterdam", CHAIN_ID, tx).intrinsic_gas == intrinsic
    # Before Glamsterdam, each of them costs 21000, and 53000 to create.
    assert transactions.intrinsic_gas("bpo5", tx) == (53_000 if to == b"" else 21_000)


def test_access_list() -> None:
    # One address with one key: 2900 and 2000 by EIP-8038, plus 64 gas per byte by EIP-7981.
    tx = _fee_market(OTHER, 1, access_list=[[OTHER, [bytes(32)]]])
    assert transactions.intrinsic_gas("glamsterdam", tx) == 21_000 + 2_900 + 2_000 + 64 * 52
    # Before, 2400 and 1900, with no data price.
    assert transactions.intrinsic_gas("bpo5", tx) == 21_000 + 2_400 + 1_900


def test_calldata_floor() -> None:
    # 100 nonzero bytes: 1600 gas of call data, and a floor of 64 gas per byte by EIP-7976.
    data = b"\x01" * 100
    floor = 21_000 + 64 * 100
    assert transactions.intrinsic_gas("glamsterdam", _fee_market(OTHER, 1, data)) == 22_600
    transactions.check("glamsterdam", CHAIN_ID, _fee_market(OTHER, 1, data, gas=floor))
    with pytest.raises(transactions.TransactionError, match="insufficientGas 27400 27399"):
        transactions.check("glamsterdam", CHAIN_ID, _fee_market(OTHER, 1, data, gas=floor - 1))
    # Before Glamsterdam the floor is 21000 plus 10 gas per token, 4 tokens per nonzero byte.
    transactions.check("bpo5", CHAIN_ID, _fee_market(OTHER, 1, data, gas=25_000))


def test_gas_limit_bounds() -> None:
    # EIP-8037 bounds the gas limit at 2^32 - 1 and moves the bound 2^24 of EIP-7825.
    high = _fee_market(OTHER, gas=2**24 + 1)
    transactions.check("glamsterdam", CHAIN_ID, high)
    with pytest.raises(transactions.TransactionError, match="gasLimitExceeded"):
        transactions.check("bpo5", CHAIN_ID, high)
    transactions.check("glamsterdam", CHAIN_ID, _fee_market(OTHER, gas=2**32 - 1))
    with pytest.raises(transactions.TransactionError, match="gasLimitExceeded") as error:
        transactions.check("glamsterdam", CHAIN_ID, _fee_market(OTHER, gas=2**32))
    assert error.value.code == 8


def test_floor_above_bound() -> None:
    # A floor above 2^24 makes the transaction invalid, whatever its gas limit.
    tx = _fee_market(OTHER, data=b"\x01" * 270_000, gas=2**25)
    with pytest.raises(transactions.TransactionError, match="intrinsicGasAboveLimit") as error:
        transactions.check("glamsterdam", CHAIN_ID, tx)
    assert error.value.code == 16


def test_init_code_size() -> None:
    # EIP-7954 raises the bound on init code from 49152 to 131072 bytes.
    tx = _fee_market(b"", data=bytes(49_153), gas=2**24)
    transactions.check("glamsterdam", CHAIN_ID, tx)
    with pytest.raises(transactions.TransactionError, match="initCodeTooLarge"):
        transactions.check("bpo5", CHAIN_ID, tx)
    too_large = _fee_market(b"", data=bytes(131_073), gas=2**24)
    with pytest.raises(transactions.TransactionError, match="initCodeTooLarge"):
        transactions.check("glamsterdam", CHAIN_ID, too_large)
