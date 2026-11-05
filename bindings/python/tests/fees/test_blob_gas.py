"""The fee of the blobs of a transaction, against the formula of EIP-4844."""

import json
from pathlib import Path

import pytest

from ethlib.errors import FeesError
from ethlib.execution import fees
from ethlib.serialization import rlp
from raising import raises

_BLOCKS = json.loads(
    (
        Path(__file__).resolve().parents[4]
        / "tests"
        / "execution"
        / "blocks"
        / "blockchain_tests.json"
    ).read_text()
)

# EIP-4844 "Parameters": the blob gas of one blob.
GAS_PER_BLOB = 2**17

# The update fraction of each fork, from EIP-4844, EIP-7691, EIP-8134 and EIP-8135.
UPDATE_FRACTION = {"dencun": 3338477, "pectra": 5007716, "bpo1": 8346193, "bpo2": 11684671}


def fake_exponential(factor: int, numerator: int, denominator: int) -> int:
    """The `fake_exponential` of EIP-4844, "Helpers", as the EIP writes it."""
    i = 1
    output = 0
    numerator_accum = factor * denominator
    while numerator_accum > 0:
        output += numerator_accum
        numerator_accum = (numerator_accum * numerator) // (denominator * i)
        i += 1
    return output // denominator


def _transactions(network: str) -> list[bytes]:
    """The transactions of the fixture blocks of a network, as their bytes."""
    out = []
    for case in _BLOCKS:
        if case["network"] == network:
            for tx in rlp.decode(bytes.fromhex(case["rlp"]))[1]:
                out.append(tx if isinstance(tx, bytes) else rlp.encode(tx))
    return out


BLOB_TX = next(tx for tx in _transactions("Cancun") if tx[0] == 3)
BLOB_COUNT = len(rlp.decode(BLOB_TX[1:])[10])


def test_fixture_has_blobs() -> None:
    assert BLOB_COUNT > 0


@pytest.mark.parametrize("fork", sorted(UPDATE_FRACTION))
@pytest.mark.parametrize("excess", [0, 1, 393216, 2**20, 10**8])
def test_data_fee_of_blob_transaction(fork: str, excess: int) -> None:
    price = fake_exponential(1, excess, UPDATE_FRACTION[fork])
    assert fees.calculate_data_fee(fork, excess, BLOB_TX) == GAS_PER_BLOB * BLOB_COUNT * price


@pytest.mark.parametrize("network,fork", [("Cancun", "dencun"), ("Prague", "pectra")])
def test_transactions_without_blobs_pay_nothing(network: str, fork: str) -> None:
    others = [tx for tx in _transactions(network) if tx[0] != 3]
    assert others
    for tx in others:
        assert fees.calculate_data_fee(fork, 10**8, tx) == 0


def test_fork_before_dencun_rejected() -> None:
    with raises(FeesError, "a fork before dencun has no blob schedule") as error:
        fees.calculate_data_fee("shapella", 0, BLOB_TX)
    assert error.value.code == 0
