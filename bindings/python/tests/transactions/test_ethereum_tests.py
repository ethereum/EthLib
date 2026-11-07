"""Transactions against the transaction tests of ethereum/tests."""

import json
from pathlib import Path

import pytest

from ethlib.execution import transactions
from raising import raises_shape

from .expected_errors import expected_template

_REPO = Path(__file__).resolve().parents[4]
_FIXTURES = _REPO / "tests" / "execution" / "ethereum_tests" / "TransactionTests"

# The network of a fixture, and the case of the Lean fork type that it names.
FORK_OF_NETWORK = {
    "Frontier": "frontier",
    "Homestead": "homestead",
    "EIP150": "tangerineWhistle",
    "EIP158": "spuriousDragon",
    "Byzantium": "byzantium",
    "Constantinople": "constantinople",
    "ConstantinopleFix": "petersburg",
    "Istanbul": "istanbul",
    "Berlin": "berlin",
    "London": "london",
    "Paris": "paris",
    "Shanghai": "shapella",
    "Cancun": "dencun",
    # One result of ttWrongRLP/RLPgasLimitWithFirstZeros.json misspells Cancun.
    # The file has no other Cancun result, so the misspelt key is the Cancun one.
    "Cancnun": "dencun",
    "Prague": "pectra",
}

# The fixtures run on chain 1.
CHAIN_ID = 1

# The results that ethereum/tests rejects and EthLib accepts, by file and exception.
#
# The fixtures reject a gas limit of 2^64 and a gas limit times gas price above 2^256 - 1.
# The Yellow Paper (Berlin version, section 4.2) types the gas limit and gas price as scalars.
# Such a scalar is below 2^256.
# Section 6.2 of the paper computes the up-front cost in the naturals.
# It checks that cost against the balance.
# The same section checks the gas limit against the gas left in the block.
# So a block or the sender's balance rejects these transactions, and no rule rejects one alone.
# EIP-7825 caps the gas limit only from Fusaka, after the last fork of these fixtures.
# The suite asserts that EthLib accepts them, so that any change shows.
DISAGREEMENTS = {
    ("ttGasLimit/TransactionWithGasLimitOverflow64.json", "GASLIMIT_OVERFLOW"),
    ("ttGasLimit/TransactionWithGasLimitxPriceOverflow.json", "GASLIMIT_PRICE_PRODUCT_OVERFLOW"),
    ("ttEIP1559/GasLimitPriceProductOverflow.json", "GASLIMIT_PRICE_PRODUCT_OVERFLOW"),
    ("ttEIP1559/GasLimitPriceProductPlusOneOverflow.json", "GASLIMIT_PRICE_PRODUCT_OVERFLOW"),
    ("ttEIP1559/maxFeePerGas32BytesValue.json", "GASLIMIT_PRICE_PRODUCT_OVERFLOW"),
}

# The number of results in those files that EthLib accepts.
DISAGREEMENT_COUNT = 43


def _results():
    """Every result of the fixtures, with the file it comes from."""
    for path in sorted(_FIXTURES.rglob("*.json")):
        relative = path.relative_to(_FIXTURES).as_posix()
        for name, fixture in json.loads(path.read_text()).items():
            tx = bytes.fromhex(fixture["txbytes"].removeprefix("0x"))
            for network, outcome in sorted(fixture["result"].items()):
                yield pytest.param(relative, network, tx, outcome, id=f"{network}-{name}")


RESULTS = list(_results())


def _disagrees(path: str, outcome: dict) -> bool:
    exception = outcome.get("exception", "").removeprefix("TransactionException.")
    return (path, exception) in DISAGREEMENTS


def test_counts():
    """The copy holds 210 files, 2,938 results, and each network of the fixtures."""
    assert len({result.values[0] for result in RESULTS}) == 210
    assert len(RESULTS) == 2938
    assert {result.values[1] for result in RESULTS} == set(FORK_OF_NETWORK)
    assert sum(_disagrees(r.values[0], r.values[3]) for r in RESULTS) == DISAGREEMENT_COUNT


@pytest.mark.parametrize("path, network, tx, outcome", RESULTS)
def test_result(path: str, network: str, tx: bytes, outcome: dict):
    """The checks reach the outcome of the fixture at its fork."""
    fork = FORK_OF_NETWORK[network]
    if _disagrees(path, outcome):
        transactions.check(fork, CHAIN_ID, tx)
    elif "exception" in outcome:
        intrinsic = int(outcome["intrinsicGas"], 16)
        template = expected_template(outcome["exception"], fork, tx, CHAIN_ID, intrinsic or None)
        with raises_shape(ValueError, template):
            transactions.check(fork, CHAIN_ID, tx)
        # Where the fixture gives the intrinsic gas of a rejected transaction, it must agree.
        if intrinsic and not template.startswith(("decoding", "unsupportedType")):
            assert transactions.intrinsic_gas(fork, tx) == intrinsic
    else:
        checked = transactions.check(fork, CHAIN_ID, tx)
        assert checked.sender == bytes.fromhex(outcome["sender"].removeprefix("0x"))
        assert checked.intrinsic_gas == int(outcome["intrinsicGas"], 16)
        assert transactions.tx_hash(fork, tx) == bytes.fromhex(outcome["hash"].removeprefix("0x"))
