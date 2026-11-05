"""Transactions against the transaction tests of ethereum/tests."""

import json
import re
from pathlib import Path

import pytest

from ethlib.execution import transactions

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

# The forks in activation order, as far as the fixtures go.
FORKS = list(dict.fromkeys(FORK_OF_NETWORK.values()))

# The first fork of each transaction type of EIP-2718.
FIRST_FORK_OF_TYPE = {0: "frontier", 1: "berlin", 2: "london", 3: "dencun", 4: "pectra"}

# The fixtures run on chain 1.
CHAIN_ID = 1

# The index of each field in the payload of each type, by the names that the exceptions use.
FIELDS = {
    0: {
        "NONCE": 0,
        "GASPRICE": 1,
        "GASLIMIT": 2,
        "TO": 3,
        "VALUE": 4,
        "DATA": 5,
        "V": 6,
        "R": 7,
        "S": 8,
    },
    1: {
        "NONCE": 1,
        "GASPRICE": 2,
        "GASLIMIT": 3,
        "TO": 4,
        "VALUE": 5,
        "DATA": 6,
        "ACCESS_LIST": 7,
        "R": 9,
        "S": 10,
    },
    2: {
        "NONCE": 1,
        "PRIORITY": 2,
        "MAXFEE": 3,
        "GASLIMIT": 4,
        "TO": 5,
        "VALUE": 6,
        "DATA": 7,
        "ACCESS_LIST": 8,
        "R": 10,
        "S": 11,
    },
}

# The results that ethereum/tests rejects and EthLib accepts, by file and exception.
#
# The fixtures reject a gas limit of 2^64 and a gas limit times gas price above 2^256 - 1.
# The Yellow Paper (Berlin version, section 4.2) types the gas limit and gas price as scalars
# below 2^256.
# Its section 6.2 computes the up-front cost in the naturals, and checks it against the balance.
# Its section 6.2 also checks the gas limit against the gas left in the block.
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

# A gas limit below the intrinsic gas.
_SHORT_OF_GAS = "insufficientGas"

# Transactions with a second fault, which EthLib reports before the one the fixture names.
SECOND_FAULT = {
    # The data of these transactions costs more than their gas limit of 21000 or 2000.
    **{
        f"ttVValue/{name}.json": _SHORT_OF_GAS
        for name in (
            "V_overflow32bit",
            "V_overflow32bitSigned",
            "V_wrongvalue_101",
            "V_wrongvalue_121",
            "V_wrongvalue_122",
            "V_wrongvalue_123",
            "V_wrongvalue_124",
            "V_wrongvalue_ff",
            "V_wrongvalue_ffff",
        )
    },
    "ttWrongRLP/TRANSCT_rvalue_TooShort.json": _SHORT_OF_GAS,
    # The empty transaction has a gas limit of 0.
    "ttSignature/EmptyTransaction.json": _SHORT_OF_GAS,
    # The gas limit 00 00 00 00 00 00 00 00 01 is written with leading zero bytes.
    "ttGasLimit/TransactionWithGasLimitOverflowZeros64.json": "leadingZeroInScalar",
}


def _sized(pattern: str, compare):
    """Whether a message holds the pattern, and its last number passes `compare`."""

    def check(message: str, kind: int) -> bool:
        match = re.search(pattern.format(**FIELDS.get(kind, {})) + r" (\d+)$", message)
        return match is not None and compare(int(match.group(1)))

    return check


def _field(name: str, fault: str):
    """Whether a message names a fault of one field of the payload."""

    def check(message: str, kind: int) -> bool:
        index = FIELDS[kind][name]
        return re.search(rf"decoding: field {index}: {fault}", message) is not None

    return check


def _any(*rules):
    def check(message: str, kind: int) -> bool:
        return any(
            rule(message, kind) if callable(rule) else re.search(rule, message) is not None
            for rule in rules
        )

    return check


_TOO_LARGE = r"scalarTooLarge \d+ 256$"
_TOO_SHORT = r"decoding: inputTooShort \d+ \d+$"

# Whether an error message names each exception of the fixtures.
NAMES = {
    "ADDRESS_TOO_LONG": _sized(r"decoding: field {TO}: wrongLength 20", lambda n: n > 20),
    "ADDRESS_TOO_SHORT": _sized(r"decoding: field {TO}: wrongLength 20", lambda n: n < 20),
    "EC_RECOVERY_FAIL": _any(r"^invalidSignature$"),
    "GASLIMIT_OVERFLOW": _field("GASLIMIT", _TOO_LARGE),
    "GASPRICE_OVERFLOW": _any(
        lambda m, k: k != 2 and _field("GASPRICE", _TOO_LARGE)(m, k),
        lambda m, k: k == 2 and _field("MAXFEE", _TOO_LARGE)(m, k),
    ),
    "INITCODE_SIZE_EXCEEDED": _any(r"^initCodeTooLarge \d+$"),
    "INTRINSIC_GAS_TOO_LOW": _any(r"^insufficientGas \d+ \d+$"),
    "INTRINSIC_NO_FLOOR_GAS": _any(r"^insufficientGas \d+ \d+$"),
    # A v below 35 other than 27 and 28 encodes no chain at all, which EthLib calls an
    # invalid signature.
    "INVALID_CHAINID": _any(rf"^wrongChainId {CHAIN_ID} \d+$", r"^invalidSignature$"),
    # An r or s of 2^256 or more is no scalar of the signature.
    "INVALID_SIGNATURE_VRS": _any(
        r"^invalidSignature$", _field("R", _TOO_LARGE), _field("S", _TOO_LARGE)
    ),
    "NONCE_OVERFLOW": _any(r"^nonceOverflow$", _field("NONCE", _TOO_LARGE)),
    "NONCE_TOO_BIG": _any(r"^nonceOverflow$"),
    "PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS_2": _any(r"^priorityFeeGreaterThanMaxFee$"),
    "PRIORITY_OVERFLOW": _field("PRIORITY", _TOO_LARGE),
    "RLP_ERROR_EOF": _any(_TOO_SHORT),
    "RLP_ERROR_SIZE": _any(_TOO_SHORT, r"^decoding: trailingBytes \d+$"),
    "RLP_ERROR_SIZE_LEADING_ZEROS": _any(r"^decoding: leadingZeroInLength$"),
    "RLP_INVALID_ACCESS_LIST_ADDRESS_TOO_LONG": _sized(
        r"decoding: field {ACCESS_LIST}: field 0: wrongLength 20", lambda n: n > 20
    ),
    "RLP_INVALID_ACCESS_LIST_ADDRESS_TOO_SHORT": _sized(
        r"decoding: field {ACCESS_LIST}: field 0: wrongLength 20", lambda n: n < 20
    ),
    "RLP_INVALID_ACCESS_LIST_STORAGE_TOO_LONG": _sized(
        r"decoding: field {ACCESS_LIST}: field 1: wrongLength 32", lambda n: n > 32
    ),
    "RLP_INVALID_ACCESS_LIST_STORAGE_TOO_SHORT": _sized(
        r"decoding: field {ACCESS_LIST}: field 1: wrongLength 32", lambda n: n < 32
    ),
    "RLP_INVALID_DATA": _field("DATA", r"listAsBytes$"),
    "RLP_LEADING_ZEROS_BASEFEE": _field("MAXFEE", r"leadingZeroInScalar$"),
    "RLP_LEADING_ZEROS_DATA_SIZE": _any(r"^decoding: leadingZeroInLength$"),
    "RLP_LEADING_ZEROS_NONCE_SIZE": _any(r"^decoding: singleByteWithPrefix \d+$"),
    "RLP_LEADING_ZEROS_PRIORITY_FEE": _field("PRIORITY", r"leadingZeroInScalar$"),
    "RLP_TOO_FEW_ELEMENTS": _sized(r"decoding: wrongFieldCount 9", lambda n: n < 9),
    "RLP_TOO_MANY_ELEMENTS": _sized(r"decoding: wrongFieldCount 9", lambda n: n > 9),
    # A type 4 transaction has 13 fields.
    "RLP_WrongAuthEncoding": _sized(r"decoding: wrongFieldCount 13", lambda n: n != 13),
    "TYPE_NOT_SUPPORTED": _any(r"^unsupportedType \d+$"),
    "VALUE_OVERFLOW": _field("VALUE", _TOO_LARGE),
}

for _name in ("GASLIMIT", "GASPRICE", "NONCE", "R", "S", "TO", "V", "VALUE"):
    NAMES[f"RLP_LEADING_ZEROS_{_name}"] = _field(_name, r"leadingZeroInScalar$")
    # A field written as a list can announce more bytes than the transaction holds.
    # Then the list of the transaction fails before the field is read.
    NAMES[f"RLP_INVALID_{_name}"] = _any(_field(_name, r"list"), _TOO_SHORT)
NAMES["RLP_INVALID_SIGNATURE_R"] = NAMES.pop("RLP_INVALID_R")
NAMES["RLP_INVALID_SIGNATURE_S"] = NAMES.pop("RLP_INVALID_S")
NAMES["RLP_INVALID_HEADER"] = _any(_TOO_SHORT)


def kind_of(tx: bytes) -> int | None:
    """The EIP-2718 type of a transaction, 0 for a legacy one, or None for neither form."""
    if not tx or 0x80 <= tx[0] < 0xC0:
        return None
    return tx[0] if tx[0] < 0x80 else 0


def names(path: str, exception: str, message: str, fork: str, tx: bytes) -> bool:
    """Whether an error message names one of the exceptions of a result."""
    kind = kind_of(tx)
    # EIP-2718: a transaction is an RLP list, or a type byte below 0x80 and a payload.
    if kind is None:
        return re.fullmatch(r"unsupportedType \d+", message) is not None
    # A type that the fork does not have rejects the transaction before its payload.
    if kind not in FIRST_FORK_OF_TYPE or FORKS.index(fork) < FORKS.index(FIRST_FORK_OF_TYPE[kind]):
        return message == f"unsupportedType {kind}"
    second = SECOND_FAULT.get(path)
    if second is not None and second in message:
        return True
    expected = exception.removeprefix("TransactionException.").split("|")
    return any(NAMES[name](message, kind) for name in expected)


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
        with pytest.raises(ValueError) as error:
            transactions.check(fork, CHAIN_ID, tx)
        message = str(error.value)
        assert names(path, outcome["exception"], message, fork, tx), message
        # Where the fixture gives the intrinsic gas of a rejected transaction, it must agree.
        intrinsic = int(outcome["intrinsicGas"], 16)
        if intrinsic and not message.startswith(("decoding", "unsupportedType")):
            assert transactions.intrinsic_gas(fork, tx) == intrinsic
    else:
        checked = transactions.check(fork, CHAIN_ID, tx)
        assert checked.sender == bytes.fromhex(outcome["sender"].removeprefix("0x"))
        assert checked.intrinsic_gas == int(outcome["intrinsicGas"], 16)
        assert transactions.tx_hash(fork, tx) == bytes.fromhex(outcome["hash"].removeprefix("0x"))
