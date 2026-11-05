"""Transactions against the transaction tests of execution-specs."""

import json
import re
from pathlib import Path

import pytest

from ethlib.execution import transactions
from raising import raises, raises_shape

from .expected_errors import expected_template

_REPO = Path(__file__).resolve().parents[4]
_FIXTURES = _REPO / "tests" / "execution" / "transactions"

# The network of a fixture, and the case of the Lean fork type that it names.
FORK_OF_NETWORK = {
    "Frontier": "frontier",
    "Homestead": "homestead",
    "TangerineWhistle": "tangerineWhistle",
    "SpuriousDragon": "spuriousDragon",
    "Byzantium": "byzantium",
    "ConstantinopleFix": "petersburg",
    "Istanbul": "istanbul",
    "Berlin": "berlin",
    "London": "london",
    "Paris": "paris",
    "Shanghai": "shapella",
    "Cancun": "dencun",
    "Prague": "pectra",
    "Osaka": "fusaka",
    "Amsterdam": "glamsterdam",
}

# The fixtures run on chain 1.
CHAIN_ID = 1

# The index of each field of a legacy transaction, by the name that the exceptions use.
LEGACY_FIELD = {
    "NONCE": 0,
    "GASPRICE": 1,
    "GASLIMIT": 2,
    "TO": 3,
    "VALUE": 4,
    "DATA": 5,
    "V": 6,
    "R": 7,
    "SIGNATURE_R": 7,
    "S": 8,
    "SIGNATURE_S": 8,
}

# The field of a type 4 transaction that holds the authorizations.
AUTHS = 9


def _field_count(message: str, compare) -> bool:
    """Whether the message is a legacy field count that passes `compare`."""
    match = re.search(r"decoding: wrongFieldCount 9 (\d+)", message)
    return match is not None and compare(int(match.group(1)))


def _address_length(message: str, compare) -> bool:
    """Whether the recipient has a wrong length that passes `compare`."""
    match = re.search(r"decoding: field 3: wrongLength 20 (\d+)", message)
    return match is not None and compare(int(match.group(1)))


def names(exception: str, message: str) -> bool:
    """Whether an error message names a fixture exception, such as `RLP_INVALID_TO`."""
    name = exception.removeprefix("TransactionException.")
    fixed = {
        "RLP_ERROR_EOF": r"decoding: inputTooShort|emptyTransaction",
        "RLP_ERROR_SIZE": r"decoding: trailingBytes",
        "RLP_ERROR_SIZE_LEADING_ZEROS": r"decoding: leadingZeroInLength",
        "RLP_LEADING_ZEROS_DATA_SIZE": r"decoding: (leadingZeroInLength|longFormForShortLength)",
        "RLP_LEADING_ZEROS_NONCE_SIZE": r"decoding: singleByteWithPrefix",
        "RLP_INVALID_HEADER": r"decoding: (?!field )",
        "TYPE_NOT_SUPPORTED": r"unsupportedType|emptyTransaction",
        "VALUE_OVERFLOW": r"decoding: field 4: scalarTooLarge",
        "NONCE_OVERFLOW": r"nonceOverflow",
        "INVALID_SIGNATURE_VRS": r"invalidSignature",
        "INVALID_CHAINID": r"wrongChainId",
        "TYPE_4_EMPTY_AUTHORIZATION_LIST": r"emptyAuthorizationList",
        "TYPE_4_INVALID_AUTHORIZATION_FORMAT": rf"decoding: (field {AUTHS}: |(?!field ))",
        "TYPE_4_INVALID_AUTHORITY_SIGNATURE": rf"decoding: field {AUTHS}: ",
        "TYPE_4_INVALID_AUTHORITY_SIGNATURE_S_TOO_HIGH": rf"decoding: field {AUTHS}: ",
    }
    if name in fixed:
        return re.search(fixed[name], message) is not None
    if name == "RLP_TOO_FEW_ELEMENTS":
        return _field_count(message, lambda n: n < 9)
    if name == "RLP_TOO_MANY_ELEMENTS":
        return _field_count(message, lambda n: n > 9)
    if name == "ADDRESS_TOO_SHORT":
        return _address_length(message, lambda n: n < 20)
    if name == "ADDRESS_TOO_LONG":
        return _address_length(message, lambda n: n > 20)
    if name.startswith("RLP_LEADING_ZEROS_"):
        field = LEGACY_FIELD[name.removeprefix("RLP_LEADING_ZEROS_")]
        return re.search(rf"decoding: field {field}: leadingZeroInScalar", message) is not None
    if name.startswith("RLP_INVALID_"):
        field = LEGACY_FIELD[name.removeprefix("RLP_INVALID_")]
        return re.search(rf"decoding: field {field}: ", message) is not None
    raise KeyError(f"no rule for the exception {exception}")


def _vectors():
    """Every vector of the fixtures."""
    for path in sorted(_FIXTURES.rglob("*.json")):
        for name, fixture in json.loads(path.read_text()).items():
            for network, outcome in fixture["result"].items():
                case_id = f"{network}-{path.stem}-{name.split('[')[-1][:70]}"
                tx = bytes.fromhex(fixture["txbytes"].removeprefix("0x"))
                yield pytest.param(network, tx, outcome, id=case_id)


VECTORS = list(_vectors())


def test_every_fork_is_covered():
    """The copy holds vectors for each fork from Frontier to Amsterdam."""
    assert {vector.values[0] for vector in VECTORS} == set(FORK_OF_NETWORK)


@pytest.mark.parametrize("network, tx, outcome", VECTORS)
def test_vector(network: str, tx: bytes, outcome: dict):
    """The checks reach the outcome of the fixture at its fork."""
    fork = FORK_OF_NETWORK[network]
    if "exception" in outcome:
        intrinsic = int(outcome.get("intrinsicGas", "0x0"), 16) or None
        template = expected_template(outcome["exception"], fork, tx, CHAIN_ID, intrinsic)
        with raises_shape(ValueError, template):
            transactions.check(fork, CHAIN_ID, tx)
    else:
        checked = transactions.check(fork, CHAIN_ID, tx)
        assert checked.sender == bytes.fromhex(outcome["sender"].removeprefix("0x"))
        assert checked.intrinsic_gas == int(outcome["intrinsicGas"], 16)
        assert transactions.tx_hash(fork, tx) == bytes.fromhex(outcome["hash"].removeprefix("0x"))
        assert transactions.recover_sender(fork, tx) == checked.sender
        assert transactions.intrinsic_gas(fork, tx) == checked.intrinsic_gas


def test_unknown_fork():
    """A fork name that is not a case of the fork type raises ValueError."""
    with raises(ValueError, "no fork named notAFork"):
        transactions.tx_type("notAFork", b"\xc0")


def test_type_of_typed_transaction():
    """The type 4 exists from Pectra on."""
    path = _FIXTURES / "for_osaka" / "prague" / "eip7702_set_code_tx" / "invalid_tx"
    fixture = json.loads((path / "empty_authorization_list.json").read_text())
    tx = bytes.fromhex(next(iter(fixture.values()))["txbytes"].removeprefix("0x"))
    assert transactions.tx_type("fusaka", tx) == 4
    # Before Pectra, no fork has the type 4.
    with raises(ValueError, "unsupportedType 4"):
        transactions.tx_type("dencun", tx)
