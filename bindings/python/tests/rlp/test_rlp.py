"""RLP against the RLP tests of ethereum/tests, and the typed decoders against hand-built cases.

`vectors/README.md` gives the origin of the two JSON files and their licence.
"""

import json
import re
from pathlib import Path

import pytest

from ethlib.serialization import rlp

_VECTORS = Path(__file__).resolve().parent / "vectors"
_VALID = json.loads((_VECTORS / "rlptest.json").read_text())
_INVALID = json.loads((_VECTORS / "invalidRLPTest.json").read_text())


def _scalar(n: int) -> bytes:
    # A scalar is its bytes in base 256 with no leading zero byte, so 0 is the empty string.
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _item(value) -> rlp.Item:
    """The item of an input, read as `docs/test_types/rlp_tests.rst` of ethereum/tests says.

    A list is a list, a number is a scalar, and a string is its bytes.
    A string that starts with `#` is a decimal number, so it is a scalar too.
    """
    if isinstance(value, list):
        return [_item(x) for x in value]
    if isinstance(value, int):
        return _scalar(value)
    if value.startswith("#"):
        return _scalar(int(value[1:]))
    # No input of the file starts with `0x`, the other form that the document allows.
    assert not value.startswith("0x")
    return value.encode("ascii")


def _bytes(hex_string: str) -> bytes:
    return bytes.fromhex(hex_string.removeprefix("0x"))


@pytest.mark.parametrize("name", list(_VALID))
def test_valid_case(name: str) -> None:
    case = _VALID[name]
    item = _item(case["in"])
    out = _bytes(case["out"])
    assert rlp.encode(item) == out
    assert rlp.decode(out) == item


# The fault of each invalid case, as the error names it.
# The name of each case describes its fault:
# - bytesShouldBeSingleByte: a byte below 0x80 written with a prefix;
# - nonOptimalLongLength and wrongSizeList: a length below 56 written in the long form;
# - leadingZerosInLongLength and incorrectLengthInArray: a length with a leading zero byte;
# - lessThan, int32Overflow and emptyEncoding: an input that ends before the bytes its prefix
#   announces, given as the bytes announced, then the bytes available.
# randomRLP is a list, inside which a byte string writes its length with a leading zero byte.
_FAULTS = {
    "int32Overflow": "inputTooShort 1080863910568919042 2",
    "int32Overflow2": "inputTooShort 1080863910568919042 2",
    "wrongSizeList": "longFormForShortLength 1",
    "wrongSizeList2": "longFormForShortLength 1",
    "incorrectLengthInArray": "leadingZeroInLength",
    "randomRLP": "leadingZeroInLength",
    "bytesShouldBeSingleByte00": "singleByteWithPrefix 0",
    "bytesShouldBeSingleByte01": "singleByteWithPrefix 1",
    "bytesShouldBeSingleByte7F": "singleByteWithPrefix 127",
    "leadingZerosInLongLengthArray1": "leadingZeroInLength",
    "leadingZerosInLongLengthArray2": "leadingZeroInLength",
    "leadingZerosInLongLengthList1": "leadingZeroInLength",
    "leadingZerosInLongLengthList2": "leadingZeroInLength",
    "nonOptimalLongLengthArray1": "longFormForShortLength 16",
    "nonOptimalLongLengthArray2": "longFormForShortLength 1",
    "nonOptimalLongLengthList1": "longFormForShortLength 16",
    "nonOptimalLongLengthList2": "longFormForShortLength 3",
    "emptyEncoding": "inputTooShort 1 0",
    "lessThanShortLengthArray1": "inputTooShort 1 0",
    "lessThanShortLengthArray2": "inputTooShort 32 31",
    "lessThanShortLengthList1": "inputTooShort 5 3",
    "lessThanShortLengthList2": "inputTooShort 34 7",
    "lessThanLongLengthArray1": "inputTooShort 65536 6",
    "lessThanLongLengthArray2": "inputTooShort 64 16",
    "lessThanLongLengthList1": "inputTooShort 384 0",
    "lessThanLongLengthList2": "inputTooShort 18446744073709551615 8",
}


def test_every_invalid_case_has_a_fault() -> None:
    assert set(_FAULTS) == set(_INVALID)


@pytest.mark.parametrize("name", list(_INVALID))
def test_invalid_case(name: str) -> None:
    case = _INVALID[name]
    assert case["in"] == "INVALID"
    with pytest.raises(ValueError, match=re.escape(_FAULTS[name]) + "$"):
        rlp.decode(_bytes(case["out"]))


# Hand-built cases of the typed decoders, worked out from the rules of each type.


def test_scalar() -> None:
    # 82 04 00 holds 1024, and 80, the empty byte string, holds 0.
    assert rlp.decode_as("nat", bytes.fromhex("820400")) == 1024
    assert rlp.decode_as("nat", bytes.fromhex("80")) == 0


@pytest.mark.parametrize(
    ("data", "fault"),
    [
        # The byte string 00 holds no scalar: 0 encodes as 80.
        ("00", "leadingZeroInScalar"),
        # 82 00 01 holds no scalar: 1 encodes as 01.
        ("820001", "leadingZeroInScalar"),
        # c0, the empty list, holds no scalar.
        ("c0", "listAsScalar"),
    ],
)
def test_scalar_rejected(data: str, fault: str) -> None:
    with pytest.raises(ValueError, match=re.escape(fault) + "$"):
        rlp.decode_as("nat", bytes.fromhex(data))


def test_word() -> None:
    assert rlp.decode_as("u256", bytes.fromhex("820400")) == 1024


def test_word_list_rejected() -> None:
    # c2 01 02 is a list, so it holds no word.
    with pytest.raises(ValueError, match="listAsScalar$"):
        rlp.decode_as("u256", bytes.fromhex("c20102"))


def test_bool() -> None:
    assert rlp.decode_as("bool", bytes.fromhex("80")) is False
    assert rlp.decode_as("bool", bytes.fromhex("01")) is True


def test_bool_two_rejected() -> None:
    # 02 holds no boolean: 2 is not below 2^1.
    with pytest.raises(ValueError, match=re.escape("scalarTooLarge 2 1") + "$"):
        rlp.decode_as("bool", bytes.fromhex("02"))


def test_uint64_overflow_rejected() -> None:
    # 89 01 then 8 zero bytes holds 2^64, which is no 64-bit integer.
    with pytest.raises(ValueError, match=re.escape(f"scalarTooLarge {2**64} 64") + "$"):
        rlp.decode_as("uint64", bytes.fromhex("89010000000000000000"))


def test_recipient_none() -> None:
    # 80, the empty byte string, is the recipient of a contract creation.
    assert rlp.decode_as("recipient", bytes.fromhex("80")) is None


def test_recipient_address() -> None:
    address = bytes(range(1, 21))
    assert rlp.decode_as("recipient", bytes([0x94]) + address) == address


def test_recipient_short_rejected() -> None:
    # 81 ff is one byte, which is no address.
    with pytest.raises(ValueError, match=re.escape("wrongLength 20 1") + "$"):
        rlp.decode_as("recipient", bytes.fromhex("81ff"))


def test_list_nat() -> None:
    # c2 01 02 holds the list of the integers 1 and 2.
    assert rlp.decode_as("list_nat", bytes.fromhex("c20102")) == [1, 2]


def test_unknown_kind_rejected() -> None:
    with pytest.raises(ValueError):
        rlp.decode_as("float", bytes.fromhex("80"))
