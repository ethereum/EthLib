"""The rules of the readers of the parameters that the official fixtures do not cover."""

from typing import TYPE_CHECKING, get_args

import pytest

from ethlib.execution import rpc
from raising import raises

# The code of invalid parameters, from its group, without its sign.
INVALID_PARAMS = -next(
    error.code
    for group in rpc.error_groups()
    for error in group.errors
    if error.message == "Invalid params"
)

# A hash of 32 bytes in hex, with a nonzero first digit.
HASH = "0x" + "1" + "0" * 63
HASH_BYTES = bytes([0x10]) + bytes(31)

# One value of each schema, with what it reads as.
# Each reading is worked out by hand from `base-types.yaml` and `block.yaml` of the source.
ACCEPTED = [
    pytest.param("byte", "0x5", 5, id="byte-one-digit"),
    pytest.param("byte", "0x05", 5, id="byte-leading-zero"),
    pytest.param("uint", "0x0", 0, id="uint-zero"),
    pytest.param("uint", "0x10000000000000000", 2**64, id="uint-above-64-bits"),
    pytest.param("uint32", "0xffffffff", 2**32 - 1, id="uint32-max"),
    pytest.param("uint64", "0xffffffffffffffff", 2**64 - 1, id="uint64-max"),
    pytest.param("uint256", "0x" + "f" * 64, 2**256 - 1, id="uint256-max"),
    pytest.param("uintDecimal", "1234", 1234, id="uintDecimal"),
    pytest.param("bytes", "0x", b"", id="bytes-empty"),
    pytest.param("bytes", "0x0102", b"\x01\x02", id="bytes"),
    pytest.param("bytesMax32", "0x1", bytes(31) + b"\x01", id="bytesMax32-odd"),
    pytest.param("bytesMax32", "0x" + "ab" * 32, b"\xab" * 32, id="bytesMax32-full"),
    pytest.param("bytes4", "0x" + "ab" * 4, b"\xab" * 4, id="bytes4"),
    pytest.param("bytes8", "0x" + "ab" * 8, b"\xab" * 8, id="bytes8"),
    pytest.param("bytes16", "0x" + "ab" * 16, b"\xab" * 16, id="bytes16"),
    pytest.param("bytes32", "0x" + "ab" * 32, b"\xab" * 32, id="bytes32"),
    pytest.param("bytes48", "0x" + "ab" * 48, b"\xab" * 48, id="bytes48"),
    pytest.param("bytes65", "0x" + "ab" * 65, b"\xab" * 65, id="bytes65"),
    pytest.param("bytes96", "0x" + "ab" * 96, b"\xab" * 96, id="bytes96"),
    pytest.param("bytes256", "0x" + "ab" * 256, b"\xab" * 256, id="bytes256"),
    pytest.param("hash32", HASH, HASH_BYTES, id="hash32"),
    pytest.param("address", "0x" + "AB" * 20, b"\xab" * 20, id="address-uppercase"),
    pytest.param("BlockNumberOrTag", "0x32", ("number", 50), id="number"),
    pytest.param("BlockNumberOrTagForRange", "finalized", ("tag", "finalized"), id="range-tag"),
    pytest.param("BlockNumberOrTagOrHash", "safe", ("tag", "safe"), id="tag-or-hash"),
]


@pytest.mark.parametrize(("schema", "value", "reading"), ACCEPTED)
def test_accepted(schema: rpc.Schema, value: object, reading: object) -> None:
    """A value in the pattern of its schema reads as the number, bytes or block it writes."""
    assert rpc.read_param(schema, value) == reading


def test_every_schema_has_a_case() -> None:
    """The table of accepted values covers every schema that the wrapper names."""
    schemas = {*get_args(rpc.NumberSchema), *get_args(rpc.BytesSchema), *get_args(rpc.BlockSchema)}
    assert {case.values[0] for case in ACCEPTED} == schemas


# One value outside the pattern of a schema, with the reason of the reader.
REJECTED = [
    pytest.param("byte", "0x123", "byte: not one or two hex digits", id="byte-three-digits"),
    pytest.param("uint", "0x01", "uint: leading zero", id="uint-leading-zero"),
    pytest.param("uint", "0x", "uint: no digits", id="uint-no-digits"),
    pytest.param("uint", 5, "uint: not a string", id="uint-json-number"),
    # Python bytes have no JSON form, though the extension would carry them as hex text.
    pytest.param("uint", b"0x1", "uint: not a JSON value", id="uint-python-bytes"),
    pytest.param("uint32", "0x100000000", "uint32: above 2^32", id="uint32-overflow"),
    pytest.param("uint64", "0x10000000000000000", "uint64: above 2^64", id="uint64-overflow"),
    pytest.param("uint256", "0x1" + "0" * 64, "uint256: above 2^256", id="uint256-overflow"),
    pytest.param("uintDecimal", "012", "uintDecimal: leading zero", id="decimal-leading-zero"),
    pytest.param("uintDecimal", "12a", "uintDecimal: not a decimal digit", id="decimal-hex"),
    pytest.param("bytes", "0x123", "bytes: odd number of hex digits", id="bytes-odd"),
    pytest.param("bytes", "0xAB", "bytes: not a hex digit", id="bytes-uppercase"),
    pytest.param("bytes4", "0x010203", "bytes4: 3 bytes, not 4", id="bytes4-short"),
    pytest.param("hash32", "0x" + "AB" * 32, "hash32: not a hex digit", id="hash32-uppercase"),
    pytest.param("address", "0x" + "ab" * 19, "address: 19 bytes, not 20", id="address-short"),
    pytest.param(
        "BlockNumberOrTag", "Latest", "BlockNumberOrTag: no 0x marker", id="tag-capitalized"
    ),
    pytest.param(
        "BlockNumberOrTagOrHash",
        5,
        "BlockNumberOrTagOrHash: not a string or an object",
        id="block-json-number",
    ),
]


@pytest.mark.parametrize(("schema", "value", "reason"), REJECTED)
def test_rejected(schema: rpc.Schema, value: object, reason: str) -> None:
    """A value outside the pattern of its schema raises the code of invalid parameters."""
    with raises(rpc.RpcError, reason) as error:
        rpc.read_param(schema, value)
    assert error.value.code == INVALID_PARAMS


def test_unknown_schema() -> None:
    """A name that is no schema of the reader raises code 0."""
    with raises(rpc.RpcError, "unknown schema: Quantity") as error:
        rpc.read_param("Quantity", "0x1")  # ty: ignore[no-matching-overload]  # not a schema
    assert error.value.code == 0


def test_sixty_four_digits_read_as_a_hash() -> None:
    """A string of 64 digits that is both a number and a hash reads as a hash where both fit."""
    assert rpc.read_param("BlockNumberOrTagOrHash", HASH) == ("hash", HASH_BYTES, False)
    assert rpc.read_param("BlockNumberOrTag", HASH) == ("number", 2**252)


def test_sixty_three_digits_read_as_a_number() -> None:
    """A string of 63 digits is no hash, so it reads as a number."""
    assert rpc.read_param("BlockNumberOrTagOrHash", HASH[:-1]) == ("number", 2**248)


@pytest.mark.parametrize("tag", get_args(rpc.BlockTag))
def test_every_tag_names_a_block(tag: rpc.BlockTag) -> None:
    """Each of the five tags reads as itself."""
    assert rpc.read_param("BlockNumberOrTag", tag) == ("tag", tag)


def test_pending_is_no_block_of_a_range() -> None:
    """The tag `pending` names a block, but not one end of a range."""
    assert rpc.read_param("BlockNumberOrTag", "pending") == ("tag", "pending")
    reason = "BlockNumberOrTagForRange: pending is not a block of a range"
    with raises(rpc.RpcError, reason) as error:
        rpc.read_param("BlockNumberOrTagForRange", "pending")
    assert error.value.code == INVALID_PARAMS


@pytest.mark.parametrize(
    ("flag", "canonical"),
    [({}, False), ({"requireCanonical": False}, False), ({"requireCanonical": True}, True)],
    ids=["absent", "false", "true"],
)
def test_require_canonical(flag: dict[str, object], canonical: bool) -> None:
    """The flag of an object of EIP-1898 is false when it is absent."""
    value = {"blockHash": HASH, **flag}
    assert rpc.read_param("BlockNumberOrTagOrHash", value) == ("hash", HASH_BYTES, canonical)


# One object of EIP-1898 that the reader rejects, with its reason.
REJECTED_OBJECTS = [
    pytest.param(
        {"blockHash": HASH, "extra": True},
        "a member other than blockHash and requireCanonical",
        id="hash-unknown-member",
    ),
    pytest.param(
        {"blockNumber": "0x1", "requireCanonical": True},
        "a member other than blockNumber",
        id="number-with-flag",
    ),
    pytest.param(
        {"blockHash": HASH, "requireCanonical": None},
        "requireCanonical is not a boolean",
        id="null-flag",
    ),
    pytest.param(
        {"blockHash": HASH, "requireCanonical": "true"},
        "requireCanonical is not a boolean",
        id="string-flag",
    ),
    pytest.param({"blockHash": None}, "not a string", id="null-hash"),
    pytest.param({"blockNumber": None}, "not a string", id="null-number"),
    pytest.param(
        {"blockNumber": "0x1", "blockHash": HASH},
        "not one block number or one block hash",
        id="number-and-hash",
    ),
    pytest.param({}, "not one block number or one block hash", id="empty"),
]


@pytest.mark.parametrize(("value", "fault"), REJECTED_OBJECTS)
def test_rejected_object(value: dict[str, object], fault: str) -> None:
    """An object with another member, a null member, or not exactly one block is rejected."""
    with raises(rpc.RpcError, f"BlockNumberOrTagOrHash: {fault}") as error:
        rpc.read_param("BlockNumberOrTagOrHash", value)
    assert error.value.code == INVALID_PARAMS


# The type checker checks what each overload returns.
# These lines never run, since the suites also run on Python 3.10, which lacks `assert_type`.
if TYPE_CHECKING:
    from typing import assert_type

    def check_overloads() -> None:
        """A number schema reads as an int, a byte string as bytes, a block as a tuple."""
        assert_type(rpc.read_param("uint64", "0x1"), int)
        assert_type(rpc.read_param("hash32", HASH), bytes)
        assert_type(rpc.read_param("BlockNumberOrTag", "latest"), rpc.BlockParam)
