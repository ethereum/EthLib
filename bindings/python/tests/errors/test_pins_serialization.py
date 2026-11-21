"""The code and message of the errors that the RLP and SSZ exports pass to Python."""

from collections.abc import Callable

import pytest

from ethlib.errors import EthLibError, RlpError, SszError
from ethlib.serialization import rlp, ssz
from raising import raises

# An export turns the typed error of an operation into a code and a message.
# Each case pins one way of doing so, with the code and the message that Python sees.


@pytest.mark.parametrize(
    ("error", "code", "message", "call"),
    [
        # No item fits in zero bytes.
        pytest.param(
            RlpError,
            2,
            "input rejected: EthLib.Serialization.Rlp.RlpError.inputTooShort 1 0",
            lambda: rlp.decode(b""),
            id="rlp-decode",
        ),
        # Two empty strings, where one item is expected.
        pytest.param(
            RlpError,
            6,
            "input rejected: EthLib.Serialization.Rlp.RlpError.trailingBytes 1",
            lambda: rlp.decode(b"\x80\x80"),
            id="rlp-decode-trailing",
        ),
        # 0x02 is one byte, so it is the scalar 2, too large for a bool.
        pytest.param(
            RlpError,
            12,
            "input rejected: EthLib.Serialization.Rlp.RlpError.scalarTooLarge 2 1",
            lambda: rlp.decode_as("bool", b"\x02"),
            id="rlp-decode-as",
        ),
        # A scalar has no leading zero byte.
        pytest.param(
            RlpError,
            7,
            "input rejected: EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar",
            lambda: rlp.decode_as("nat", b"\x00"),
            id="rlp-decode-as-nat",
        ),
        # No RLP type has the name no such type.
        pytest.param(
            RlpError,
            0,
            "unknown RLP type",
            lambda: rlp.decode_as("no such type", b""),
            id="rlp-unknown-type",
        ),
        # The name of the type must be a str, not bytes.
        pytest.param(
            RlpError,
            0,
            "expected a str",
            lambda: rlp.decode_as(b"nat", b"\x80"),  # ty: ignore[invalid-argument-type]
            id="rlp-argument",
        ),
        # A bool is the byte 0 or 1.
        pytest.param(
            SszError,
            13,
            "input rejected: EthLib.Serialization.Ssz.Err.notABit 2",
            lambda: ssz.deserialize("bool", b"\x02"),
            id="ssz-input",
        ),
        # One byte, where the vector holds two.
        pytest.param(
            SszError,
            3,
            "value rejected: EthLib.Serialization.Ssz.Err.scope 2 1",
            lambda: ssz.serialize({"byte_vector": 2}, {"bytes": "0x00"}),
            id="ssz-value",
        ),
        # zz are not hex digits, so the value does not read.
        pytest.param(
            SszError,
            0,
            "value: bytes must be 0x and hex digits",
            lambda: ssz.serialize({"byte_vector": 2}, {"bytes": "0xzz"}),
            id="ssz-value-read",
        ),
        # No SSZ type has the name nope.
        pytest.param(
            SszError,
            0,
            "type: unknown SSZ type nope",
            lambda: ssz.deserialize({"nope": 1}, b""),
            id="ssz-type-read",
        ),
        # A vector has at least one element.
        pytest.param(
            SszError,
            50,
            "type rejected: EthLib.Serialization.Ssz.Err.vectorEmpty",
            lambda: ssz.deserialize({"byte_vector": 0}, b""),
            id="ssz-type-rejected",
        ),
        # One byte, where the vector holds two.
        pytest.param(
            SszError,
            3,
            "value rejected: EthLib.Serialization.Ssz.Err.scope 2 1",
            lambda: ssz.hash_tree_root({"byte_vector": 2}, {"bytes": "0x00"}),
            id="ssz-root",
        ),
        # The container has a field a, but none named b.
        pytest.param(
            SszError,
            0,
            "path: no field b",
            lambda: ssz.get_generalized_index({"container": [["a", "bool"]]}, "b"),
            id="ssz-path-field",
        ),
        # A bool is a leaf, so a path cannot step into it.
        pytest.param(
            SszError,
            40,
            "path rejected: EthLib.Serialization.Ssz.Err.noParts",
            lambda: ssz.get_generalized_index("bool", 0),
            id="ssz-path-index",
        ),
        # Index 5 steps below the one chunk of a bool.
        pytest.param(
            SszError,
            37,
            "proof rejected: EthLib.Serialization.Ssz.Err.pathIntoPacked",
            lambda: ssz.compute_merkle_proof("bool", {"bool": True}, 5),
            id="ssz-merkle-proof",
        ),
        # Three chunks, above the limit of two.
        pytest.param(
            SszError,
            48,
            "chunks rejected: EthLib.Serialization.Ssz.Err.merkleizeLimit 3 2",
            lambda: ssz.merkleize_chunks([bytes(32)] * 3, 2),
            id="ssz-merkleize",
        ),
    ],
)
def test_code_and_message(
    error: type[EthLibError], code: int, message: str, call: Callable[[], object]
) -> None:
    with raises(error, message) as info:
        call()
    assert type(info.value) is error
    assert info.value.code == code
