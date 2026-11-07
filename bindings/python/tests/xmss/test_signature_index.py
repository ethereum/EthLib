"""Test-vector generator: `signature_index`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import xmss

from . import fixtures

# Each signature carries its leaf index in its first 4 bytes, little-endian.
# The expected index of each signed case is the index it was signed at, not a value read back.

HANDLER = "signature_index"


def _emit(case: str, signature: bytes, expected: int | None) -> None:
    # Inputs of the wrong length are rejected, written as a null output.
    try:
        result = xmss.signature_index(signature)
    except (ValueError, RuntimeError):
        result = None
    assert result == expected
    write_case(
        "xmss",
        HANDLER,
        case,
        {
            "input": {"signature": hex_str(signature)},
            "output": result,
        },
    )


# ---- Signed cases ------------------------------------------------------------


@pytest.mark.parametrize(
    "case, leaf_index",
    [
        ("sign_known_answer", fixtures.LEAF_KNOWN_ANSWER),
        ("sign_first_leaf", fixtures.LEAF_FIRST),
        ("sign_second_tree", fixtures.LEAF_SECOND_TREE),
        ("sign_last_leaf", fixtures.LEAF_LAST),
    ],
)
def test_signed(case: str, leaf_index: int) -> None:
    # The committed signature of each sign case, read back as the index it was signed at.
    _emit(
        f"{HANDLER}_{case.removeprefix('sign_')}",
        fixtures.read_output("sign", case),
        expected=leaf_index,
    )


# ---- No verification ---------------------------------------------------------


def test_tampered() -> None:
    # A flipped bit in the bottom randomizer, the first byte after the index, breaks the signature.
    #
    # The index is before it, so it reads the same.
    signature = fixtures.read_output("sign", "sign_known_answer")
    tampered = fixtures.flip(signature, xmss.LEAF_INDEX_SIZE)
    _emit(f"{HANDLER}_tampered", tampered, expected=fixtures.LEAF_KNOWN_ANSWER)


def test_byte_order() -> None:
    # Bytes 01 02 03 04, then zeros.
    #
    # Little-endian, the first byte is the least significant: 0x04030201.
    signature = bytes([1, 2, 3, 4]) + bytes(xmss.SIG_SIZE - 4)
    _emit(f"{HANDLER}_byte_order", signature, expected=0x0403_0201)


# ---- Rejected: wrong lengths --------------------------------------------------


def test_short_signature() -> None:
    # One byte short: the index bytes are there, but the signature is not whole.
    _emit(
        f"{HANDLER}_short_signature",
        fixtures.read_output("sign", "sign_known_answer")[:-1],
        expected=None,
    )


def test_long_signature() -> None:
    _emit(
        f"{HANDLER}_long_signature",
        fixtures.read_output("sign", "sign_known_answer") + b"\x00",
        expected=None,
    )
