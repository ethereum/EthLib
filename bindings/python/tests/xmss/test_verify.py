"""Test-vector generator: `verify`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import xmss

from . import fixtures

# The keys and signatures come from the committed `key_gen` and `sign` cases.
# Each rejection changes one input, so it fails at one known step.

HANDLER = "verify"

# Where each field of a signature starts.
#
#     [ leaf index: 4 | bottom layer: 1200 | top layer: 1200 ]
#
#     layer = [ randomizer: 16 | 58 chain values: 928 | 16 siblings: 256 ]
BOTTOM = 4
TOP = 4 + 1200
CHAINS = 16
SIBLINGS = 16 + 58 * 16


def _emit(
    case: str, public_key: bytes, message: bytes, signature: bytes, expected: bool | None
) -> None:
    # Inputs of the wrong length are rejected, written as a null output.
    try:
        result = xmss.verify(public_key, message, signature)
    except (ValueError, RuntimeError):
        result = None
    assert result == expected
    write_case(
        "xmss",
        HANDLER,
        case,
        {
            "input": {
                "public_key": hex_str(public_key),
                "message": hex_str(message),
                "signature": hex_str(signature),
            },
            "output": result,
        },
    )


def _key() -> bytes:
    return fixtures.read_output("key_gen", "key_gen_known_answer")


def _signature(case: str = "sign_known_answer") -> bytes:
    return fixtures.read_output("sign", case)


# ---- Accepted ----------------------------------------------------------------


@pytest.mark.parametrize(
    "case",
    [
        "sign_known_answer",
        "sign_first_leaf",
        "sign_second_tree",
        "sign_last_leaf",
    ],
)
def test_valid(case: str) -> None:
    _emit(
        f"{HANDLER}_valid_{case.removeprefix('sign_')}",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(case),
        expected=True,
    )


# ---- Rejected: one changed input ------------------------------------------------


def test_wrong_message() -> None:
    # The bottom digest changes, so it is no codeword.
    _emit(
        f"{HANDLER}_wrong_message",
        _key(),
        fixtures.flip(fixtures.MESSAGE_KNOWN_ANSWER, 0),
        _signature(),
        expected=False,
    )


def test_wrong_leaf_index() -> None:
    # 0xA5C37E19 becomes 0xA5C37E18: every bottom address changes.
    _emit(
        f"{HANDLER}_wrong_leaf_index",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        fixtures.flip(_signature(), 0),
        expected=False,
    )


@pytest.mark.parametrize("layer, start", [("bottom", BOTTOM), ("top", TOP)])
@pytest.mark.parametrize(
    "field, offset",
    [
        ("randomizer", 0),
        ("chain_value", CHAINS),
        ("sibling", SIBLINGS),
    ],
)
def test_tampered(layer: str, start: int, field: str, offset: int) -> None:
    # One flipped bit in the first value of one field of one layer.
    _emit(
        f"{HANDLER}_tampered_{layer}_{field}",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        fixtures.flip(_signature(), start + offset),
        expected=False,
    )


def test_tampered_top_last_sibling() -> None:
    # The last byte of the signature: the sibling just below the key's root.
    signature = _signature()
    _emit(
        f"{HANDLER}_tampered_top_last_sibling",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        fixtures.flip(signature, len(signature) - 1),
        expected=False,
    )


def test_zeroed_message_byte() -> None:
    # The first byte of the message becomes 0x00, so the bottom layer signs another digest.
    message = b"\x00" + fixtures.MESSAGE_KNOWN_ANSWER[1:]
    _emit(f"{HANDLER}_zeroed_message_byte", _key(), message, _signature(), expected=False)


def test_next_leaf_index() -> None:
    # 0xA5C37E19 becomes 0xA5C37E1A, the next leaf: every bottom address changes.
    # The leaf index is the first 4 bytes of the signature, least significant first.
    signature = (fixtures.LEAF_KNOWN_ANSWER + 1).to_bytes(4, "little") + _signature()[4:]
    _emit(
        f"{HANDLER}_next_leaf_index",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        signature,
        expected=False,
    )


def test_zeroed_top_last_sibling() -> None:
    # The sibling just below the key's root, the last 16 bytes, becomes all zero.
    signature = _signature()[:-16] + bytes(16)
    _emit(
        f"{HANDLER}_zeroed_top_last_sibling",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        signature,
        expected=False,
    )


def test_wrong_root() -> None:
    # The public key is the root, then the public parameter.
    _emit(
        f"{HANDLER}_wrong_root",
        fixtures.flip(_key(), 0),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_wrong_public_param() -> None:
    _emit(
        f"{HANDLER}_wrong_public_param",
        fixtures.flip(_key(), 16),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_other_key() -> None:
    # A valid signature, checked under the key of another seed.
    _emit(
        f"{HANDLER}_other_key",
        fixtures.read_output("key_gen", "key_gen_zero_seed"),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


# ---- Rejected: wrong lengths --------------------------------------------------


def test_short_public_key() -> None:
    _emit(
        f"{HANDLER}_short_public_key",
        _key()[:31],
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=None,
    )


def test_short_message() -> None:
    _emit(
        f"{HANDLER}_short_message",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER[:31],
        _signature(),
        expected=None,
    )


def test_short_signature() -> None:
    _emit(
        f"{HANDLER}_short_signature",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature()[:-1],
        expected=None,
    )


def test_long_signature() -> None:
    _emit(
        f"{HANDLER}_long_signature",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature() + b"\x00",
        expected=None,
    )
