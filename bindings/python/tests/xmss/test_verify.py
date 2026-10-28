"""Test-vector generator: `verify`.

The keys and signatures come from the committed `key_gen` and `sign` cases.

Each rejection changes one input, so it fails at one known step.
"""

import pytest

from ethlib.cryptography import xmss

from . import fixtures as F
from dumper import hex_str, write_case


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


def _emit(case: str, public_key: bytes, message: bytes, signature: bytes,
          expected: bool | None) -> None:
    # Inputs of the wrong length are rejected, written as a null output.
    try:
        result = xmss.verify(public_key, message, signature)
    except (ValueError, RuntimeError):
        result = None
    assert result == expected
    write_case("xmss", HANDLER, case, {
        "input": {
            "public_key": hex_str(public_key),
            "message":    hex_str(message),
            "signature":  hex_str(signature),
        },
        "output": result,
    })


def _key() -> bytes:
    return F.read_output("key_gen", "key_gen_known_answer")


def _signature(case: str = "sign_known_answer") -> bytes:
    return F.read_output("sign", case)


# ---- Accepted ----------------------------------------------------------------

@pytest.mark.parametrize("case", [
    "sign_known_answer", "sign_first_leaf", "sign_second_tree", "sign_last_leaf",
])
def test_valid(case: str) -> None:
    _emit(f"{HANDLER}_valid_{case.removeprefix('sign_')}",
          _key(), F.MESSAGE_KNOWN_ANSWER, _signature(case), expected=True)


# ---- Rejected: one changed input ------------------------------------------------

def test_wrong_message() -> None:
    # The bottom digest changes, so it is no codeword.
    _emit(f"{HANDLER}_wrong_message",
          _key(), F.flip(F.MESSAGE_KNOWN_ANSWER, 0), _signature(), expected=False)


def test_wrong_leaf_index() -> None:
    # 0xA5C37E19 becomes 0xA5C37E18: every bottom address changes.
    _emit(f"{HANDLER}_wrong_leaf_index",
          _key(), F.MESSAGE_KNOWN_ANSWER, F.flip(_signature(), 0), expected=False)


@pytest.mark.parametrize("layer, start", [("bottom", BOTTOM), ("top", TOP)])
@pytest.mark.parametrize("field, offset", [
    ("randomizer", 0), ("chain_value", CHAINS), ("sibling", SIBLINGS),
])
def test_tampered(layer: str, start: int, field: str, offset: int) -> None:
    # One flipped bit in the first value of one field of one layer.
    _emit(f"{HANDLER}_tampered_{layer}_{field}",
          _key(), F.MESSAGE_KNOWN_ANSWER, F.flip(_signature(), start + offset),
          expected=False)


def test_tampered_top_last_sibling() -> None:
    # The last byte of the signature: the sibling just below the key's root.
    signature = _signature()
    _emit(f"{HANDLER}_tampered_top_last_sibling",
          _key(), F.MESSAGE_KNOWN_ANSWER, F.flip(signature, len(signature) - 1),
          expected=False)


def test_wrong_root() -> None:
    # The public key is the root, then the public parameter.
    _emit(f"{HANDLER}_wrong_root",
          F.flip(_key(), 0), F.MESSAGE_KNOWN_ANSWER, _signature(), expected=False)


def test_wrong_public_param() -> None:
    _emit(f"{HANDLER}_wrong_public_param",
          F.flip(_key(), 16), F.MESSAGE_KNOWN_ANSWER, _signature(), expected=False)


def test_other_key() -> None:
    # A valid signature, checked under the key of another seed.
    _emit(f"{HANDLER}_other_key",
          F.read_output("key_gen", "key_gen_zero_seed"), F.MESSAGE_KNOWN_ANSWER,
          _signature(), expected=False)


# ---- Rejected: wrong lengths --------------------------------------------------

def test_short_public_key() -> None:
    _emit(f"{HANDLER}_short_public_key",
          _key()[:31], F.MESSAGE_KNOWN_ANSWER, _signature(), expected=None)


def test_short_message() -> None:
    _emit(f"{HANDLER}_short_message",
          _key(), F.MESSAGE_KNOWN_ANSWER[:31], _signature(), expected=None)


def test_short_signature() -> None:
    _emit(f"{HANDLER}_short_signature",
          _key(), F.MESSAGE_KNOWN_ANSWER, _signature()[:-1], expected=None)


def test_long_signature() -> None:
    _emit(f"{HANDLER}_long_signature",
          _key(), F.MESSAGE_KNOWN_ANSWER, _signature() + b"\x00", expected=None)
