"""Test-vector generator: `verify`.

The keys and signatures come from the committed `key_gen` and `sign` cases.

Each rejection changes one input, so it fails at one known step.
"""

import pytest

from ethlib.cryptography import sphincs

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "verify"

# Where each field of a signature starts.
#
#     [ randomizer: 16 | FORS: 4224 | bottom: 1156 | middle: 1156 | top: 1188 ]
#
#     FORS  = 24 openings, each [ secret: 16 | 10 path nodes: 160 ]
#     layer = [ counter: 4 | 64 chain values: 1024 | h siblings: 16 h ]
FORS = 16
FORS_PATH = 16
BOTTOM = FORS + 24 * 176
MIDDLE = BOTTOM + 1156
TOP = MIDDLE + 1156
CHAINS = 4
SIBLINGS = 4 + 64 * 16


def _emit(
    case: str, public_key: bytes, message: bytes, signature: bytes, expected: bool | None
) -> None:
    # Inputs of the wrong length are rejected, written as a null output.
    try:
        result = sphincs.verify(public_key, message, signature)
    except (ValueError, RuntimeError):
        result = None
    assert result == expected
    write_case(
        "sphincs",
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


def _key(case: str = "key_gen_known_answer") -> bytes:
    return F.read_output("key_gen", case)


def _signature(case: str = "sign_known_answer") -> bytes:
    return F.read_output("sign", case)


# ---- Accepted ----------------------------------------------------------------


@pytest.mark.parametrize(
    "case, key, message",
    [
        ("sign_known_answer", "key_gen_known_answer", F.MESSAGE_KNOWN_ANSWER),
        ("sign_zero_message", "key_gen_known_answer", F.MESSAGE_ZERO),
        ("sign_zero_seed", "key_gen_zero_seed", F.MESSAGE_KNOWN_ANSWER),
    ],
)
def test_valid(case: str, key: str, message: bytes) -> None:
    _emit(
        f"{HANDLER}_valid_{case.removeprefix('sign_')}",
        _key(key),
        message,
        _signature(case),
        expected=True,
    )


def test_valid_scheme_seed() -> None:
    # The independent key and signature: every hash of the verifier is fixed by them.
    _emit(
        f"{HANDLER}_valid_scheme_seed",
        F.PUBLIC_KEY_SCHEME_SEED,
        F.MESSAGE_KNOWN_ANSWER,
        F.SIGNATURE_SCHEME_SEED,
        expected=True,
    )


def test_zeroed_scheme_seed_top_last_sibling() -> None:
    # The sibling just below the key's root, the last 16 bytes, becomes all zero.
    signature = F.SIGNATURE_SCHEME_SEED[:-16] + bytes(16)
    _emit(
        f"{HANDLER}_zeroed_scheme_seed_top_last_sibling",
        F.PUBLIC_KEY_SCHEME_SEED,
        F.MESSAGE_KNOWN_ANSWER,
        signature,
        expected=False,
    )


def test_zeroed_scheme_seed_fors_secret() -> None:
    # The secret of FORS tree 0 becomes all zero, so the bottom layer signed another FORS key.
    signature = F.SIGNATURE_SCHEME_SEED
    signature = signature[:FORS] + bytes(16) + signature[FORS + 16 :]
    _emit(
        f"{HANDLER}_zeroed_scheme_seed_fors_secret",
        F.PUBLIC_KEY_SCHEME_SEED,
        F.MESSAGE_KNOWN_ANSWER,
        signature,
        expected=False,
    )


# ---- Rejected: one changed input ------------------------------------------------


def test_wrong_message() -> None:
    # The digest changes, so it names another FORS instance and other leaves.
    _emit(
        f"{HANDLER}_wrong_message",
        _key(),
        F.flip(F.MESSAGE_KNOWN_ANSWER, 0),
        _signature(),
        expected=False,
    )


def test_tampered_randomizer() -> None:
    # The randomizer is hashed into the digest, so the digest changes too.
    _emit(
        f"{HANDLER}_tampered_randomizer",
        _key(),
        F.MESSAGE_KNOWN_ANSWER,
        F.flip(_signature(), 0),
        expected=False,
    )


@pytest.mark.parametrize("field, offset", [("secret", FORS), ("path_node", FORS + FORS_PATH)])
def test_tampered_fors(field: str, offset: int) -> None:
    # One flipped bit in the first opening: tree 0 recovers other nodes, so the FORS key changes.
    _emit(
        f"{HANDLER}_tampered_fors_{field}",
        _key(),
        F.MESSAGE_KNOWN_ANSWER,
        F.flip(_signature(), offset),
        expected=False,
    )


@pytest.mark.parametrize("layer, start", [("bottom", BOTTOM), ("middle", MIDDLE), ("top", TOP)])
@pytest.mark.parametrize(
    "field, offset",
    [
        ("counter", 0),
        ("chain_value", CHAINS),
        ("sibling", SIBLINGS),
    ],
)
def test_tampered(layer: str, start: int, field: str, offset: int) -> None:
    # One flipped bit in the first value of one field of one layer.
    _emit(
        f"{HANDLER}_tampered_{layer}_{field}",
        _key(),
        F.MESSAGE_KNOWN_ANSWER,
        F.flip(_signature(), start + offset),
        expected=False,
    )


def test_tampered_top_last_sibling() -> None:
    # The last byte of the signature: the sibling just below the key's root.
    signature = _signature()
    _emit(
        f"{HANDLER}_tampered_top_last_sibling",
        _key(),
        F.MESSAGE_KNOWN_ANSWER,
        F.flip(signature, len(signature) - 1),
        expected=False,
    )


def test_wrong_root() -> None:
    # The public key is the root, then the public parameter.
    _emit(
        f"{HANDLER}_wrong_root",
        F.flip(_key(), 0),
        F.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_wrong_public_param() -> None:
    _emit(
        f"{HANDLER}_wrong_public_param",
        F.flip(_key(), 16),
        F.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_other_key() -> None:
    # A valid signature, checked under the key of another seed.
    _emit(
        f"{HANDLER}_other_key",
        _key("key_gen_zero_seed"),
        F.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


# ---- Rejected: wrong lengths --------------------------------------------------


def test_short_public_key() -> None:
    _emit(
        f"{HANDLER}_short_public_key",
        _key()[:31],
        F.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=None,
    )


def test_short_message() -> None:
    _emit(
        f"{HANDLER}_short_message", _key(), F.MESSAGE_KNOWN_ANSWER[:31], _signature(), expected=None
    )


def test_short_signature() -> None:
    _emit(
        f"{HANDLER}_short_signature",
        _key(),
        F.MESSAGE_KNOWN_ANSWER,
        _signature()[:-1],
        expected=None,
    )


def test_long_signature() -> None:
    _emit(
        f"{HANDLER}_long_signature",
        _key(),
        F.MESSAGE_KNOWN_ANSWER,
        _signature() + b"\x00",
        expected=None,
    )
