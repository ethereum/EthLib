"""Test-vector generator: `verify`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import sphincs

from . import fixtures

# The keys and signatures come from the committed `key_gen` and `sign` cases.
# The `zeroed` cases start from leanVM's known answer, the same bytes as the known-answer cases.
# Each rejection changes one input, so it fails at one known step.

HANDLER = "verify"

# Where each field of a signature starts, from the sizes that Lean exports.
#
#     [ randomizer | FORS | bottom layer | middle layer | top layer ]
#
#     FORS  = FORS_TREES openings, each [ secret | FORS_HEIGHT path nodes ]
#     layer = [ counter | CHAINS chain values | h siblings ]
#
# Each secret, path node, chain value and sibling has N bytes.
# The bottom and middle layers have height LOWER_HEIGHT, and the top layer TOP_HEIGHT.
# With the parameters of leanSPHINCS, the layers have 1156, 1156 and 1188 bytes.
OPENING = sphincs.N + sphincs.FORS_HEIGHT * sphincs.N
LOWER = sphincs.COUNTER_LEN + (sphincs.CHAINS + sphincs.LOWER_HEIGHT) * sphincs.N
FORS = sphincs.RANDOMIZER_LEN
FORS_PATH = sphincs.N
BOTTOM = FORS + sphincs.FORS_TREES * OPENING
MIDDLE = BOTTOM + LOWER
TOP = MIDDLE + LOWER
CHAINS = sphincs.COUNTER_LEN
SIBLINGS = sphincs.COUNTER_LEN + sphincs.CHAINS * sphincs.N


def test_layout_fills_signature() -> None:
    """The fields of the layout, with the top layer last, fill the signature exactly."""
    top = sphincs.COUNTER_LEN + (sphincs.CHAINS + sphincs.TOP_HEIGHT) * sphincs.N
    assert TOP + top == sphincs.SIG_SIZE


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
    return fixtures.read_output("key_gen", case)


def _signature(case: str = "sign_known_answer") -> bytes:
    return fixtures.read_output("sign", case)


# ---- Accepted ----------------------------------------------------------------


@pytest.mark.parametrize(
    "case, key, message",
    [
        ("sign_known_answer", "key_gen_known_answer", fixtures.MESSAGE_KNOWN_ANSWER),
        ("sign_zero_message", "key_gen_known_answer", fixtures.MESSAGE_ZERO),
        ("sign_zero_seed", "key_gen_zero_seed", fixtures.MESSAGE_KNOWN_ANSWER),
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


def test_zeroed_top_last_sibling() -> None:
    # The sibling just below the key's root, the last N bytes, becomes all zero.
    signature = fixtures.SIGNATURE_KNOWN_ANSWER[: -sphincs.N] + bytes(sphincs.N)
    _emit(
        f"{HANDLER}_zeroed_top_last_sibling",
        fixtures.PUBLIC_KEY_KNOWN_ANSWER,
        fixtures.MESSAGE_KNOWN_ANSWER,
        signature,
        expected=False,
    )


def test_zeroed_fors_secret() -> None:
    # The secret of FORS tree 0 becomes all zero, so the bottom layer signed another FORS key.
    signature = fixtures.SIGNATURE_KNOWN_ANSWER
    signature = signature[:FORS] + bytes(sphincs.N) + signature[FORS + sphincs.N :]
    _emit(
        f"{HANDLER}_zeroed_fors_secret",
        fixtures.PUBLIC_KEY_KNOWN_ANSWER,
        fixtures.MESSAGE_KNOWN_ANSWER,
        signature,
        expected=False,
    )


# ---- Rejected: one changed input ------------------------------------------------


def test_wrong_message() -> None:
    # The digest changes, so it names another FORS instance and other leaves.
    _emit(
        f"{HANDLER}_wrong_message",
        _key(),
        fixtures.flip(fixtures.MESSAGE_KNOWN_ANSWER, 0),
        _signature(),
        expected=False,
    )


def test_tampered_randomizer() -> None:
    # The randomizer is hashed into the digest, so the digest changes too.
    _emit(
        f"{HANDLER}_tampered_randomizer",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        fixtures.flip(_signature(), 0),
        expected=False,
    )


@pytest.mark.parametrize("field, offset", [("secret", FORS), ("path_node", FORS + FORS_PATH)])
def test_tampered_fors(field: str, offset: int) -> None:
    # One flipped bit in the first opening: tree 0 recovers other nodes, so the FORS key changes.
    _emit(
        f"{HANDLER}_tampered_fors_{field}",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        fixtures.flip(_signature(), offset),
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


def test_wrong_pk_seed() -> None:
    # The public key is PK.seed, then PK.root.
    # PK.seed is hashed into every call, so the digest and every node change.
    _emit(
        f"{HANDLER}_wrong_pk_seed",
        fixtures.flip(_key(), 0),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_wrong_root() -> None:
    # PK.root is hashed into the digest, and it is the root the top layer must reach.
    _emit(
        f"{HANDLER}_wrong_root",
        fixtures.flip(_key(), sphincs.N),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_other_key() -> None:
    # A valid signature, checked under the key of another seed.
    _emit(
        f"{HANDLER}_other_key",
        _key("key_gen_zero_seed"),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


# ---- Rejected: wrong lengths --------------------------------------------------


def test_short_public_key() -> None:
    _emit(
        f"{HANDLER}_short_public_key",
        _key()[:-1],
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=None,
    )


def test_short_message() -> None:
    _emit(
        f"{HANDLER}_short_message",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER[:-1],
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
