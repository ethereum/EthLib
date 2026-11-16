"""Test-vector generator: `verify`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import xmss

from . import derivation, fixtures

# The keys and signatures come from the committed `key_gen` and `sign` cases.
# Each rejection changes one input, so it fails at one known step.
# The zero cases change more than one input, and each says which.

HANDLER = "verify"

# Where each field of a signature starts, from the sizes that Lean exports.
#
#     [ leaf index | bottom layer | top layer ]
#
#     layer = [ randomizer | CHAINS chain values | LAYER_HEIGHT siblings ]
#
# Each chain value and each sibling is a digest.
# With the parameters of leanXMSS, the leaf index has 4 bytes and a layer 1200.
LAYER = xmss.RANDOMIZER_LEN + (xmss.CHAINS + xmss.LAYER_HEIGHT) * xmss.DIGEST_LEN
BOTTOM = xmss.LEAF_INDEX_SIZE
TOP = BOTTOM + LAYER
CHAINS = xmss.RANDOMIZER_LEN
SIBLINGS = xmss.RANDOMIZER_LEN + xmss.CHAINS * xmss.DIGEST_LEN


def test_layout_fills_signature() -> None:
    """The leaf index and the two layers fill the signature exactly."""
    assert TOP + LAYER == xmss.SIG_SIZE


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
    # The leaf index is the first bytes of the signature, least significant first.
    index = (fixtures.LEAF_KNOWN_ANSWER + 1).to_bytes(xmss.LEAF_INDEX_SIZE, "little")
    signature = index + _signature()[xmss.LEAF_INDEX_SIZE :]
    _emit(
        f"{HANDLER}_next_leaf_index",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        signature,
        expected=False,
    )


def test_zeroed_top_last_sibling() -> None:
    # The sibling just below the key's root, the last digest, becomes all zero.
    signature = _signature()[: -xmss.DIGEST_LEN] + bytes(xmss.DIGEST_LEN)
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


def test_wrong_root_last_byte() -> None:
    # The last byte of the root, which a comparison of its first bytes does not read.
    _emit(
        f"{HANDLER}_wrong_root_last_byte",
        fixtures.flip(_key(), xmss.DIGEST_LEN - 1),
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_wrong_root_high_bit() -> None:
    # The high bit of the first byte of the root.
    key = _key()
    _emit(
        f"{HANDLER}_wrong_root_high_bit",
        bytes([key[0] ^ 0x80]) + key[1:],
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        expected=False,
    )


def test_wrong_public_param() -> None:
    _emit(
        f"{HANDLER}_wrong_public_param",
        fixtures.flip(_key(), xmss.DIGEST_LEN),
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


# ---- Rejected: a digest that is not a codeword --------------------------------

# A codeword has zero digits after those of its chains, and its chain digits sum to TARGET_SUM.
# Each near miss signs one layer again, under a randomizer whose digest is not a codeword.
# Its chain values are the key's own at that digest, so the leaf, the path and the root still match.
# So the codeword check of that layer is the only check that rejects the signature.
#
# A randomizer is a counter, written as RANDOMIZER_LEN little-endian bytes.
# Each counter is the least one from 0 whose digest has the digits that the case names.
# The test checks the digest that it gives.
#
# In a case named `all_sum`, the digits of the whole digest sum to TARGET_SUM.
# A verifier that sums every digit rejects such a digest only through its zero digits.
#
# Each row is a name, the first and the last digit after the chains, and the sum of chain digits.
# The counter of the bottom layer and the counter of the top layer end the row.
NEAR_MISSES = [
    ("digit_sum_105", 0, 0, xmss.TARGET_SUM - 1, 238156, 45339),
    ("digit_sum_107", 0, 0, xmss.TARGET_SUM + 1, 4909009, 2384780),
    ("digit_58_nonzero", 1, 0, xmss.TARGET_SUM, 1425269, 502872),
    ("digit_58_all_sum_106", 1, 0, xmss.TARGET_SUM - 1, 1789135, 712522),
    ("last_digit_nonzero", 0, 2, xmss.TARGET_SUM, 1794943, 328771),
    ("last_digit_all_sum_106", 0, 2, xmss.TARGET_SUM - 2, 1349650, 97764),
]


@pytest.mark.parametrize(
    "layer_name, layer", [("bottom", derivation.BOTTOM_LAYER), ("top", derivation.TOP_LAYER)]
)
@pytest.mark.parametrize("name, first, last, chain_sum, bottom_counter, top_counter", NEAR_MISSES)
def test_near_miss(
    layer_name: str,
    layer: int,
    name: str,
    first: int,
    last: int,
    chain_sum: int,
    bottom_counter: int,
    top_counter: int,
) -> None:
    counter = top_counter if layer == derivation.TOP_LAYER else bottom_counter
    near_miss = derivation.near_miss(
        fixtures.SEED_KNOWN_ANSWER,
        fixtures.MESSAGE_KNOWN_ANSWER,
        _signature(),
        layer,
        counter.to_bytes(xmss.RANDOMIZER_LEN, "little"),
    )
    # The digest has the digits that the case names.
    digits = derivation.digits(near_miss.digest)
    after_chains = digits[xmss.CHAINS :]
    assert (after_chains[0], after_chains[-1]) == (first, last)
    assert not any(after_chains[1:-1])
    assert sum(digits[: xmss.CHAINS]) == chain_sum
    # The chain values lead to the leaf of the valid signature, so every later check passes.
    assert near_miss.leaf == near_miss.valid_leaf
    _emit(
        f"{HANDLER}_{layer_name}_{name}",
        _key(),
        fixtures.MESSAGE_KNOWN_ANSWER,
        near_miss.signature,
        expected=False,
    )


# ---- Rejected: zero inputs and a zero root -------------------------------------


def test_zero_inputs() -> None:
    # Every byte of the public key, the message and the signature is zero.
    _emit(
        f"{HANDLER}_zero_inputs",
        bytes(xmss.PUB_KEY_SIZE),
        bytes(xmss.MESSAGE_LEN),
        bytes(xmss.SIG_SIZE),
        expected=False,
    )


@pytest.mark.parametrize("layer, start", [("bottom", BOTTOM), ("top", TOP)])
def test_zero_root_not_codeword(layer: str, start: int) -> None:
    # The root of the public key is zero, and a flipped bit in one randomizer changes its digest.
    # A verifier that holds zero for a root it never computed would compare zero with zero.
    key = _key()
    signature = fixtures.flip(_signature(), start)
    # The digest of that layer is not a codeword.
    bottom_digest, top_digest = derivation.layer_digests(
        key[xmss.DIGEST_LEN :], fixtures.MESSAGE_KNOWN_ANSWER, signature
    )
    assert not derivation.is_codeword(top_digest if layer == "top" else bottom_digest)
    _emit(
        f"{HANDLER}_zero_root_{layer}_not_codeword",
        bytes(xmss.DIGEST_LEN) + key[xmss.DIGEST_LEN :],
        fixtures.MESSAGE_KNOWN_ANSWER,
        signature,
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
