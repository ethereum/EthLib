"""Checks of the leanXMSS derivations against the committed known answers."""

from ethlib.cryptography import xmss

from . import derivation, fixtures

# An independent implementation computed `key_gen_known_answer` and `sign_known_answer`.
# The derivations must reproduce them before a `verify` case is built on them.


def _key() -> bytes:
    return fixtures.read_output("key_gen", "key_gen_known_answer")


def _signature() -> bytes:
    return fixtures.read_output("sign", "sign_known_answer")


def _seeds() -> tuple[bytes, bytes]:
    # The scheme seed, and the public parameter derived from it.
    s = derivation.scheme_seed(fixtures.SEED_KNOWN_ANSWER)
    return s, derivation.public_param(s)


def test_public_param() -> None:
    # The public key is the root, then the public parameter.
    _, pp = _seeds()
    assert pp == _key()[xmss.DIGEST_LEN :]


def test_signature_layout() -> None:
    # The leaf index, then the two layers, fill the signature.
    signature = _signature()
    leaf_index, bottom, top = derivation.decode_signature(signature)
    assert leaf_index == fixtures.LEAF_KNOWN_ANSWER
    assert signature[xmss.LEAF_INDEX_SIZE :] == bottom.encode() + top.encode()


def test_digests_are_codewords() -> None:
    # An honest signature signs a codeword on each layer.
    _, pp = _seeds()
    bottom, top = derivation.layer_digests(pp, fixtures.MESSAGE_KNOWN_ANSWER, _signature())
    assert derivation.is_codeword(bottom)
    assert derivation.is_codeword(top)


def test_bottom_chain_values() -> None:
    # The chains of the bottom key, at the digits of its digest, are those of the signature.
    s, pp = _seeds()
    leaf_index, bottom, _ = derivation.decode_signature(_signature())
    digest, _ = derivation.layer_digests(pp, fixtures.MESSAGE_KNOWN_ANSWER, _signature())
    values = derivation.reveal(pp, s, derivation.BOTTOM_LAYER, leaf_index, digest)
    assert values == bottom.chain_values


def test_top_chain_values() -> None:
    # The top key is the one of the bottom tree, and it signs that tree's root.
    s, pp = _seeds()
    leaf_index, _, top = derivation.decode_signature(_signature())
    _, digest = derivation.layer_digests(pp, fixtures.MESSAGE_KNOWN_ANSWER, _signature())
    e = leaf_index >> xmss.LAYER_HEIGHT
    assert derivation.reveal(pp, s, derivation.TOP_LAYER, e, digest) == top.chain_values


def test_root() -> None:
    # The bottom layer leads to the root of its tree, and the top layer to the root of the key.
    _, pp = _seeds()
    leaf_index, bottom, top = derivation.decode_signature(_signature())
    message = fixtures.MESSAGE_KNOWN_ANSWER
    bottom_root = derivation.layer_root(pp, derivation.BOTTOM_LAYER, leaf_index, message, bottom)
    e = leaf_index >> xmss.LAYER_HEIGHT
    root = derivation.layer_root(pp, derivation.TOP_LAYER, e, bottom_root, top)
    assert root == _key()[: xmss.DIGEST_LEN]
