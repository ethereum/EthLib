"""The draft operations against `py_ecc.bls.G2ProofOfPossession`, writing no vectors."""

from typing import cast

import pytest
from eth_typing import BLSPubkey
from py_ecc.bls import G2ProofOfPossession as RefBls
from py_ecc.bls.g2_primitives import G1_to_pubkey, pubkey_to_G1
from py_ecc.optimized_bls12_381 import G1, add, multiply, neg

from ethlib.cryptography import bls
from raising import raises

from . import fixtures


def sk_bytes(sk: int) -> bytes:
    return sk.to_bytes(32, "big")


R = 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001


@pytest.mark.parametrize("sk", fixtures.PRIVKEYS)
@pytest.mark.parametrize("msg", fixtures.MESSAGES + [b"", b"abc" * 50])
def test_sign_matches_reference(sk: int, msg: bytes) -> None:
    sig = bls.sign(sk_bytes(sk), msg)
    assert sig == RefBls.Sign(sk, msg)
    assert bls.verify(fixtures.sk_to_pk(sk), msg, sig)


@pytest.mark.parametrize("sk", [0, R, R + 1])
def test_sign_rejects_out_of_range_key(sk: int) -> None:
    with raises(ValueError, "invalid secret key"):
        bls.sign(sk_bytes(sk), fixtures.SAMPLE_MESSAGE)


def test_sign_rejects_short_key() -> None:
    with raises(ValueError, "invalid secret key"):
        bls.sign(b"\x01" * 31, fixtures.SAMPLE_MESSAGE)


def test_verify_rejects() -> None:
    sk = fixtures.PRIVKEYS[0]
    pk = fixtures.sk_to_pk(sk)
    sig = RefBls.Sign(sk, fixtures.SAMPLE_MESSAGE)
    assert not bls.verify(pk, fixtures.MESSAGES[0], sig)
    assert not bls.verify(fixtures.sk_to_pk(fixtures.PRIVKEYS[1]), fixtures.SAMPLE_MESSAGE, sig)
    assert not bls.verify(pk[:-1], fixtures.SAMPLE_MESSAGE, sig)
    assert not bls.verify(pk, fixtures.SAMPLE_MESSAGE, sig[:-1])
    assert not bls.verify(
        fixtures.G1_POINT_AT_INFINITY, fixtures.SAMPLE_MESSAGE, fixtures.G2_POINT_AT_INFINITY
    )


def test_aggregate_matches_reference() -> None:
    sigs = [
        RefBls.Sign(sk, msg) for sk, msg in zip(fixtures.PRIVKEYS, fixtures.MESSAGES, strict=True)
    ]
    for n in range(1, len(sigs) + 1):
        # The reference types its signatures as BLSSignature, and a list is invariant.
        assert bls.aggregate(cast(list[bytes], sigs[:n])) == RefBls.Aggregate(sigs[:n])
    assert bls.aggregate([fixtures.G2_POINT_AT_INFINITY]) == fixtures.G2_POINT_AT_INFINITY


def test_aggregate_rejects() -> None:
    with raises(ValueError, "empty signature list"):
        bls.aggregate([])
    with raises(ValueError, "invalid G2 point"):
        bls.aggregate([fixtures.ZERO_SIGNATURE])


def test_aggregate_verify() -> None:
    pks = [fixtures.sk_to_pk(sk) for sk in fixtures.PRIVKEYS]
    sig = RefBls.Aggregate(
        [RefBls.Sign(sk, m) for sk, m in zip(fixtures.PRIVKEYS, fixtures.MESSAGES, strict=True)]
    )
    assert bls.aggregate_verify(pks, fixtures.MESSAGES, sig)
    assert not bls.aggregate_verify(pks, fixtures.MESSAGES[::-1], sig)
    assert not bls.aggregate_verify(pks[:-1], fixtures.MESSAGES, sig)
    assert not bls.aggregate_verify([], [], fixtures.G2_POINT_AT_INFINITY)


def test_fast_aggregate_verify() -> None:
    pks = [fixtures.sk_to_pk(sk) for sk in fixtures.PRIVKEYS]
    sig = RefBls.Aggregate([RefBls.Sign(sk, fixtures.SAMPLE_MESSAGE) for sk in fixtures.PRIVKEYS])
    assert bls.fast_aggregate_verify(pks, fixtures.SAMPLE_MESSAGE, sig)
    assert not bls.fast_aggregate_verify(pks[:-1], fixtures.SAMPLE_MESSAGE, sig)
    # Unlike the Ethereum wrapper, the draft rejects an empty key list.
    assert not bls.fast_aggregate_verify([], fixtures.SAMPLE_MESSAGE, fixtures.G2_POINT_AT_INFINITY)


@pytest.mark.parametrize("sk", fixtures.PRIVKEYS)
def test_proof_of_possession(sk: int) -> None:
    proof = bls.pop_prove(sk_bytes(sk))
    assert proof == RefBls.PopProve(sk)
    assert bls.pop_verify(fixtures.sk_to_pk(sk), proof)
    # A signature on the public key under the signing DST is not a proof.
    assert not bls.pop_verify(fixtures.sk_to_pk(sk), RefBls.Sign(sk, fixtures.sk_to_pk(sk)))
    assert not bls.pop_verify(fixtures.sk_to_pk(sk + 1), proof)


@pytest.mark.parametrize(
    "length, message",
    [
        (-1, "can't convert negative int to unsigned"),
        (2**64, "int too big to convert"),
        (2**64 + 32, "int too big to convert"),
    ],
)
def test_expand_message_xmd_length_out_of_range(length: int, message: str) -> None:
    # A length that does not fit in 64 bits is an error, not a length modulo 2^64.
    with raises(OverflowError, message):
        bls.expand_message_xmd(b"msg", b"dst", length)


# Keys at the ends of the range [1, r - 1], beside the keys of the fixtures.
KEYS = [1, 2, R - 1, *fixtures.PRIVKEYS]


@pytest.mark.parametrize("sk", KEYS)
def test_sk_to_pk_matches_reference(sk: int) -> None:
    assert bls.sk_to_pk(sk_bytes(sk)) == RefBls.SkToPk(sk)


@pytest.mark.parametrize("key", [sk_bytes(0), sk_bytes(R), sk_bytes(R + 1), b"\x01" * 31])
def test_sk_to_pk_rejects(key: bytes) -> None:
    with raises(bls.BlsError, "invalid secret key"):
        bls.sk_to_pk(key)


# Valid keys, their negations, the point at infinity, and inputs of the wrong form.
VALIDATE_CASES = [
    *(RefBls.SkToPk(sk) for sk in KEYS),
    *(G1_to_pubkey(neg(pubkey_to_G1(RefBls.SkToPk(sk)))) for sk in fixtures.PRIVKEYS),
    fixtures.G1_POINT_AT_INFINITY,
    fixtures.ZERO_PUBKEY,
    b"\x00" * 47,
    b"\x00" * 49,
]


@pytest.mark.parametrize("pubkey", VALIDATE_CASES, ids=lambda pk: pk.hex()[:16])
def test_key_validate_matches_reference(pubkey: bytes) -> None:
    assert bls.key_validate(pubkey) == RefBls.KeyValidate(BLSPubkey(pubkey))


def g1_bytes(k: int) -> bytes:
    """The compressed encoding of `k G`, by the reference."""
    return cast(bytes, G1_to_pubkey(multiply(G1, k)))


# Small, large and equal multiples, so that the addition meets doubling and cancellation.
MULTIPLES = [(1, 1), (1, 2), (3, 5), (7, R - 7), (2**200 + 3, 2**128 - 1), (R - 1, R - 2)]


@pytest.mark.parametrize(("a", "c"), MULTIPLES)
def test_g1_add_matches_reference(a: int, c: int) -> None:
    expected = G1_to_pubkey(add(multiply(G1, a), multiply(G1, c)))
    assert bls.g1_add(g1_bytes(a), g1_bytes(c)) == expected


@pytest.mark.parametrize("k", [1, 2, 5, R - 1, 2**255 % R])
def test_g1_neg_matches_reference(k: int) -> None:
    assert bls.g1_neg(g1_bytes(k)) == G1_to_pubkey(neg(multiply(G1, k)))


@pytest.mark.parametrize("point", [b"\x00" * 47, b"\x00" * 49, fixtures.ZERO_PUBKEY])
def test_g1_operations_reject_invalid_points(point: bytes) -> None:
    for call in (
        lambda: bls.bytes48_to_g1(point),
        lambda: bls.g1_neg(point),
        lambda: bls.g1_add(point, g1_bytes(1)),
        lambda: bls.g1_add(g1_bytes(1), point),
    ):
        with raises(bls.BlsError, "invalid G1 point") as error:
            call()
        assert error.value.code == 4
