"""The draft operations against `py_ecc.bls.G2ProofOfPossession`.

These tests write no vectors.
"""

from typing import cast

import pytest
from py_ecc.bls import G2ProofOfPossession as RefBls

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
