"""The draft operations against `py_ecc.bls.G2ProofOfPossession`.

These tests write no vectors.
"""

import pytest

from ethlib.cryptography import bls

from . import fixtures as F
from py_ecc.bls import G2ProofOfPossession as ref_bls


def sk_bytes(sk: int) -> bytes:
    return sk.to_bytes(32, "big")


R = 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001


@pytest.mark.parametrize("sk", F.PRIVKEYS)
@pytest.mark.parametrize("msg", F.MESSAGES + [b"", b"abc" * 50])
def test_sign_matches_reference(sk: int, msg: bytes) -> None:
    sig = bls.sign(sk_bytes(sk), msg)
    assert sig == ref_bls.Sign(sk, msg)
    assert bls.verify(F.sk_to_pk(sk), msg, sig)


@pytest.mark.parametrize("sk", [0, R, R + 1])
def test_sign_rejects_out_of_range_key(sk: int) -> None:
    with pytest.raises(ValueError, match="invalid secret key"):
        bls.sign(sk_bytes(sk), F.SAMPLE_MESSAGE)


def test_sign_rejects_short_key() -> None:
    with pytest.raises(ValueError, match="invalid secret key"):
        bls.sign(b"\x01" * 31, F.SAMPLE_MESSAGE)


def test_verify_rejects() -> None:
    sk = F.PRIVKEYS[0]
    pk = F.sk_to_pk(sk)
    sig = ref_bls.Sign(sk, F.SAMPLE_MESSAGE)
    assert not bls.verify(pk, F.MESSAGES[0], sig)
    assert not bls.verify(F.sk_to_pk(F.PRIVKEYS[1]), F.SAMPLE_MESSAGE, sig)
    assert not bls.verify(pk[:-1], F.SAMPLE_MESSAGE, sig)
    assert not bls.verify(pk, F.SAMPLE_MESSAGE, sig[:-1])
    assert not bls.verify(F.G1_POINT_AT_INFINITY, F.SAMPLE_MESSAGE, F.G2_POINT_AT_INFINITY)


def test_aggregate_matches_reference() -> None:
    sigs = [ref_bls.Sign(sk, msg) for sk, msg in zip(F.PRIVKEYS, F.MESSAGES)]
    for n in range(1, len(sigs) + 1):
        assert bls.aggregate(sigs[:n]) == ref_bls.Aggregate(sigs[:n])
    assert bls.aggregate([F.G2_POINT_AT_INFINITY]) == F.G2_POINT_AT_INFINITY


def test_aggregate_rejects() -> None:
    with pytest.raises(ValueError, match="empty signature list"):
        bls.aggregate([])
    with pytest.raises(ValueError, match="invalid G2 point"):
        bls.aggregate([F.ZERO_SIGNATURE])


def test_aggregate_verify() -> None:
    pks = [F.sk_to_pk(sk) for sk in F.PRIVKEYS]
    sig = ref_bls.Aggregate([ref_bls.Sign(sk, m) for sk, m in zip(F.PRIVKEYS, F.MESSAGES)])
    assert bls.aggregate_verify(pks, F.MESSAGES, sig)
    assert not bls.aggregate_verify(pks, F.MESSAGES[::-1], sig)
    assert not bls.aggregate_verify(pks[:-1], F.MESSAGES, sig)
    assert not bls.aggregate_verify([], [], F.G2_POINT_AT_INFINITY)


def test_fast_aggregate_verify() -> None:
    pks = [F.sk_to_pk(sk) for sk in F.PRIVKEYS]
    sig = ref_bls.Aggregate([ref_bls.Sign(sk, F.SAMPLE_MESSAGE) for sk in F.PRIVKEYS])
    assert bls.fast_aggregate_verify(pks, F.SAMPLE_MESSAGE, sig)
    assert not bls.fast_aggregate_verify(pks[:-1], F.SAMPLE_MESSAGE, sig)
    # Unlike the Ethereum wrapper, the draft rejects an empty key list.
    assert not bls.fast_aggregate_verify([], F.SAMPLE_MESSAGE, F.G2_POINT_AT_INFINITY)


@pytest.mark.parametrize("sk", F.PRIVKEYS)
def test_proof_of_possession(sk: int) -> None:
    proof = bls.pop_prove(sk_bytes(sk))
    assert proof == ref_bls.PopProve(sk)
    assert bls.pop_verify(F.sk_to_pk(sk), proof)
    # A signature on the public key under the signing DST is not a proof.
    assert not bls.pop_verify(F.sk_to_pk(sk), ref_bls.Sign(sk, F.sk_to_pk(sk)))
    assert not bls.pop_verify(F.sk_to_pk(sk + 1), proof)


@pytest.mark.parametrize("length", [-1, 2**64, 2**64 + 32])
def test_expand_message_xmd_length_out_of_range(length: int) -> None:
    # A length that does not fit in 64 bits is an error, not a length modulo 2^64.
    with pytest.raises(OverflowError):
        bls.expand_message_xmd(b"msg", b"dst", length)
