"""Test-vector generator: `eth_fast_aggregate_verify`."""

import pytest

from ethlib.cryptography import bls

from . import fixtures as F
from dumper import hex_str, hex_list, write_case


HANDLER = "eth_fast_aggregate_verify"


def _emit(case: str, pubkeys: list[bytes], message: bytes, signature: bytes,
          expected: bool) -> None:
    result = bls.eth_fast_aggregate_verify(pubkeys, message, signature)
    assert result == expected
    write_case("bls", HANDLER, case, {
        "input": {
            "pubkeys":   hex_list(pubkeys),
            "message":   hex_str(message),
            "signature": hex_str(signature),
        },
        "output": result,
    })


@pytest.mark.parametrize("i", range(len(F.MESSAGES)))
def test_valid(i: int) -> None:
    msg      = F.MESSAGES[i]
    privkeys = F.PRIVKEYS[: i + 1]
    sig      = F.aggregate([F.sign(sk, msg) for sk in privkeys])
    pubkeys  = [F.sk_to_pk(sk) for sk in privkeys]
    _emit(f"{HANDLER}_valid_{i}", pubkeys, msg, sig, expected=True)


@pytest.mark.parametrize("i", range(len(F.MESSAGES)))
def test_extra_pubkey(i: int) -> None:
    msg      = F.MESSAGES[i]
    privkeys = F.PRIVKEYS[: i + 1]
    sig      = F.aggregate([F.sign(sk, msg) for sk in privkeys])
    pubkeys  = [F.sk_to_pk(sk) for sk in privkeys] + [F.sk_to_pk(F.PRIVKEYS[-1])]
    _emit(f"{HANDLER}_extra_pubkey_{i}", pubkeys, msg, sig, expected=False)


@pytest.mark.parametrize("i", range(len(F.MESSAGES)))
def test_tampered_signature(i: int) -> None:
    msg       = F.MESSAGES[i]
    privkeys  = F.PRIVKEYS[: i + 1]
    sig       = F.aggregate([F.sign(sk, msg) for sk in privkeys])
    tampered  = sig[:-4] + b"\xff\xff\xff\xff"
    pubkeys   = [F.sk_to_pk(sk) for sk in privkeys]
    _emit(f"{HANDLER}_tampered_signature_{i}", pubkeys, msg, tampered, expected=False)


def test_na_pubkeys_and_infinity_signature() -> None:
    _emit(f"{HANDLER}_na_pubkeys_and_infinity_signature",
          [], F.MESSAGES[-1], F.G2_POINT_AT_INFINITY, expected=True)


def test_na_pubkeys_and_zero_signature() -> None:
    _emit(f"{HANDLER}_na_pubkeys_and_zero_signature",
          [], F.MESSAGES[-1], F.ZERO_SIGNATURE, expected=False)


def test_infinity_pubkey() -> None:
    pubkeys = [F.sk_to_pk(sk) for sk in F.PRIVKEYS] + [F.G1_POINT_AT_INFINITY]
    sig     = F.aggregate([F.sign(sk, F.SAMPLE_MESSAGE) for sk in F.PRIVKEYS])
    _emit(f"{HANDLER}_infinity_pubkey",
          pubkeys, F.SAMPLE_MESSAGE, sig, expected=False)
