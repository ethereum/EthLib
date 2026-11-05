"""Test-vector generator: `eth_fast_aggregate_verify`."""

import pytest

from dumper import hex_list, hex_str, write_case
from ethlib.cryptography import bls

from . import fixtures

HANDLER = "eth_fast_aggregate_verify"


def _emit(
    case: str, pubkeys: list[bytes], message: bytes, signature: bytes, expected: bool
) -> None:
    result = bls.eth_fast_aggregate_verify(pubkeys, message, signature)
    assert result == expected
    write_case(
        "bls",
        HANDLER,
        case,
        {
            "input": {
                "pubkeys": hex_list(pubkeys),
                "message": hex_str(message),
                "signature": hex_str(signature),
            },
            "output": result,
        },
    )


@pytest.mark.parametrize("i", range(len(fixtures.MESSAGES)))
def test_valid(i: int) -> None:
    msg = fixtures.MESSAGES[i]
    privkeys = fixtures.PRIVKEYS[: i + 1]
    sig = fixtures.aggregate([fixtures.sign(sk, msg) for sk in privkeys])
    pubkeys = [fixtures.sk_to_pk(sk) for sk in privkeys]
    _emit(f"{HANDLER}_valid_{i}", pubkeys, msg, sig, expected=True)


@pytest.mark.parametrize("i", range(len(fixtures.MESSAGES)))
def test_extra_pubkey(i: int) -> None:
    msg = fixtures.MESSAGES[i]
    privkeys = fixtures.PRIVKEYS[: i + 1]
    sig = fixtures.aggregate([fixtures.sign(sk, msg) for sk in privkeys])
    pubkeys = [fixtures.sk_to_pk(sk) for sk in privkeys] + [
        fixtures.sk_to_pk(fixtures.PRIVKEYS[-1])
    ]
    _emit(f"{HANDLER}_extra_pubkey_{i}", pubkeys, msg, sig, expected=False)


@pytest.mark.parametrize("i", range(len(fixtures.MESSAGES)))
def test_tampered_signature(i: int) -> None:
    msg = fixtures.MESSAGES[i]
    privkeys = fixtures.PRIVKEYS[: i + 1]
    sig = fixtures.aggregate([fixtures.sign(sk, msg) for sk in privkeys])
    tampered = sig[:-4] + b"\xff\xff\xff\xff"
    pubkeys = [fixtures.sk_to_pk(sk) for sk in privkeys]
    _emit(f"{HANDLER}_tampered_signature_{i}", pubkeys, msg, tampered, expected=False)


def test_na_pubkeys_and_infinity_signature() -> None:
    _emit(
        f"{HANDLER}_na_pubkeys_and_infinity_signature",
        [],
        fixtures.MESSAGES[-1],
        fixtures.G2_POINT_AT_INFINITY,
        expected=True,
    )


def test_na_pubkeys_and_zero_signature() -> None:
    _emit(
        f"{HANDLER}_na_pubkeys_and_zero_signature",
        [],
        fixtures.MESSAGES[-1],
        fixtures.ZERO_SIGNATURE,
        expected=False,
    )


def test_infinity_pubkey() -> None:
    pubkeys = [fixtures.sk_to_pk(sk) for sk in fixtures.PRIVKEYS] + [fixtures.G1_POINT_AT_INFINITY]
    sig = fixtures.aggregate(
        [fixtures.sign(sk, fixtures.SAMPLE_MESSAGE) for sk in fixtures.PRIVKEYS]
    )
    _emit(f"{HANDLER}_infinity_pubkey", pubkeys, fixtures.SAMPLE_MESSAGE, sig, expected=False)
