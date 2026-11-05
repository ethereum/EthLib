"""Test-vector generator: `eth_aggregate_pubkeys`."""

import pytest

from dumper import hex_list, hex_str, write_case
from ethlib.cryptography import bls
from raising import raises

from . import fixtures

HANDLER = "eth_aggregate_pubkeys"


def _emit_valid(case: str, pubkeys: list[bytes]) -> None:
    out = bls.eth_aggregate_pubkeys(pubkeys)
    write_case(
        "bls",
        HANDLER,
        case,
        {
            "input": hex_list(pubkeys),
            "output": hex_str(out),
        },
    )


def _emit_invalid(case: str, pubkeys: list[bytes], message: str) -> None:
    with raises(bls.BlsError, message):
        bls.eth_aggregate_pubkeys(pubkeys)
    write_case(
        "bls",
        HANDLER,
        case,
        {
            "input": hex_list(pubkeys),
            "output": None,
        },
    )


@pytest.mark.parametrize("i", range(len(fixtures.PRIVKEYS)))
def test_valid_single(i: int) -> None:
    pk = fixtures.sk_to_pk(fixtures.PRIVKEYS[i])
    _emit_valid(f"{HANDLER}_valid_{i}", [pk])


def test_valid_pubkeys() -> None:
    pubkeys = [fixtures.sk_to_pk(sk) for sk in fixtures.PRIVKEYS]
    _emit_valid(f"{HANDLER}_valid_pubkeys", pubkeys)


def test_empty_list() -> None:
    _emit_invalid(f"{HANDLER}_empty_list", [], "empty pubkey list")


def test_zero_pubkey() -> None:
    _emit_invalid(f"{HANDLER}_zero_pubkey", [fixtures.ZERO_PUBKEY], "invalid pubkey at index 0")


def test_infinity_pubkey() -> None:
    _emit_invalid(
        f"{HANDLER}_infinity_pubkey", [fixtures.G1_POINT_AT_INFINITY], "invalid pubkey at index 0"
    )


def test_x40_pubkey() -> None:
    _emit_invalid(f"{HANDLER}_x40_pubkey", [b"\x40" + b"\x00" * 47], "invalid pubkey at index 0")
