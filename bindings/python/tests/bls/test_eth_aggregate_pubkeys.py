"""Test-vector generator: `eth_aggregate_pubkeys`."""

import pytest

from ethlib.cryptography import bls

from . import fixtures as F
from dumper import hex_str, hex_list, write_case


HANDLER = "eth_aggregate_pubkeys"


def _emit_valid(case: str, pubkeys: list[bytes]) -> None:
    out = bls.eth_aggregate_pubkeys(pubkeys)
    write_case("bls", HANDLER, case, {
        "input":  hex_list(pubkeys),
        "output": hex_str(out),
    })


def _emit_invalid(case: str, pubkeys: list[bytes]) -> None:
    with pytest.raises(Exception):
        bls.eth_aggregate_pubkeys(pubkeys)
    write_case("bls", HANDLER, case, {
        "input":  hex_list(pubkeys),
        "output": None,
    })


@pytest.mark.parametrize("i", range(len(F.PRIVKEYS)))
def test_valid_single(i: int) -> None:
    pk = F.sk_to_pk(F.PRIVKEYS[i])
    _emit_valid(f"{HANDLER}_valid_{i}", [pk])


def test_valid_pubkeys() -> None:
    pubkeys = [F.sk_to_pk(sk) for sk in F.PRIVKEYS]
    _emit_valid(f"{HANDLER}_valid_pubkeys", pubkeys)


def test_empty_list() -> None:
    _emit_invalid(f"{HANDLER}_empty_list", [])


def test_zero_pubkey() -> None:
    _emit_invalid(f"{HANDLER}_zero_pubkey", [F.ZERO_PUBKEY])


def test_infinity_pubkey() -> None:
    _emit_invalid(f"{HANDLER}_infinity_pubkey", [F.G1_POINT_AT_INFINITY])


def test_x40_pubkey() -> None:
    _emit_invalid(f"{HANDLER}_x40_pubkey", [b"\x40" + b"\x00" * 47])
