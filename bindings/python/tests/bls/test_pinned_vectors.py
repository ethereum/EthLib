"""EthLib against the pinned BLS and hash-to-curve vectors.

The `sign`, `verify`, `aggregate`, `fast_aggregate_verify` and `aggregate_verify` cases come from
`ethereum/bls12-381-tests` v0.1.2.
The `hash_to_curve` cases come from RFC 9380, Appendices J.10.1, K.1 and K.2.

These tests read the cases and write nothing, so the digests keep their upstream provenance.
"""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.cryptography import bls

ROOT = Path(__file__).resolve().parents[4] / "tests" / "cryptography"
LOADER = YAML(typ="safe", pure=True)


def cases(kind: str, handler: str) -> list:
    paths = sorted((ROOT / kind / handler).glob("*/data.yaml"))
    assert paths, f"no cases for {kind}/{handler}"
    return [pytest.param(LOADER.load(p.read_text()), id=p.parent.name) for p in paths]


def b(hex_str: str) -> bytes:
    return bytes.fromhex(hex_str.removeprefix("0x"))


@pytest.mark.parametrize("case", cases("bls", "sign"))
def test_sign(case: dict) -> None:
    sk, msg = b(case["input"]["privkey"]), b(case["input"]["message"])
    if case["output"] is None:
        with pytest.raises(ValueError):
            bls.sign(sk, msg)
    else:
        assert bls.sign(sk, msg) == b(case["output"])


@pytest.mark.parametrize("case", cases("bls", "verify"))
def test_verify(case: dict) -> None:
    i = case["input"]
    assert bls.verify(b(i["pubkey"]), b(i["message"]), b(i["signature"])) == case["output"]


@pytest.mark.parametrize("case", cases("bls", "aggregate"))
def test_aggregate(case: dict) -> None:
    sigs = [b(s) for s in case["input"]]
    if case["output"] is None:
        with pytest.raises(ValueError):
            bls.aggregate(sigs)
    else:
        assert bls.aggregate(sigs) == b(case["output"])


@pytest.mark.parametrize("case", cases("bls", "fast_aggregate_verify"))
def test_fast_aggregate_verify(case: dict) -> None:
    i = case["input"]
    pks = [b(pk) for pk in i["pubkeys"]]
    assert bls.fast_aggregate_verify(pks, b(i["message"]), b(i["signature"])) == case["output"]


@pytest.mark.parametrize("case", cases("bls", "aggregate_verify"))
def test_aggregate_verify(case: dict) -> None:
    i = case["input"]
    pks = [b(pk) for pk in i["pubkeys"]]
    msgs = [b(m) for m in i["messages"]]
    assert bls.aggregate_verify(pks, msgs, b(i["signature"])) == case["output"]


@pytest.mark.parametrize("case", cases("hash_to_curve", "expand_message_xmd"))
def test_expand_message_xmd(case: dict) -> None:
    i = case["input"]
    out = bls.expand_message_xmd(b(i["msg"]), b(i["dst"]), i["len_in_bytes"])
    assert out == b(case["output"])


@pytest.mark.parametrize("case", cases("hash_to_curve", "hash_to_g2"))
def test_hash_to_g2(case: dict) -> None:
    i, o = case["input"], case["output"]
    expected = b"".join(b(c) for c in o["x"] + o["y"])
    assert bls.hash_to_g2(b(i["msg"]), b(i["dst"])) == expected
