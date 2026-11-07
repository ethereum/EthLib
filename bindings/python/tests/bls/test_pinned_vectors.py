"""EthLib against the pinned BLS and hash-to-curve vectors."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.cryptography import bls
from raising import raises

# The BLS cases come from `ethereum/bls12-381-tests` v0.1.2.
# They are `sign`, `verify`, `aggregate`, `fast_aggregate_verify` and `aggregate_verify`.
# They also cover `deserialization_G1`, `deserialization_G2` and `hash_to_G2`.
# The `hash_to_curve` cases come from RFC 9380, Appendices J.10.1, K.1 and K.2.
#
# These tests write nothing, so the digests keep their upstream provenance.

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
        with raises(ValueError, "invalid secret key"):
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
        with raises(ValueError, "empty signature list"):
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


# The error of each failing deserialization case.
# The point is malformed, off the curve, or on the curve but outside the subgroup of order r.
#
# The G1 case with the infinity flag cleared reads as x = 0.
# Since 0^3 + 4 = 2^2, it decodes to an affine point on the curve, outside the subgroup.
# In G2, x = 0 gives y^2 = 4(1 + i), which has no square root, so that case is off the curve.
DESERIALIZATION_ERRORS = {
    ("G1", "deserialization_fails_not_in_G1"): ("point not in subgroup", 7),
    ("G1", "deserialization_fails_infinity_with_false_b_flag"): ("point not in subgroup", 7),
    ("G2", "deserialization_fails_not_in_G2"): ("point not in subgroup", 7),
}


DECODE = {"G1": (bls.decode_g1, "pubkey"), "G2": (bls.decode_g2, "signature")}


@pytest.mark.parametrize(
    "group, name, case",
    [
        pytest.param(group, param.id, param.values[0], id=f"{group}-{param.id}")
        for group in DECODE
        for param in cases("bls", f"deserialization_{group}")
    ],
)
def test_deserialization(group: str, name: str, case: dict) -> None:
    decode, field = DECODE[group]
    data = b(case["input"][field])
    if case["output"]:
        # A valid encoding decodes, and its canonical encoding is the input itself.
        assert decode(data) == data
        return
    message, code = DESERIALIZATION_ERRORS.get(
        (group, name), (f"invalid {group} point", 4 if group == "G1" else 5)
    )
    with raises(bls.BlsError, message) as error:
        decode(data)
    assert error.value.code == code


@pytest.mark.parametrize("case", cases("bls", "hash_to_G2"))
def test_hash_to_g2_bls_tests(case: dict) -> None:
    # The messages are ASCII text, hashed under the test DST of RFC 9380, Appendix J.10.1.
    # Each coordinate is written as its two Fp components, c0 then c1.
    dst = b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_"
    out = case["output"]
    expected = b"".join(b(c) for c in out["x"].split(",") + out["y"].split(","))
    assert bls.hash_to_g2(case["input"]["msg"].encode(), dst) == expected
