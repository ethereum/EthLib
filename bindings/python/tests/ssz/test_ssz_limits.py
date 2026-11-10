"""SSZ of lists whose limits reach 2^32 or 2^64 bytes or chunks, against ssz-specs v0.1.0."""

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.errors import SszError
from ethlib.serialization import ssz
from raising import raises

FILES = Path(__file__).resolve().parents[4] / "tests" / "serialization" / "ssz_limits"
CASES = json.loads((FILES / "cases.json").read_text())
VALID = [c for c in CASES if c["root"] is not None]
INVALID = [c for c in CASES if c["root"] is None]


def _type(case: dict) -> dict:
    """The type of a case, in the tagged form of the bindings."""
    if case["kind"] == "list":
        return {"list": [{"uint": case["width"]}, case["limit"]]}
    return {case["kind"]: case["limit"]}


def _value(case: dict) -> dict:
    """The value of a valid case, in the tagged form of the bindings."""
    if case["kind"] == "list":
        return {"seq": [{"uint": n} for n in case["value"]]}
    if case["kind"] == "byte_list":
        return {"bytes": "0x" + bytes(case["value"]).hex()}
    return {"bits": case["value"]}


def _data(case: dict) -> bytes:
    return bytes.fromhex(case["serialized"].removeprefix("0x"))


def test_digests() -> None:
    """Every file of the directory is pinned, and has its pinned digest."""
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split("  ", 1) for line in lines if not line.startswith("#")]
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name
    pinned = {name for _, name in entries} | {"SHA256SUMS", "README.md"}
    assert pinned == {path.name for path in FILES.iterdir()}


def test_counts() -> None:
    """The file holds 75 values and 36 rejected inputs, over 25 types."""
    assert (len(VALID), len(INVALID)) == (75, 36)
    assert len({c["name"].split("/")[0] for c in CASES}) == 25


@pytest.mark.parametrize("case", VALID, ids=[c["name"] for c in VALID])
def test_valid(case: dict) -> None:
    kind, value, data = _type(case), _value(case), _data(case)
    assert ssz.serialize(kind, value) == data
    assert ssz.deserialize(kind, data) == value
    assert ssz.hash_tree_root(kind, value).hex() == case["root"].removeprefix("0x")


def _rejection(case: dict) -> tuple[str, int]:
    """The message and the code with which the decoder rejects an invalid case."""
    if case["reason"] == "partial_element":
        return f"scopeUndivided {len(_data(case))} {case['width']}", 5
    return {"empty": ("emptyEncoding", 16), "no_delimiter": ("trailingZeros", 18)}[case["reason"]]


@pytest.mark.parametrize("case", INVALID, ids=[c["name"] for c in INVALID])
def test_invalid(case: dict) -> None:
    error, code = _rejection(case)
    with raises(SszError, f"input rejected: EthLib.Serialization.Ssz.Err.{error}") as caught:
        ssz.deserialize(_type(case), _data(case))
    assert caught.value.code == code
