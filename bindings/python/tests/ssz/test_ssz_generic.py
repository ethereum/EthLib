"""SSZ against the ssz_generic vectors of consensus-spec-tests."""

import hashlib
import re
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.errors import SszError
from ethlib.networking import snappy
from ethlib.serialization import ssz

FILES = Path(__file__).resolve().parents[4] / "tests" / "serialization" / "ssz_generic"
CASES = FILES / "general" / "phase0" / "ssz_generic"

# The valid and invalid cases of each handler, as the release counts them.
COUNTS = {
    "basic_progressive_list": (320, 567),
    "basic_vector": (200, 957),
    "bitlist": (450, 44),
    "bitvector": (54, 31),
    "boolean": (2, 4),
    "compatible_unions": (210, 311),
    "progressive_bitlist": (700, 3),
    "uints": (48, 18),
}

SUITES = ("valid", "invalid")

BOOL = "bool"
BYTE = {"uint": 1}
UINT16 = {"uint": 2}
PROGRESSIVE_BITLIST = {"progressive_bitlist": None}

# The element types that a type name can carry.
ELEMENTS = {
    "bool": BOOL,
    **{f"uint{bits}": {"uint": bits // 8} for bits in (8, 16, 32, 64, 128, 256)},
}


def _progressive_container(active, fields):
    """A progressive container: its layout bits, then its fields in order."""
    layout = [bool(bit) for bit in active]
    return {"progressive_container": [layout, [list(field) for field in fields]]}


# The structures that the compatible unions name, as the format of the suite defines them.
SINGLE_FIELD = _progressive_container([1], [("A", BYTE)])
SINGLE_LIST = _progressive_container([0, 0, 0, 0, 1], [("C", PROGRESSIVE_BITLIST)])
VAR = _progressive_container(
    [1, 0, 1, 0, 1], [("A", BYTE), ("B", {"list": [UINT16, 123]}), ("C", PROGRESSIVE_BITLIST)]
)

# The unions, longest name first, so that a name matches its own entry and not a prefix.
UNIONS = {
    "CompatibleUnionABCA": {"compatible_union": [
        [1, SINGLE_FIELD], [2, SINGLE_LIST], [3, VAR], [4, SINGLE_FIELD],
    ]},
    "CompatibleUnionBC": {"compatible_union": [[2, SINGLE_LIST], [3, VAR]]},
    "CompatibleUnionA": {"compatible_union": [[1, SINGLE_FIELD]]},
}


def type_of(handler: str, case: str):
    """The type that the name of a case declares, by the templates of the suite."""
    parts = case.split("_")
    if handler == "uints":
        return {"uint": int(parts[1]) // 8}
    if handler == "boolean":
        return BOOL
    if handler == "basic_vector":
        return {"vector": [ELEMENTS[parts[1]], int(parts[2])]}
    if handler == "basic_progressive_list":
        return {"progressive_list": [ELEMENTS[parts[1]], None]}
    if handler == "bitvector":
        return {"bitvector": int(parts[1])}
    if handler == "bitlist":
        return {"bitlist": int(parts[1])}
    if handler == "progressive_bitlist":
        return PROGRESSIVE_BITLIST
    if handler == "compatible_unions":
        return next(union for name, union in UNIONS.items() if case.startswith(name + "_"))
    raise AssertionError(f"no type for the handler {handler}")


def _bits(data: bytes, count: int) -> list[bool]:
    """The first `count` bits of bytes, from the lowest bit of the first byte."""
    return [bool(data[i // 8] >> (i % 8) & 1) for i in range(count)]


def _delimited(text: str) -> list[bool]:
    """The bits of a bitlist that the suite writes as hex, closing bit included."""
    data = bytes.fromhex(text.removeprefix("0x"))
    return _bits(data, 8 * len(data) - 8 + data[-1].bit_length() - 1)


def tagged(ssz_type, value):
    """The tagged form that the binding takes of a value that a case writes."""
    if ssz_type == BOOL:
        return {"bool": value}
    (kind, body), = ssz_type.items()
    if kind == "uint":
        return {"uint": int(value)}
    if kind == "bitvector":
        return {"bits": _bits(bytes.fromhex(value.removeprefix("0x")), body)}
    if kind in ("bitlist", "progressive_bitlist"):
        return {"bits": _delimited(value)}
    if kind in ("vector", "list", "progressive_list"):
        return {"seq": [tagged(body[0], element) for element in value]}
    if kind == "progressive_container":
        return {"seq": [tagged(field, value[name]) for name, field in body[1]]}
    if kind == "compatible_union":
        option = dict(body)[value["selector"]]
        return {"union": [value["selector"], tagged(option, value["data"])]}
    raise AssertionError(f"no reader for the type {kind}")


def _load(path: Path):
    return YAML(typ="safe").load(path.read_text(encoding="utf-8"))


def _serialized(case: Path) -> bytes:
    return snappy.decompress((case / "serialized.ssz_snappy").read_bytes())


def _cases(suite: str) -> list:
    return [
        pytest.param(handler, case, id=f"{handler}/{case.name}")
        for handler in COUNTS
        for case in sorted((CASES / handler / suite).iterdir())
    ]


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in (FILES / "general").rglob("*") if path.is_file())
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_counts():
    found = {
        handler.name: tuple(sum(1 for _ in (handler / suite).iterdir()) for suite in SUITES)
        for handler in CASES.iterdir()
    }
    assert found == COUNTS


@pytest.mark.parametrize(("handler", "case"), _cases("valid"))
def test_valid(handler: str, case: Path) -> None:
    ssz_type = type_of(handler, case.name)
    value = tagged(ssz_type, _load(case / "value.yaml"))
    encoded = _serialized(case)
    assert ssz.serialize(ssz_type, value) == encoded
    assert ssz.deserialize(ssz_type, encoded) == value
    root = _load(case / "meta.yaml")["root"]
    assert "0x" + ssz.hash_tree_root(ssz_type, value).hex() == root


# The invalid cases whose type is itself illegal: SSZ has no vector of no elements.
ILLEGAL_TYPE = re.compile(r"(vec_[a-z0-9]+|bitvec)_0$")


@pytest.mark.parametrize(("handler", "case"), _cases("invalid"))
def test_invalid(handler: str, case: Path) -> None:
    ssz_type = type_of(handler, case.name)
    stage = "type" if ILLEGAL_TYPE.fullmatch(case.name) else "input"
    with pytest.raises(SszError, match=f"^{stage} rejected: "):
        ssz.deserialize(ssz_type, _serialized(case))
