"""SSZ against the test vectors of the ssz-specs release v0.1.0."""

import hashlib
import json
import re
from pathlib import Path

import pytest

from ethlib.errors import SszError
from ethlib.serialization import ssz

FILES = Path(__file__).resolve().parents[4] / "tests" / "serialization" / "ssz"

# The cases of each fixture directory, as the release counts them.
COUNTS = {
    "test_basic_types": 59,
    "test_compatible_unions": 16,
    "test_decode_failure_smoke": 1,
    "test_merkleization_boundaries": 8,
    "test_progressive_containers": 15,
    "test_progressive_types": 18,
}

BOOL = "bool"
UINT8, UINT16, UINT32, UINT64 = ({"uint": n} for n in (1, 2, 4, 8))
BYTES32 = {"byte_vector": 32}


def _progressive_container(active, fields):
    """A progressive container: its layout bits, then its fields in order."""
    layout = [bool(bit) for bit in active]
    return {"progressive_container": [layout, [list(field) for field in fields]]}


def _progressive_list(element):
    """A progressive list, with no limit."""
    return {"progressive_list": [element, None]}


# The types of the release, written out from the filler classes of its source tree.
# A name can mean another type in another directory, so each directory has its own table.
BASIC = {
    "Boolean": BOOL,
    "Uint8": UINT8,
    "Uint16": UINT16,
    "Uint32": UINT32,
    "Uint64": UINT64,
    "Uint128": {"uint": 16},
    "Uint256": {"uint": 32},
    "Bytes4": {"byte_vector": 4},
    "Bytes32": BYTES32,
    "Bytes52": {"byte_vector": 52},
    "Bytes64": {"byte_vector": 64},
    "ByteList512KiB": {"byte_list": 512 * 1024},
    "SampleBitVector8": {"bitvector": 8},
    "SampleBitVector64": {"bitvector": 64},
    "SampleBitList16": {"bitlist": 16},
    "SampleUint16Vector3": {"vector": [UINT16, 3]},
    "SampleUint64Vector4": {"vector": [UINT64, 4]},
    "SampleUint32List16": {"list": [UINT32, 16]},
    "SampleBytes32List8": {"list": [BYTES32, 8]},
}

UNION_SQUARE = _progressive_container([1, 0, 1], [("side", UINT16), ("color", UINT8)])
UNION_CIRCLE = _progressive_container([0, 1, 1], [("radius", UINT16), ("color", UINT8)])
UNION_LIST4 = {"list": [UINT16, 4]}
UNION_SHAPE = {"compatible_union": [[1, UNION_SQUARE], [2, UNION_CIRCLE], [127, UNION_SQUARE]]}
UNIONS = {
    "SampleShape": UNION_SHAPE,
    "SampleNumbers": {"compatible_union": [[1, UNION_LIST4], [2, UNION_LIST4]]},
    "SampleEmptyProne": {"compatible_union": [
        [1, _progressive_list(UNION_SQUARE)], [2, _progressive_list(UNION_CIRCLE)],
    ]},
    "SampleNestedShape": {"compatible_union": [
        [1, UNION_SHAPE], [2, {"compatible_union": [[5, UNION_SQUARE]]}],
    ]},
    "SampleShapeContainer": {"container": [["tag", UINT64], ["body", UNION_SHAPE]]},
    "SampleShapeProgressiveContainer": _progressive_container(
        [1, 0, 1], [("tag", UINT64), ("body", UNION_SHAPE)]
    ),
    "SampleShapeProgressiveList": _progressive_list(UNION_SHAPE),
}

SMOKE = {"SmokeBitList8": {"bitlist": 8}}

BOUNDARIES = {
    **{f"BoundaryBitVector{n}": {"bitvector": n} for n in (1, 7, 9, 255, 256, 257)},
    "BoundaryBitList256": {"bitlist": 256},
    "BoundaryUint64List32": {"list": [UINT64, 32]},
}

SQUARE = _progressive_container([1, 0, 1], [("side", UINT16), ("color", UINT8)])
CONTAINERS = {
    "SampleSquare": SQUARE,
    "SampleCircle": _progressive_container([0, 1, 1], [("radius", UINT16), ("color", UINT8)]),
    "SampleOneField": _progressive_container([1], [("a", UINT16)]),
    "SampleLeadingGaps": _progressive_container([0, 0, 1], [("c", UINT32)]),
    "SampleMultipleGaps": _progressive_container(
        [1, 0, 0, 1, 0, 1], [("a", UINT8), ("b", UINT16), ("c", UINT32)]
    ),
    "SampleWidestLayout": _progressive_container([0] * 255 + [1], [("tail", UINT8)]),
    "SampleLevelBoundary": _progressive_container(
        [1] + [0] * 20 + [1], [("first", UINT16), ("last", UINT8)]
    ),
    "SampleBoundedListField": _progressive_container(
        [1, 0, 1], [("head", UINT64), ("body", {"list": [UINT16, 4]})]
    ),
    "SampleProgressiveFields": _progressive_container([1, 1, 1], [
        ("head", UINT64),
        ("numbers", _progressive_list(UINT64)),
        ("flags", {"progressive_bitlist": None}),
    ]),
    "SampleOuterShape": _progressive_container([1, 0, 1], [
        ("head", UINT8),
        ("inner", _progressive_container([1, 0, 1], [("x", UINT16), ("y", UINT8)])),
    ]),
    "SampleSquareProgressiveList": _progressive_list(SQUARE),
    "SampleShapeContainer": {"container": [["tag", UINT8], ["shape", SQUARE]]},
}

PROGRESSIVE = {
    "ProgressiveBitList": {"progressive_bitlist": None},
    "SampleUint64ProgressiveList": _progressive_list(UINT64),
    "SampleBytes32ProgressiveList": _progressive_list(BYTES32),
    "SampleNestedProgressiveList": _progressive_list(_progressive_list(UINT16)),
    "SampleContainerWithProgressiveList": {"container": [
        ["a", UINT16], ["b", _progressive_list(UINT64)], ["c", UINT8],
    ]},
}

TYPES = {
    "test_basic_types": BASIC,
    "test_compatible_unions": UNIONS,
    "test_decode_failure_smoke": SMOKE,
    "test_merkleization_boundaries": BOUNDARIES,
    "test_progressive_containers": CONTAINERS,
    "test_progressive_types": PROGRESSIVE,
}

def _scope(compare):
    """Whether a Lean error is a byte budget, other than the width, that passes `compare`."""
    def check(fault: str) -> bool:
        match = re.fullmatch(r"scope (\d+) (\d+)", fault)
        return match is not None and compare(int(match.group(2)), int(match.group(1)))
    return check


_short = _scope(lambda budget, width: budget < width)

# Whether a Lean error names each rejection reason of the release.
# The release says SCOPE for bytes past a fixed width, and TRUNCATED for bytes short of it.
# EthLib names both a budget that is not the width, with the width and the budget.
REJECTION = {
    "FIRST_OFFSET": lambda fault: re.fullmatch(r"firstOffset \d+ \d+", fault) is not None,
    "LIMIT": lambda fault: re.fullmatch(r"overLimit \d+ \d+", fault) is not None,
    "NO_SELECTOR": lambda fault: fault == "noSelector",
    "SCOPE": _scope(lambda budget, width: budget > width),
    "TRUNCATED": lambda fault: fault == "truncated" or _short(fault),
    "UNKNOWN_SELECTOR": lambda fault: re.fullmatch(r"unknownSelector \d+", fault) is not None,
}


def _tagged(ssz_type, value):
    """The tagged form that the binding takes of a value that a fixture writes."""
    if ssz_type == BOOL:
        return {"bool": value}
    (kind, body), = ssz_type.items()
    if kind == "uint":
        return {"uint": int(value)}
    if kind == "byte_vector":
        return {"bytes": value}
    if kind == "byte_list":
        return {"bytes": value["data"]}
    if kind in ("bitvector", "bitlist", "progressive_bitlist"):
        return {"bits": value["data"]}
    if kind in ("vector", "list", "progressive_list"):
        return {"seq": [_tagged(body[0], element) for element in value["data"]]}
    if kind == "container":
        return {"seq": [_tagged(field, value[name]) for name, field in body]}
    if kind == "progressive_container":
        return {"seq": [_tagged(field, value[name]) for name, field in body[1]]}
    if kind == "compatible_union":
        option = dict(body)[value["selector"]]
        return {"union": [value["selector"], _tagged(option, value["data"])]}
    raise AssertionError(f"no reader for the type {kind}")


def _cases():
    """Each case of the release: its directory, file name and fixture."""
    cases = []
    for path in sorted(FILES.glob("*/*.json")):
        (fixture,) = json.loads(path.read_text(encoding="utf-8")).values()
        cases.append(pytest.param(path.parent.name, fixture, id=path.stem))
    return cases


CASES = _cases()


def _accepted():
    return [case for case in CASES if "rejectionReason" not in case.values[1]]


def _rejected():
    return [case for case in CASES if "rejectionReason" in case.values[1]]


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for _ in FILES.rglob("*.json"))
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_counts():
    found = {}
    for case in CASES:
        found[case.values[0]] = found.get(case.values[0], 0) + 1
    assert found == COUNTS


@pytest.mark.parametrize(("directory", "fixture"), _accepted())
def test_accepted(directory: str, fixture: dict) -> None:
    ssz_type = TYPES[directory][fixture["typeName"]]
    value = _tagged(ssz_type, fixture["value"])
    encoded = bytes.fromhex(fixture["serialized"].removeprefix("0x"))
    assert ssz.serialize(ssz_type, value) == encoded
    assert ssz.deserialize(ssz_type, encoded) == value
    assert ssz.hash_tree_root(ssz_type, value).hex() == fixture["root"].removeprefix("0x")


@pytest.mark.parametrize(("directory", "fixture"), _rejected())
def test_rejected(directory: str, fixture: dict) -> None:
    ssz_type = TYPES[directory][fixture["typeName"]]
    data = bytes.fromhex(fixture["rawBytes"].removeprefix("0x"))
    with pytest.raises(SszError, match=r"^input rejected: EthLib\.Serialization\.Ssz\.Err\.") as e:
        ssz.deserialize(ssz_type, data)
    fault = str(e.value).rpartition("Err.")[2]
    assert REJECTION[fixture["rejectionReason"]](fault), fault
