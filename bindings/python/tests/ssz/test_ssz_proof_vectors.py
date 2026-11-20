"""Generalized indices, Merkle proofs and chunk roots, against the vectors of ssz-specs v0.1.0."""

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.errors import SszError
from ethlib.serialization import ssz
from raising import raises

FILES = Path(__file__).resolve().parents[4] / "tests" / "serialization" / "ssz_proofs"
CASES = json.loads((FILES / "cases.json").read_text())
TYPES = CASES["types"]
VALUES = {value["name"]: value for value in CASES["values"]}

INDICES = [c for c in CASES["generalized_indices"] if c["gindex"] is not None]
REFUSED_PATHS = [c for c in CASES["generalized_indices"] if c["gindex"] is None]
PROOFS = [(v["name"], p) for v in CASES["values"] for p in v["proofs"] if p["branch"] is not None]
REFUSED_PROOFS = [
    (v["name"], p) for v in CASES["values"] for p in v["proofs"] if p["branch"] is None
]
ROOTS = [c for c in CASES["chunk_roots"] if c["root"] is not None]
REFUSED_CHUNKS = [c for c in CASES["chunk_roots"] if c["root"] is None]

ERR = "EthLib.Serialization.Ssz.Err."

# The message of EthLib for each fault of the package, filled from the fields of the case.
# The package calls an unknown field name, or a position given for a field, a missing field.
# It refuses a field name on a union as not a position, and EthLib as a missing field.
# EthLib refuses these three when it reads the path, before any SSZ fault.
FAULTS = {
    "NO_SUCH_POSITION": "path rejected: " + ERR + "noSuchPosition {step}",
    "NO_SUCH_OPTION": "path rejected: " + ERR + "noSuchOption {step}",
    "NO_PARTS": "path rejected: " + ERR + "noParts",
    "NO_PARTS_MIXIN": "path rejected: " + ERR + "noPartsMixin",
    "NO_MIXIN": "path rejected: " + ERR + "noMixin",
    "NO_SUCH_FIELD": "path: no field {step}",
    "NOT_A_POSITION": "path: no field {step}",
    "NOT_A_GINDEX": "proof rejected: " + ERR + "notAGindex {index}",
    "ROOT_HAS_NO_BRANCH": "proof rejected: " + ERR + "rootHasNoBranch",
    "PATH_INTO_MIXIN": "proof rejected: " + ERR + "pathIntoMixin",
    "PATH_INTO_PACKED": "proof rejected: " + ERR + "pathIntoPacked",
    "PATH_INTO_GAP": "proof rejected: " + ERR + "pathIntoGap",
    "PATH_PAST_SPINE": "proof rejected: " + ERR + "pathPastSpine",
    "MERKLEIZE_LIMIT": "chunks rejected: " + ERR + "merkleizeLimit {count} {limit}",
}


def _bytes(text: str) -> bytes:
    return bytes.fromhex(text.removeprefix("0x"))


def _message(case: dict) -> str:
    """The whole message of EthLib for the fault of a case."""
    return FAULTS[case["fault"]].format_map(case)


def _value(name: str) -> tuple[dict, dict]:
    """The type of a value, and the value that EthLib reads from its bytes in the file."""
    value = VALUES[name]
    ssz_type = TYPES[value["type"]]
    return ssz_type, ssz.deserialize(ssz_type, _bytes(value["serialized"]))


def _path_id(case: dict) -> str:
    return "/".join([case["type"], *map(str, case["path"])])


def _proof_id(pair: tuple[str, dict]) -> str:
    return f"{pair[0]}/{pair[1]['gindex']}"


def _chunks_id(case: dict) -> str:
    return f"{len(case['chunks'])}/{case['limit']}"


def test_digests() -> None:
    """Every file of the directory is pinned, and has its pinned digest."""
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split("  ", 1) for line in lines if not line.startswith("#")]
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name
    pinned = {name for _, name in entries} | {"SHA256SUMS", "README.md"}
    assert pinned == {path.name for path in FILES.iterdir()}


def test_counts() -> None:
    """The file holds 112 paths, 22 values with 759 indices, and 26 chunk lists."""
    assert (len(INDICES), len(REFUSED_PATHS)) == (73, 39)
    assert len(VALUES) == 22
    assert (len(PROOFS), len(REFUSED_PROOFS)) == (195, 564)
    assert (len(ROOTS), len(REFUSED_CHUNKS)) == (23, 3)


@pytest.mark.parametrize("name", VALUES)
def test_value_has_the_root_of_the_package(name: str) -> None:
    # The types and values of the file mean in EthLib what they mean in the package.
    ssz_type, value = _value(name)
    assert ssz.serialize(ssz_type, value) == _bytes(VALUES[name]["serialized"])
    assert ssz.hash_tree_root(ssz_type, value) == _bytes(VALUES[name]["root"])


@pytest.mark.parametrize("case", INDICES, ids=map(_path_id, INDICES))
def test_generalized_index(case: dict) -> None:
    assert ssz.get_generalized_index(TYPES[case["type"]], *case["path"]) == case["gindex"]


@pytest.mark.parametrize("case", REFUSED_PATHS, ids=map(_path_id, REFUSED_PATHS))
def test_generalized_index_refuses(case: dict) -> None:
    with raises(SszError, _message(case)):
        ssz.get_generalized_index(TYPES[case["type"]], *case["path"])


@pytest.mark.parametrize(("name", "case"), PROOFS, ids=map(_proof_id, PROOFS))
def test_merkle_proof(name: str, case: dict) -> None:
    ssz_type, value = _value(name)
    branch = [_bytes(node) for node in case["branch"]]
    assert ssz.compute_merkle_proof(ssz_type, value, case["gindex"]) == branch


@pytest.mark.parametrize(("name", "case"), REFUSED_PROOFS, ids=map(_proof_id, REFUSED_PROOFS))
def test_merkle_proof_refuses(name: str, case: dict) -> None:
    ssz_type, value = _value(name)
    with raises(SszError, _message(case)):
        ssz.compute_merkle_proof(ssz_type, value, case["gindex"])


@pytest.mark.parametrize("case", ROOTS, ids=map(_chunks_id, ROOTS))
def test_merkleize_chunks(case: dict) -> None:
    chunks = [_bytes(chunk) for chunk in case["chunks"]]
    assert ssz.merkleize_chunks(chunks, case["limit"]) == _bytes(case["root"])


@pytest.mark.parametrize("case", REFUSED_CHUNKS, ids=map(_chunks_id, REFUSED_CHUNKS))
def test_merkleize_chunks_refuses(case: dict) -> None:
    with raises(SszError, _message(case)):
        ssz.merkleize_chunks([_bytes(chunk) for chunk in case["chunks"]], case["limit"])
