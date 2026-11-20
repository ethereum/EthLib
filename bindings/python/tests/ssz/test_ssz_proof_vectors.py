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
INDICES = CASES["generalized_indices"]
VALUES = {value["name"]: value for value in CASES["values"]}
PROOFS = [(value["name"], proof) for value in CASES["values"] for proof in value["proofs"]]
CHUNKS = CASES["chunk_roots"]

ERR = "EthLib.Serialization.Ssz.Err."

# The message of EthLib for each fault of the package, filled from the fields of the case.
# The package names a field position in a container, or a field name in a union, a missing field.
FAULTS = {
    "NO_SUCH_POSITION": "path rejected: " + ERR + "noSuchPosition {step}",
    "NO_SUCH_OPTION": "path rejected: " + ERR + "noSuchOption {step}",
    "NO_PARTS": "path rejected: " + ERR + "noParts",
    "NO_PARTS_MIXIN": "path rejected: " + ERR + "noPartsMixin",
    "NO_MIXIN": "path rejected: " + ERR + "noMixin",
    "NO_SUCH_FIELD": "path: no field {step}",
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


def test_digests() -> None:
    """Every file of the directory is pinned, and has its pinned digest."""
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split("  ", 1) for line in lines if not line.startswith("#")]
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name
    pinned = {name for _, name in entries} | {"SHA256SUMS", "README.md"}
    assert pinned == {path.name for path in FILES.iterdir()}


def test_counts() -> None:
    """The file holds 95 paths, 18 values with 605 indices, and 26 chunk lists."""
    assert len(INDICES) == 95
    assert (len(VALUES), len(PROOFS)) == (18, 605)
    assert len(CHUNKS) == 26


@pytest.mark.parametrize("name", VALUES)
def test_value_has_the_root_of_the_package(name: str) -> None:
    # The types and values of the file mean in EthLib what they mean in the package.
    ssz_type, value = _value(name)
    assert ssz.serialize(ssz_type, value) == _bytes(VALUES[name]["serialized"])
    assert ssz.hash_tree_root(ssz_type, value) == _bytes(VALUES[name]["root"])


@pytest.mark.parametrize("case", INDICES, ids=[f"{c['type']}{c['path']}" for c in INDICES])
def test_generalized_index(case: dict) -> None:
    ssz_type = TYPES[case["type"]]
    if case["gindex"] is None:
        with raises(SszError, _message(case)):
            ssz.get_generalized_index(ssz_type, *case["path"])
    else:
        assert ssz.get_generalized_index(ssz_type, *case["path"]) == case["gindex"]


@pytest.mark.parametrize(("name", "case"), PROOFS, ids=[f"{n}-{c['gindex']}" for n, c in PROOFS])
def test_merkle_proof(name: str, case: dict) -> None:
    ssz_type, value = _value(name)
    if case["branch"] is None:
        with raises(SszError, _message(case)):
            ssz.compute_merkle_proof(ssz_type, value, case["gindex"])
    else:
        branch = [_bytes(node) for node in case["branch"]]
        assert ssz.compute_merkle_proof(ssz_type, value, case["gindex"]) == branch


@pytest.mark.parametrize("case", CHUNKS, ids=[f"{len(c['chunks'])}-{c['limit']}" for c in CHUNKS])
def test_merkleize_chunks(case: dict) -> None:
    chunks = [_bytes(chunk) for chunk in case["chunks"]]
    if case["root"] is None:
        with raises(SszError, _message(case)):
            ssz.merkleize_chunks(chunks, case["limit"])
    else:
        assert ssz.merkleize_chunks(chunks, case["limit"]) == _bytes(case["root"])
