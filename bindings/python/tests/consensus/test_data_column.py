"""The data column sidecars and the matrix of Fulu against the vectors of consensus-specs."""

import hashlib
import json
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.cryptography import _native
from ethlib.errors import KzgError
from ethlib.networking import snappy

TESTS = Path(__file__).resolve().parents[4] / "tests"
FILES = TESTS / "consensus" / "data_columns"
PROOFS = TESTS / "consensus" / "merkle_proof"
KZG = TESTS / "cryptography" / "kzg"

# The gossip reasons that name one sidecar check, and the check that each names.
REASONS = {
    "invalid sidecar": "shape",
    "invalid sidecar inclusion proof": "inclusion",
    "invalid sidecar kzg proofs": "kzg",
}

# The bytes of a cell, of a proof, of a commitment and of a matrix entry.
CELL = 2048
PROOF = 48
COMMITMENT = 48
ENTRY = CELL + PROOF + 8 + 8

_YAML = YAML(typ="safe")


def _yaml(path: Path):
    return _YAML.load(path.read_text())


def _conform(base, value):
    # Give a YAML value the JSON form of the Lean value it replaces.
    if isinstance(value, list):
        sample = base[0] if base else {}
        return [_conform(sample, item) for item in value]
    if isinstance(value, dict):
        return {key: _conform(base.get(key, ""), item) for key, item in value.items()}
    if isinstance(value, int) and isinstance(base, str):
        # YAML reads an unquoted 0x value as an integer; Lean keeps it as bytes.
        if base.startswith("0x"):
            return "0x" + value.to_bytes((len(base) - 2) // 2, "big").hex()
        return str(value)
    return value


def replacements(case_config: dict, name: str) -> dict:
    """The values of a case's configuration that the named configuration holds, in Lean's form."""
    base = json.loads(_native.consensus_config(name))
    return {key: _conform(base[key], value) for key, value in case_config.items() if key in base}


def _sidecar_parts(data: bytes) -> dict:
    """The fields of a sidecar that the tests compare, read at their SSZ offsets."""
    column, commitments, proofs = (int.from_bytes(data[i:i + 4], "little") for i in (8, 12, 16))
    header = data[20:228]
    return {
        "index": int.from_bytes(data[:8], "little"),
        "cells": [data[i:i + CELL] for i in range(column, commitments, CELL)],
        "commitments": data[commitments:proofs],
        "proofs": [data[i:i + PROOF] for i in range(proofs, len(data), PROOF)],
        "header": header,
        "branch": data[228:356],
    }


def run_gossip_case(case: Path, preset: str) -> None:
    """Run the sidecar checks of each message of a gossip case.

    A message rejected for a reason that names one check fails that check.
    Every other message passes all three, since the rest of gossip validation reads the store.
    """
    meta = _yaml(case / "meta.yaml")
    config_file = case / "config.yaml"
    config = replacements(_yaml(config_file), preset) if config_file.exists() else None
    for message in meta["messages"]:
        data = snappy.decompress((case / f"{message['message']}.ssz_snappy").read_bytes())
        try:
            kzg = consensus.verify_data_column_sidecar_kzg_proofs(preset, "fusaka", data)
        except KzgError:
            # The batch check raises on inputs it cannot read, which rejects the sidecar.
            kzg = False
        results = {
            "shape": consensus.verify_data_column_sidecar(preset, "fusaka", data, config),
            "inclusion":
                consensus.verify_data_column_sidecar_inclusion_proof(preset, "fusaka", data),
            "kzg": kzg,
        }
        failing = REASONS.get(message.get("reason"))
        if failing is None:
            assert all(results.values()), (message, results)
        else:
            assert not results[failing], (message, results)


def _gossip_cases() -> list:
    return [pytest.param(case.parts[-6], case, id=f"{case.parts[-6]}-{case.name}")
            for case in sorted(FILES.glob("*/fulu/networking/gossip_data_column_sidecar/*/*"))]


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*") if path.is_file()
                               and path.name != "SHA256SUMS")
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, case", _gossip_cases())
def test_gossip_sidecar_checks(preset, case):
    run_gossip_case(case, preset)


@pytest.mark.parametrize("preset, case", _gossip_cases())
def test_sidecars_from_column_sidecar(preset, case):
    # One sidecar and the cells of each blob give back every sidecar, the first one among them.
    meta = _yaml(case / "meta.yaml")
    data = snappy.decompress((case / f"{meta['messages'][0]['message']}.ssz_snappy").read_bytes())
    parts = _sidecar_parts(data)
    if parts["index"] >= 128 or len(parts["cells"]) * COMMITMENT != len(parts["commitments"]):
        pytest.skip("the sidecar has no valid column to rebuild")
    rows = []
    for cell, proof in zip(parts["cells"], parts["proofs"]):
        cells = [bytes(CELL)] * 128
        proofs = [bytes(PROOF)] * 128
        cells[parts["index"]], proofs[parts["index"]] = cell, proof
        rows.append((cells, proofs))
    sidecars = consensus.get_data_column_sidecars_from_column_sidecar(preset, "fusaka", data, rows)
    assert len(sidecars) == 128
    assert sidecars[parts["index"]] == data
    for index, sidecar in enumerate(sidecars):
        other = _sidecar_parts(sidecar)
        assert other["index"] == index
        assert (other["header"], other["branch"]) == (parts["header"], parts["branch"])


def _fulu_proof_cases() -> list:
    return [pytest.param(case.parts[-6], case, id=f"{case.parts[-6]}-{case.name}")
            for case in sorted(PROOFS.glob("*/fulu/merkle_proof/*/BeaconBlockBody/*"))]


@pytest.mark.parametrize("preset, case", _fulu_proof_cases())
def test_sidecars_from_block(preset, case):
    # A block around a vendored body: the branch of each sidecar is the branch of the case.
    proof = _yaml(case / "proof.yaml")
    body = snappy.decompress((case / "object.ssz_snappy").read_bytes())
    length, _ = consensus.merkle_proof(preset, "fusaka", "BeaconBlockBody", body,
                                       2 * proof["leaf_index"] + 1)
    count = int.from_bytes(length, "little")
    message = (7).to_bytes(8, "little") + (3).to_bytes(8, "little") + bytes([1]) * 32 + \
        bytes([2]) * 32 + (84).to_bytes(4, "little") + body
    block = (100).to_bytes(4, "little") + bytes(96) + message
    rows = [([bytes(CELL)] * 128, [bytes(PROOF)] * 128)] * count
    sidecars = consensus.get_data_column_sidecars_from_block(preset, "fusaka", block, rows)
    branch = b"".join(bytes.fromhex(node[2:]) for node in proof["branch"])
    body_root, _ = consensus.ssz_static(preset, "fusaka", "BeaconBlockBody", body)
    assert len(sidecars) == 128
    for index, sidecar in enumerate(sidecars):
        parts = _sidecar_parts(sidecar)
        assert parts["index"] == index
        assert parts["branch"] == branch
        # The header holds the fields of the block, the root of its body, then its signature.
        assert parts["header"] == message[:80] + body_root + bytes(96)
        assert len(parts["cells"]) == count
        assert consensus.verify_data_column_sidecar_inclusion_proof(preset, "fusaka", sidecar)


def test_sidecars_need_one_row_per_commitment():
    case = sorted(PROOFS.glob("minimal/fulu/merkle_proof/*/BeaconBlockBody/*"))[0]
    body = snappy.decompress((case / "object.ssz_snappy").read_bytes())
    message = bytes(80) + (84).to_bytes(4, "little") + body
    block = (100).to_bytes(4, "little") + bytes(96) + message
    rows = [([bytes(CELL)] * 128, [bytes(PROOF)] * 128)] * 200
    with pytest.raises(Exception):
        consensus.get_data_column_sidecars_from_block("minimal", "fusaka", block, rows)


def _kzg_case(i: int) -> tuple:
    name = f"compute_cells_and_kzg_proofs_case_valid_{i}"
    data = _yaml(KZG / "compute_cells_and_kzg_proofs" / name / "data.yaml")
    cells, proofs = ([bytes.fromhex(x[2:]) for x in part] for part in data["output"])
    return bytes.fromhex(data["input"]["blob"][2:]), cells, proofs


def _entry(entry: bytes) -> tuple:
    return (entry[:CELL], entry[CELL:CELL + PROOF],
            int.from_bytes(entry[CELL + PROOF:CELL + PROOF + 8], "little"),
            int.from_bytes(entry[CELL + PROOF + 8:], "little"))


def test_compute_and_recover_matrix():
    # The matrix of two blobs holds the cells and proofs of the KZG vectors, row after row.
    cases = [_kzg_case(i) for i in (0, 1)]
    matrix = consensus.compute_matrix([blob for blob, _, _ in cases])
    assert len(matrix) == 2 * 128
    for row, (_, cells, proofs) in enumerate(cases):
        for column in range(128):
            expected = (cells[column], proofs[column], column, row)
            assert _entry(matrix[128 * row + column]) == expected
    # Half of the columns recover the whole matrix.
    kept = [entry for entry in matrix if _entry(entry)[2] % 2 == 1]
    assert consensus.recover_matrix(kept, 2) == matrix
    # One column fewer than half is not enough.
    with pytest.raises(KzgError):
        consensus.recover_matrix([e for e in kept if _entry(e)[2] != 1], 2)


def test_no_data_column_sidecar_before_fulu():
    with pytest.raises(Exception):
        consensus.verify_data_column_sidecar_inclusion_proof("minimal", "pectra", b"")
