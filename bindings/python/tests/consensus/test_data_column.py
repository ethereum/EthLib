"""The data column sidecars and the matrix, from Fulu, against the vectors of consensus-specs."""

import hashlib
import json
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.cryptography import _native
from ethlib.errors import KzgError, SszError
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

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

# From Gloas, the gossip reasons that gossip validation gives before it reads the block.
BEFORE_BLOCK = {
    "already seen sidecar for this block root and index",
    "sidecar is for wrong subnet",
    "sidecar is from a future slot",
    "block for sidecar's beacon block root has not been seen",
}

# The forks from Gloas on, where a sidecar names its block by root.
GLOAS = ("glamsterdam", "hegota")

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
    column, commitments, proofs = (int.from_bytes(data[i : i + 4], "little") for i in (8, 12, 16))
    header = data[20:228]
    return {
        "index": int.from_bytes(data[:8], "little"),
        "cells": [data[i : i + CELL] for i in range(column, commitments, CELL)],
        "commitments": data[commitments:proofs],
        "proofs": [data[i : i + PROOF] for i in range(proofs, len(data), PROOF)],
        "header": header,
        "branch": data[228:356],
    }


def _gloas_sidecar_parts(data: bytes) -> dict:
    """The fields of a sidecar from Gloas, read at their SSZ offsets."""
    column, proofs = (int.from_bytes(data[i : i + 4], "little") for i in (8, 12))
    return {
        "index": int.from_bytes(data[:8], "little"),
        "cells": [data[i : i + CELL] for i in range(column, proofs, CELL)],
        "proofs": [data[i : i + PROOF] for i in range(proofs, len(data), PROOF)],
        "slot": data[16:24],
        "root": data[24:56],
    }


def case_blocks(case: Path, preset: str, fork: str) -> dict:
    """The signed blocks of a gossip case, by the root of their message."""
    blocks = {}
    for entry in _yaml(case / "meta.yaml").get("blocks", []):
        signed = snappy.decompress((case / f"{entry['block']}.ssz_snappy").read_bytes())
        offset = int.from_bytes(signed[:4], "little")
        root, _ = consensus.ssz_static(preset, fork, "BeaconBlock", signed[offset:])
        blocks[root] = signed
    return blocks


def run_gossip_case(case: Path, preset: str) -> None:
    """Run the sidecar checks of each message of a gossip case.

    A message rejected for a reason that names one check fails that check.
    Every other message passes them all, since the rest of gossip validation reads the store.
    """
    fork = FORKS[case.parts[-5]]
    meta = _yaml(case / "meta.yaml")
    config_file = case / "config.yaml"
    config = replacements(_yaml(config_file), preset) if config_file.exists() else None
    blocks = case_blocks(case, preset, fork) if fork in GLOAS else {}
    for message in meta["messages"]:
        data = snappy.decompress((case / f"{message['message']}.ssz_snappy").read_bytes())
        block = b""
        if fork in GLOAS:
            # From Gloas the commitments are in the bid of the block that the sidecar names.
            block = blocks.get(_gloas_sidecar_parts(data)["root"])
            if block is None:
                assert message.get("reason") in BEFORE_BLOCK, message
                continue
        try:
            kzg = consensus.verify_data_column_sidecar_kzg_proofs(preset, fork, data, block)
        except KzgError:
            # The batch check raises on inputs it cannot read, which rejects the sidecar.
            kzg = False
        results = {
            "shape": consensus.verify_data_column_sidecar(preset, fork, data, block, config),
            "kzg": kzg,
        }
        if fork not in GLOAS:
            results["inclusion"] = consensus.verify_data_column_sidecar_inclusion_proof(
                preset, fork, data
            )
        failing = REASONS.get(message.get("reason"))
        if failing is None:
            assert all(results.values()), (message, results)
        else:
            assert not results[failing], (message, results)


def _gossip_cases(fork: str = "*") -> list:
    return [
        pytest.param(case.parts[-6], case, id=f"{case.parts[-6]}-{case.parts[-5]}-{case.name}")
        for case in sorted(FILES.glob(f"*/{fork}/networking/gossip_data_column_sidecar/*/*"))
    ]


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1 for path in FILES.rglob("*") if path.is_file() and path.name != "SHA256SUMS"
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, case", _gossip_cases())
def test_gossip_sidecar_checks(preset, case):
    run_gossip_case(case, preset)


@pytest.mark.parametrize("preset, case", _gossip_cases("fulu"))
def test_sidecars_from_column_sidecar(preset, case):
    # One sidecar and the cells of each blob give back every sidecar, the first one among them.
    meta = _yaml(case / "meta.yaml")
    data = snappy.decompress((case / f"{meta['messages'][0]['message']}.ssz_snappy").read_bytes())
    parts = _sidecar_parts(data)
    if parts["index"] >= 128 or len(parts["cells"]) * COMMITMENT != len(parts["commitments"]):
        pytest.skip("the sidecar has no valid column to rebuild")
    rows = []
    for cell, proof in zip(parts["cells"], parts["proofs"], strict=True):
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


def _valid_gloas_messages() -> list:
    params = []
    for gloas in ("gloas", "heze"):
        for param in _gossip_cases(gloas):
            preset, case = param.values
            for message in _yaml(case / "meta.yaml")["messages"]:
                if message["expected"] == "valid":
                    params.append(
                        pytest.param(
                            preset,
                            case,
                            message["message"],
                            id=f"{param.id}-{message['message'][-8:]}",
                        )
                    )
    return params


@pytest.mark.parametrize("preset, case, name", _valid_gloas_messages())
def test_gloas_sidecars_from_block_and_sidecar(preset, case, name):
    # From Gloas the block, or one sidecar, and the cells of a column give back that sidecar.
    fork = FORKS[case.parts[-5]]
    data = snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())
    parts = _gloas_sidecar_parts(data)
    rows = []
    for cell, proof in zip(parts["cells"], parts["proofs"], strict=True):
        cells = [bytes(CELL)] * 128
        proofs = [bytes(PROOF)] * 128
        cells[parts["index"]], proofs[parts["index"]] = cell, proof
        rows.append((cells, proofs))
    block = case_blocks(case, preset, fork)[parts["root"]]
    from_block = consensus.get_data_column_sidecars_from_block(preset, fork, block, rows)
    from_sidecar = consensus.get_data_column_sidecars_from_column_sidecar(preset, fork, data, rows)
    assert len(from_block) == 128
    assert from_block == from_sidecar
    assert from_block[parts["index"]] == data
    for index, sidecar in enumerate(from_block):
        other = _gloas_sidecar_parts(sidecar)
        assert other["index"] == index
        assert (other["slot"], other["root"]) == (parts["slot"], parts["root"])


def _first_message(case: Path) -> bytes:
    meta = _yaml(case / "meta.yaml")
    return snappy.decompress((case / f"{meta['messages'][0]['message']}.ssz_snappy").read_bytes())


def test_sidecar_and_block_must_match():
    gloas = _first_message(_gossip_cases("gloas")[0].values[1])
    # From Gloas the check decodes the signed block, so bytes that are not one, or no block, fail.
    with raises(SszError, "block rejected: EthLib.Serialization.Ssz.Err.firstOffset 100 0"):
        consensus.verify_data_column_sidecar("minimal", "glamsterdam", gloas, bytes(200))
    with raises(KzgError, "block rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 100 0"):
        consensus.verify_data_column_sidecar_kzg_proofs("minimal", "glamsterdam", gloas)
    # No sidecar from Gloas has an inclusion proof.
    with raises(SszError, "no form of this check at glamsterdam"):
        consensus.verify_data_column_sidecar_inclusion_proof("minimal", "glamsterdam", gloas)
    # Before Gloas the sidecar carries its commitments, so a block is refused.
    fulu = _first_message(_gossip_cases("fulu")[0].values[1])
    with raises(KzgError, "no block for a sidecar at fusaka"):
        consensus.verify_data_column_sidecar_kzg_proofs("minimal", "fusaka", fulu, b"\x00")


def _gloas_sidecar_and_block() -> tuple:
    """The preset, a sidecar and its signed block, from the first Gloas case that has both."""
    for param in _gossip_cases("gloas"):
        preset, case = param.values
        blocks = case_blocks(case, preset, "glamsterdam")
        for message in _yaml(case / "meta.yaml")["messages"]:
            data = snappy.decompress((case / f"{message['message']}.ssz_snappy").read_bytes())
            block = blocks.get(_gloas_sidecar_parts(data)["root"])
            if block is not None:
                return preset, data, block
    raise LookupError("no Gloas case has a sidecar with its block")


def test_block_of_another_root():
    preset, data, block = _gloas_sidecar_and_block()
    # The block of the sidecar decodes and matches, so the checks return a verdict.
    consensus.verify_data_column_sidecar(preset, "glamsterdam", data, block)
    consensus.verify_data_column_sidecar_kzg_proofs(preset, "glamsterdam", data, block)
    # A new state root changes the root of the block, and nothing else that the checks read.
    # The message starts at the offset in the first 4 bytes, with the slot, the proposer index
    # and the parent root before the state root.
    other = bytearray(block)
    other[int.from_bytes(block[:4], "little") + 48] ^= 1
    expected = "the block is not the block of the sidecar"
    with raises(SszError, expected) as info:
        consensus.verify_data_column_sidecar(preset, "glamsterdam", data, bytes(other))
    assert info.value.code == 0
    with raises(KzgError, expected) as info:
        consensus.verify_data_column_sidecar_kzg_proofs(preset, "glamsterdam", data, bytes(other))
    assert info.value.code == 0


def _fulu_proof_cases() -> list:
    return [
        pytest.param(case.parts[-6], case, id=f"{case.parts[-6]}-{case.name}")
        for case in sorted(PROOFS.glob("*/fulu/merkle_proof/*/BeaconBlockBody/*"))
    ]


@pytest.mark.parametrize("preset, case", _fulu_proof_cases())
def test_sidecars_from_block(preset, case):
    # A block around a vendored body: the branch of each sidecar is the branch of the case.
    proof = _yaml(case / "proof.yaml")
    body = snappy.decompress((case / "object.ssz_snappy").read_bytes())
    length, _ = consensus.merkle_proof(
        preset, "fusaka", "BeaconBlockBody", body, 2 * proof["leaf_index"] + 1
    )
    count = int.from_bytes(length, "little")
    message = (
        (7).to_bytes(8, "little")
        + (3).to_bytes(8, "little")
        + bytes([1]) * 32
        + bytes([2]) * 32
        + (84).to_bytes(4, "little")
        + body
    )
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
    with raises(SszError, "sidecars rejected: EthLib.Serialization.Ssz.Err.count 1 200"):
        consensus.get_data_column_sidecars_from_block("minimal", "fusaka", block, rows)


def _kzg_case(i: int) -> tuple:
    name = f"compute_cells_and_kzg_proofs_case_valid_{i}"
    data = _yaml(KZG / "compute_cells_and_kzg_proofs" / name / "data.yaml")
    cells, proofs = ([bytes.fromhex(x[2:]) for x in part] for part in data["output"])
    return bytes.fromhex(data["input"]["blob"][2:]), cells, proofs


def _entry(entry: bytes) -> tuple:
    return (
        entry[:CELL],
        entry[CELL : CELL + PROOF],
        int.from_bytes(entry[CELL + PROOF : CELL + PROOF + 8], "little"),
        int.from_bytes(entry[CELL + PROOF + 8 :], "little"),
    )


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
    with raises(KzgError, "not enough cells provided"):
        consensus.recover_matrix([e for e in kept if _entry(e)[2] != 1], 2)


def test_no_data_column_sidecar_before_fulu():
    with raises(SszError, "no data column sidecar at pectra"):
        consensus.verify_data_column_sidecar_inclusion_proof("minimal", "pectra", b"")
