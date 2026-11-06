"""The checks of the partial data column sidecars of Fulu that EthLib exports alone."""

from pathlib import Path

from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

TESTS = Path(__file__).resolve().parents[4] / "tests"
GOSSIP = TESTS / "consensus" / "gossip"

# The bytes of a cell, of a proof and of a block header.
CELL = 2048
PROOF = 48
HEADER = 112

_YAML = YAML(typ="safe")


def _yaml(path: Path):
    return _YAML.load(path.read_text())


def _bits(data: bytes) -> list:
    # A bitlist ends with a delimiter bit, the highest set bit of its last byte.
    length = 8 * (len(data) - 1) + data[-1].bit_length() - 1
    return [bool(data[i // 8] >> (i % 8) & 1) for i in range(length)]


def _offsets(data: bytes, count: int) -> list:
    return [int.from_bytes(data[4 * i : 4 * i + 4], "little") for i in range(count)] + [len(data)]


def header_parts(data: bytes) -> dict:
    """The fields of a partial header that the checks read, at their SSZ offsets."""
    start = int.from_bytes(data[:4], "little")
    return {"bytes": data, "message": data[4 : 4 + HEADER], "commitments": data[start:]}


def sidecar_parts(data: bytes) -> dict:
    """The fields of a partial sidecar, read at their SSZ offsets."""
    bitmap, column, proofs, header, end = _offsets(data, 4)
    parts = {
        "bits": _bits(data[bitmap:column]),
        "cells": [data[i : i + CELL] for i in range(column, proofs, CELL)],
        "proofs": [data[i : i + PROOF] for i in range(proofs, header, PROOF)],
        "header": None,
    }
    if header < end:
        # A list of one header of variable size: one offset, then the header.
        parts["header"] = header_parts(data[header + 4 :])
    return parts


def _case(name: str) -> Path:
    """A vendored partial gossip case of the minimal preset."""
    return (
        GOSSIP
        / "minimal/fulu/networking/gossip_partial_data_column_sidecar/pyspec_tests"
        / f"gossip_partial_data_column_sidecar__{name}"
    )


def _read(case: Path, name: str) -> bytes:
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def test_header_inclusion_proof():
    # The first message of the case carries a valid header.
    case = _case("valid_header_only")
    data = _read(case, _yaml(case / "meta.yaml")["messages"][0]["message"])
    header = sidecar_parts(data)["header"]
    assert consensus.verify_partial_data_column_header_inclusion_proof(
        "minimal", FORKS["fulu"], header["bytes"]
    )


def test_sidecar_kzg_proofs():
    # The message carries a header and the cells of its block.
    case = _case("valid_header_and_cells")
    message = _yaml(case / "meta.yaml")["messages"][0]
    data = _read(case, message["message"])
    parts = sidecar_parts(data)
    assert sum(parts["bits"])
    assert consensus.verify_partial_data_column_sidecar_kzg_proofs(
        "minimal", FORKS["fulu"], data, parts["header"]["commitments"], message["column_index"]
    )


def test_no_partial_sidecar_after_fulu():
    with raises(SszError, "no form of this check at glamsterdam"):
        consensus.verify_partial_data_column_header_inclusion_proof("minimal", "glamsterdam", b"")
