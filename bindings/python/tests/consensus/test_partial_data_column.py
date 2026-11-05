"""The partial data column sidecars of Fulu against the vectors of consensus-specs."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import KzgError, SszError
from ethlib.networking import snappy

from .containers import FORKS

TESTS = Path(__file__).resolve().parents[4] / "tests"
FILES = TESTS / "consensus" / "data_columns"

# The bytes of a cell, of a proof, of a commitment and of a block header.
CELL = 2048
PROOF = 48
COMMITMENT = 48
HEADER = 112

# The gossip reasons of the checks that read no store, in the order of gossip validation.
EMPTY = "partial message is semantically empty"
CELL_COUNT = "number of cells does not match number of set bits"
PROOF_COUNT = "number of proofs does not match number of set bits"
PRIOR_HEADER = "header differs from previously validated header"
ROOT = "header's block root does not match group id's block root"
NO_COMMITMENTS = "header's kzg_commitments is empty"
INCLUSION = "invalid header inclusion proof"
NO_HEADER = "valid corresponding header has not been seen"
BITMAP = "bitmap length does not match commitments length"
KZG = "invalid sidecar kzg proofs"
ALONE = {
    EMPTY,
    CELL_COUNT,
    PROOF_COUNT,
    PRIOR_HEADER,
    ROOT,
    NO_COMMITMENTS,
    INCLUSION,
    NO_HEADER,
    BITMAP,
    KZG,
}

# The reasons that read the store once the header has passed, before the checks of the cells.
CELLS_STORE = {
    "corresponding header is from a future slot",
    "corresponding header is not from a slot greater than the latest finalized slot",
}

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


def check_alone(
    preset: str,
    fork: str,
    data: bytes,
    group_root: bytes,
    column: int,
    seen: dict,
    stop: str | None,
) -> str | None:
    """The reason of the first check that reads no store and fails, or none.

    The checks stop where gossip validation would stop for a reason that reads the store.
    """
    parts = sidecar_parts(data)
    count = sum(parts["bits"])
    header = parts["header"]
    if header is None and count == 0:
        return EMPTY
    if len(parts["cells"]) != count:
        return CELL_COUNT
    if len(parts["proofs"]) != count:
        return PROOF_COUNT
    if header is not None:
        prior = seen.get(group_root)
        if prior is not None and prior["bytes"] != header["bytes"]:
            return PRIOR_HEADER
        root, _ = consensus.ssz_static(preset, fork, "BeaconBlockHeader", header["message"])
        if root != group_root:
            return ROOT
        if not header["commitments"]:
            return NO_COMMITMENTS
        if stop is not None and stop not in ALONE and stop not in CELLS_STORE:
            # Gossip validation stops at a check of the header that reads the store.
            return None
        if not consensus.verify_partial_data_column_header_inclusion_proof(
            preset, fork, header["bytes"]
        ):
            return INCLUSION
        seen[group_root] = header
    if count:
        known = seen.get(group_root)
        if known is None:
            return NO_HEADER
        if stop in CELLS_STORE:
            return None
        commitments = known["commitments"]
        if len(parts["bits"]) != len(commitments) // COMMITMENT:
            return BITMAP
        try:
            valid = consensus.verify_partial_data_column_sidecar_kzg_proofs(
                preset, fork, data, commitments, column
            )
        except KzgError:
            valid = False
        if not valid:
            return KZG
    return None


def run_partial_gossip_case(case: Path, preset: str) -> None:
    """Run the checks of each message of a partial gossip case that read no store.

    A message rejected or ignored for one of them fails it first.
    Every other message passes those that gossip validation reaches.
    """
    fork = FORKS[case.parts[-5]]
    meta = _yaml(case / "meta.yaml")
    # A case may start with headers that the node has already validated.
    seen = {
        bytes.fromhex(entry["block_root"][2:]): header_parts(
            snappy.decompress((case / f"{entry['header']}.ssz_snappy").read_bytes())
        )
        for entry in meta.get("seen_partial_data_column_headers", [])
    }
    for message in meta["messages"]:
        data = snappy.decompress((case / f"{message['message']}.ssz_snappy").read_bytes())
        group = snappy.decompress((case / f"{message['group_id']}.ssz_snappy").read_bytes())
        reason = message.get("reason")
        failing = check_alone(preset, fork, data, group, message["column_index"], seen, reason)
        if reason in ALONE:
            assert failing == reason, (message, failing)
        else:
            assert failing is None, (message, failing)


def _cases() -> list:
    return [
        pytest.param(case.parts[-6], case, id=f"{case.parts[-6]}-{case.name}")
        for case in sorted(FILES.glob("*/fulu/networking/gossip_partial_data_column_sidecar/*/*"))
    ]


@pytest.mark.parametrize("preset, case", _cases())
def test_partial_gossip_checks(preset, case):
    run_partial_gossip_case(case, preset)


def test_no_partial_sidecar_after_fulu():
    with pytest.raises(SszError):
        consensus.verify_partial_data_column_header_inclusion_proof("minimal", "glamsterdam", b"")
