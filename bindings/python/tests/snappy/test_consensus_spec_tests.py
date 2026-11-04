"""Snappy blocks against 50 ssz_snappy files of consensus-spec-tests."""

# The size and sha256 of the data of each file come from cramjam 2.11.0, an independent Snappy
# implementation, run once with `cramjam.snappy.decompress_raw`.
# `tests/consensus/snappy/README.md` gives the origin of the files and how they were chosen.

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.networking import snappy

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "snappy"
CASES = json.loads((Path(__file__).resolve().parent / "consensus_spec_tests.json").read_text())


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert sorted(name for _, name in entries) == sorted(case["file"] for case in CASES)
    assert len(entries) == sum(1 for _ in FILES.rglob("*.ssz_snappy")) == 50
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("case", CASES, ids=[case["file"] for case in CASES])
def test_decompress(case: dict) -> None:
    data = snappy.decompress((FILES / case["file"]).read_bytes())
    assert len(data) == case["size"]
    assert hashlib.sha256(data).hexdigest() == case["sha256"]
