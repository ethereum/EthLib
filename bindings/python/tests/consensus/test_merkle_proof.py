"""The Merkle proofs of beacon block bodies against the merkle_proof vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy

from .containers import FORKS

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "merkle_proof"

# The bytes of a blob.
BYTES_PER_BLOB = 4096 * 32


def _cases() -> list:
    """Every vendored case, as its preset, fork and directory."""
    cases = []
    for proof in sorted(FILES.rglob("proof.yaml")):
        case = proof.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


def _read(case: Path) -> tuple:
    proof = YAML(typ="safe").load((case / "proof.yaml").read_text())
    body = snappy.decompress((case / "object.ssz_snappy").read_bytes())
    leaf = bytes.fromhex(proof["leaf"][2:])
    branch = [bytes.fromhex(node[2:]) for node in proof["branch"]]
    return body, proof["leaf_index"], leaf, branch


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*") if path.is_file()
                               and path.name != "SHA256SUMS")
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def run_case(preset: str, fork: str, case: Path) -> None:
    """Check the leaf and branch of one case against those that EthLib builds."""
    body, gindex, leaf, branch = _read(case)
    node, siblings = consensus.merkle_proof(preset, FORKS[fork], "BeaconBlockBody", body, gindex)
    assert node == leaf
    assert siblings == branch


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_case(preset, fork, case):
    run_case(preset, fork, case)


def _sidecar(preset: str, fork: str, case: Path) -> tuple:
    """A blob sidecar for the commitment that a case proves, and its branch."""
    body, gindex, _, branch = _read(case)
    lean = FORKS[fork]
    # A commitment is 48 bytes, so it fills the two nodes below its leaf: 32 bytes, then 16.
    first, _ = consensus.merkle_proof(preset, lean, "BeaconBlockBody", body, 2 * gindex)
    second, _ = consensus.merkle_proof(preset, lean, "BeaconBlockBody", body, 2 * gindex + 1)
    commitment = first + second[:16]
    limit = consensus.preset(preset)["MAX_BLOB_COMMITMENTS_PER_BLOCK"]
    index = gindex % limit
    body_root, _ = consensus.ssz_static(preset, lean, "BeaconBlockBody", body)
    header = bytes(8 + 8 + 32 + 32) + body_root + bytes(96)
    head = index.to_bytes(8, "little") + bytes(BYTES_PER_BLOB) + commitment + bytes(48) + header
    return head, b"".join(branch)


BLOB_CASES = [case for case in _cases() if case.values[1] in ("deneb", "electra")]


@pytest.mark.parametrize("preset, fork, case", BLOB_CASES)
def test_blob_sidecar_inclusion_proof(preset, fork, case):
    head, branch = _sidecar(preset, fork, case)
    assert consensus.verify_blob_sidecar_inclusion_proof(preset, FORKS[fork], head + branch)
    # One flipped bit of the branch climbs to another root.
    broken = bytes([branch[0] ^ 1]) + branch[1:]
    assert not consensus.verify_blob_sidecar_inclusion_proof(preset, FORKS[fork], head + broken)


def test_no_blob_sidecar_at_fulu():
    with pytest.raises(SszError):
        consensus.verify_blob_sidecar_inclusion_proof("minimal", "fusaka", b"")
