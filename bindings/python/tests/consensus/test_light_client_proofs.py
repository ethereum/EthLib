"""Light client Merkle proofs against the single_merkle_proof vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "light_client"

# The cases of the release, one for each node that a light client proves.
CASE_NAMES = {
    "current_sync_committee_merkle_proof",
    "next_sync_committee_merkle_proof",
    "finality_root_merkle_proof",
    "execution_merkle_proof",
    "execution_block_hash_merkle_proof",
}

# The forks that have a light client.
SPECIFIED = ["altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"]


def _cases(base: Path) -> list:
    """Every case under a `tests` directory, as its preset, fork, container and directory."""
    cases = []
    for proof in sorted(base.rglob("light_client/single_merkle_proof/*/*/proof.yaml")):
        case = proof.parent
        preset, fork = case.relative_to(base).parts[:2]
        if fork in SPECIFIED:
            cases.append((preset, fork, case.parent.name, case))
    return cases


def _check(preset: str, fork: str, container: str, case: Path) -> None:
    """Prove the node of a case in Lean, then compare the leaf and the branch."""
    data = snappy.decompress((case / "object.ssz_snappy").read_bytes())
    proof = YAML(typ="safe").load((case / "proof.yaml").read_text())
    gindex = proof["leaf_index"]
    leaf, branch = consensus.merkle_proof(preset, FORKS[fork], container, data, gindex)
    assert "0x" + leaf.hex() == proof["leaf"]
    assert ["0x" + node.hex() for node in branch] == proof["branch"]
    # The branch climbs from the leaf to the root of the value, as is_valid_merkle_branch reads it.
    node = leaf
    for depth, sibling in enumerate(branch):
        pair = sibling + node if (gindex >> depth) & 1 else node + sibling
        node = hashlib.sha256(pair).digest()
    assert node == consensus.ssz_static(preset, FORKS[fork], container, data)[0]


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1 for path in FILES.rglob("*") if path.name != "SHA256SUMS" and path.is_file()
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_every_case_is_a_known_case():
    assert {case.name for _, _, _, case in _cases(FILES)} == CASE_NAMES


def test_every_preset_and_fork_has_cases():
    found = {(preset, fork) for preset, fork, _, _ in _cases(FILES)}
    assert found == {(preset, fork) for preset in ("minimal", "mainnet") for fork in SPECIFIED}


@pytest.mark.parametrize(
    "preset, fork, container, case",
    _cases(FILES),
    ids=lambda value: value.relative_to(FILES).as_posix() if isinstance(value, Path) else None,
)
def test_case(preset, fork, container, case):
    _check(preset, fork, container, case)


# The release archives that hold every case, one for each preset.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}


def _unpack(preset: str) -> Path:
    """The `tests` directory of the archive of a preset, with its light client proofs."""
    paths = [f"tests/{preset}/{fork}/light_client/single_merkle_proof" for fork in SPECIFIED]
    return archives.unpack(ARCHIVES[preset], *paths) / "tests"


def _archive_cases() -> list:
    """Every case of the archives at a specified fork, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        base = _unpack(preset)
        for preset_, fork, container, case in _cases(base):
            cases.append(
                pytest.param(
                    preset_,
                    fork,
                    container,
                    case,
                    id=case.relative_to(base).as_posix(),
                    marks=pytest.mark.archive(name),
                )
            )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no single_merkle_proof case")
    return cases


@archives.parametrize("preset, fork, container, case", _archive_cases)
def test_archive_case(preset, fork, container, case):
    _check(preset, fork, container, case)


@pytest.mark.parametrize(
    "preset",
    [pytest.param(preset, marks=pytest.mark.archive(name)) for preset, name in ARCHIVES.items()],
)
def test_vendored_cases_are_copies(preset):
    # Each vendored file is the file of the release, byte for byte.
    base = _unpack(preset)
    vendored = [path for path in (FILES / preset).rglob("*") if path.is_file()]
    assert vendored
    for path in vendored:
        assert path.read_bytes() == (base / path.relative_to(FILES)).read_bytes(), path
