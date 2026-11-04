"""The beacon containers of EthLib against the ssz_static vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "ssz_static"

# Each fork of the beacon chain up to Fulu, as consensus-specs names it, with its name in Lean.
FORKS = {
    "phase0": "phase0",
    "altair": "altair",
    "bellatrix": "bellatrix",
    "capella": "shapella",
    "deneb": "dencun",
    "electra": "pectra",
    "fulu": "fusaka",
}

# Each container that EthLib defines, with the first fork that has it and the first that drops it.
CONTAINERS = {
    "Fork": ("phase0", None),
    "ForkData": ("phase0", None),
    "SigningData": ("phase0", None),
    "Checkpoint": ("phase0", None),
    "Validator": ("phase0", None),
    "AttestationData": ("phase0", None),
    "PendingAttestation": ("phase0", "altair"),
    "Eth1Data": ("phase0", None),
    "HistoricalBatch": ("phase0", "capella"),
    "DepositMessage": ("phase0", None),
    "DepositData": ("phase0", None),
    "BeaconBlockHeader": ("phase0", None),
    "SignedBeaconBlockHeader": ("phase0", None),
    "Eth1Block": ("phase0", None),
    "ProposerSlashing": ("phase0", None),
    "Deposit": ("phase0", None),
    "VoluntaryExit": ("phase0", None),
    "SignedVoluntaryExit": ("phase0", None),
    "Attestation": ("phase0", None),
    "IndexedAttestation": ("phase0", None),
    "AttesterSlashing": ("phase0", None),
    "AggregateAndProof": ("phase0", None),
    "SignedAggregateAndProof": ("phase0", None),
    "SingleAttestation": ("electra", None),
    "SyncCommittee": ("altair", None),
    "SyncAggregate": ("altair", None),
    "SyncCommitteeMessage": ("altair", None),
    "SyncCommitteeContribution": ("altair", None),
    "ContributionAndProof": ("altair", None),
    "SignedContributionAndProof": ("altair", None),
    "SyncAggregatorSelectionData": ("altair", None),
    "HistoricalSummary": ("capella", None),
    "BLSToExecutionChange": ("capella", None),
    "SignedBLSToExecutionChange": ("capella", None),
    "PendingDeposit": ("electra", None),
    "PendingPartialWithdrawal": ("electra", None),
    "PendingConsolidation": ("electra", None),
    "DepositRequest": ("electra", None),
    "WithdrawalRequest": ("electra", None),
    "ConsolidationRequest": ("electra", None),
    "ExecutionRequests": ("electra", None),
    "Withdrawal": ("capella", None),
    "ExecutionPayload": ("bellatrix", None),
}


def _cases() -> list:
    """Every vendored case, as its preset, fork, container and directory."""
    cases = []
    for roots in sorted(FILES.rglob("roots.yaml")):
        case = roots.parent
        preset, fork, _, container = case.relative_to(FILES).parts[:4]
        cases.append((preset, fork, container, case))
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*") if path.name != "SHA256SUMS"
                               and path.is_file())
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


def test_every_case_is_a_known_container():
    assert {container for _, _, container, _ in _cases()} == set(CONTAINERS)


@pytest.mark.parametrize(
    "preset, fork, container, case", _cases(),
    ids=lambda value: value.relative_to(FILES).as_posix() if isinstance(value, Path) else None,
)
def test_case(preset, fork, container, case):
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    root = YAML(typ="safe").load((case / "roots.yaml").read_text())["root"]
    got_root, encoded = consensus.ssz_static(preset, FORKS[fork], container, data)
    assert "0x" + got_root.hex() == root
    assert encoded == data


@pytest.mark.parametrize("container", CONTAINERS)
def test_no_container_outside_its_forks(container):
    first, dropped = CONTAINERS[container]
    forks = list(FORKS)
    end = forks.index(dropped) if dropped else len(forks)
    for fork in forks[:forks.index(first)] + forks[end:]:
        with pytest.raises(SszError):
            consensus.ssz_static("minimal", FORKS[fork], container, b"")


def test_every_fork_of_a_container_has_cases():
    found = {(fork, container) for _, fork, container, _ in _cases()}
    forks = list(FORKS)
    for container, (first, dropped) in CONTAINERS.items():
        end = forks.index(dropped) if dropped else len(forks)
        for fork in forks[forks.index(first):end]:
            assert (fork, container) in found, (fork, container)


def test_truncated_bytes_are_rejected():
    # A withdrawal has a fixed size, so one byte less encodes no withdrawal.
    preset, fork, container, case = next(c for c in _cases() if c[2] == "Withdrawal")
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    with pytest.raises(SszError):
        consensus.ssz_static(preset, FORKS[fork], container, data[:-1])


def test_unknown_container():
    with pytest.raises(SszError):
        consensus.ssz_static("minimal", "fusaka", "NoSuchContainer", b"")
