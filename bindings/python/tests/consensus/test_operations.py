"""The block operations of EthLib against the operations vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "operations"

# The file of the operation of each handler, and the forks whose rule EthLib holds.
# Electra changes attestations and exits, Deneb the signature of exits, and Gloas attestations.
# Gloas moves the execution payload out of the block, and Heze keeps the Gloas rules.
# From Gloas the withdrawals take no payload, so their cases have no operation file.
HANDLERS = {
    "block_header": (
        "block",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "proposer_slashing": (
        "proposer_slashing",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "attester_slashing": (
        "attester_slashing",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "attestation": (
        "attestation",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "deposit": ("deposit", ("phase0", "altair", "bellatrix", "capella", "deneb", "electra")),
    "deposit_request": ("deposit_request", ("electra", "fulu", "gloas", "heze")),
    "withdrawal_request": ("withdrawal_request", ("electra", "fulu", "gloas", "heze")),
    "consolidation_request": ("consolidation_request", ("electra", "fulu", "gloas", "heze")),
    "sync_aggregate": (
        "sync_aggregate",
        ("altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "voluntary_exit": (
        "voluntary_exit",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "voluntary_exit_churn": ("voluntary_exit", ("gloas", "heze")),
    "execution_payload": ("body", ("bellatrix", "capella", "deneb", "electra", "fulu")),
    "withdrawals": ("execution_payload", ("capella", "deneb", "electra", "fulu", "gloas", "heze")),
    "bls_to_execution_change": (
        "address_change",
        ("capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "payload_attestation": ("payload_attestation", ("gloas", "heze")),
    "execution_payload_bid": ("execution_payload_bid", ("gloas", "heze")),
    "builder_deposit_request": ("builder_deposit_request", ("gloas", "heze")),
    "builder_exit_request": ("builder_exit_request", ("gloas", "heze")),
    "parent_execution_payload": ("block", ("gloas", "heze")),
}

# The release archives, and the forks whose archived cases this file runs.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}
ARCHIVE_FORKS = ("electra", "fulu", "gloas", "heze")


def runs(fork: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a handler at a fork."""
    return handler in HANDLERS and fork in HANDLERS[handler][1]


def run_case(preset: str, fork: str, handler: str, case: Path) -> None:
    """Run one case: the state after the operation, or a rejection when the case has no post."""
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    if handler == "withdrawals" and fork in ("gloas", "heze"):
        operation = b""
    else:
        operation = snappy.decompress((case / f"{HANDLERS[handler][0]}.ssz_snappy").read_bytes())
    meta_file = case / "meta.yaml"
    meta = (YAML(typ="safe").load(meta_file.read_text()) if meta_file.exists() else None) or {}
    # Setting 2 marks placeholder signatures, which the case must not check.
    setting = meta.get("bls_setting", 0)
    # The export takes the latest block header of the state as the parent block of a Gloas
    # attestation; the slot of that header starts at byte 64 of the state.
    if "parent_slot" in meta:
        assert meta["parent_slot"] == int.from_bytes(pre[64:72], "little")
    config_file = case / "config.yaml"
    config = (
        replacements(YAML(typ="safe").load(config_file.read_text()), preset)
        if config_file.exists()
        else None
    )
    # The answer of the execution layer to a payload, which the case fixes.
    execution = case / "execution.yaml"
    valid = (
        YAML(typ="safe").load(execution.read_text())["execution_valid"]
        if execution.exists()
        else True
    )
    post = case / "post.ssz_snappy"
    if post.exists():
        got = consensus.process_operation(
            preset, FORKS[fork], handler, pre, operation, setting != 2, config, valid
        )
        assert got == snappy.decompress(post.read_bytes())
    else:
        with pytest.raises(consensus.TransitionError):
            consensus.process_operation(
                preset, FORKS[fork], handler, pre, operation, setting != 2, config, valid
            )


def _cases() -> list:
    """Every vendored case, as its preset, fork, handler and directory."""
    cases = []
    for pre in sorted(FILES.rglob("pre.ssz_snappy")):
        case = pre.parent
        preset, fork, _, handler = case.relative_to(FILES).parts[:4]
        cases.append(
            pytest.param(preset, fork, handler, case, id=case.relative_to(FILES).as_posix())
        )
    return cases


def _archive_cases() -> list:
    """Every case of the archives for a handler that EthLib runs there, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [
            f"tests/{preset}/{fork}/operations/{handler}"
            for fork in ARCHIVE_FORKS
            for handler in HANDLERS
            if runs(fork, handler)
        ]
        base = archives.unpack(name, *paths) / "tests" / preset
        for path in paths:
            for pre in sorted((base / path.split("/", 2)[2]).rglob("pre.ssz_snappy")):
                case = pre.parent
                fork, _, handler = case.relative_to(base).parts[:3]
                cases.append(
                    pytest.param(
                        preset,
                        fork,
                        handler,
                        case,
                        id=f"{preset}/{case.relative_to(base).as_posix()}",
                        marks=pytest.mark.archive(name),
                    )
                )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no operations case of a handler that EthLib runs")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1
        for path in FILES.rglob("*")
        if path.is_file() and path.name not in ("SHA256SUMS", "README.md")
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, handler, case", _cases())
def test_case(preset, fork, handler, case):
    assert runs(fork, handler)
    run_case(preset, fork, handler, case)


@pytest.mark.parametrize("preset, fork, handler, case", _archive_cases())
def test_archive_case(preset, fork, handler, case):
    run_case(preset, fork, handler, case)


def test_no_deposit_from_gloas():
    # A Gloas block holds no deposit, so the operation fails before it reads the state.
    with raises(consensus.TransitionError, "no operation deposit at glamsterdam") as info:
        consensus.process_operation("minimal", "glamsterdam", "deposit", b"", b"")
    assert info.value.code == 0


def test_undecodable_state():
    with raises(
        consensus.TransitionError,
        "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 7057 0",
    ) as info:
        consensus.process_operation("minimal", "phase0", "block_header", b"", b"")
    assert info.value.code == 0


def test_payload_rejected_by_the_execution_layer():
    # A payload that every check of the beacon chain accepts fails when the execution layer says no.
    case = (
        FILES
        / "minimal"
        / "bellatrix"
        / "operations"
        / "execution_payload"
        / "pyspec_tests"
        / "success_regular_payload"
    )
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    body = snappy.decompress((case / "body.ssz_snappy").read_bytes())
    with raises(
        consensus.TransitionError, "EthLib.Consensus.TransitionError.invalidExecutionPayload"
    ) as info:
        consensus.process_operation(
            "minimal", "bellatrix", "execution_payload", pre, body, execution_valid=False
        )
    assert info.value.code == 69


def test_no_payload_before_bellatrix():
    with raises(
        consensus.TransitionError,
        "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 10229 0",
    ) as info:
        consensus.process_operation("minimal", "altair", "execution_payload", b"", b"")
    assert info.value.code == 0
