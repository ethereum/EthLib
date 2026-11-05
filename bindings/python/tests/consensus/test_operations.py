"""The block operations of EthLib against the operations vectors of consensus-specs."""

import hashlib
from pathlib import Path

import archives
import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "operations"

# The file of the operation of each handler, and the forks whose rule EthLib holds.
# Gloas also cancels the builder payments of a slashed proposer, which EthLib does not hold yet,
# so the slashings stop at Fulu.
HANDLERS = {
    "block_header": ("block", ("phase0", "altair", "bellatrix", "capella", "deneb", "electra",
                               "fulu")),
    "proposer_slashing": ("proposer_slashing",
                          ("phase0", "altair", "bellatrix", "capella", "deneb", "electra",
                           "fulu")),
    "attester_slashing": ("attester_slashing",
                          ("phase0", "altair", "bellatrix", "capella", "deneb", "electra",
                           "fulu")),
    "payload_attestation": ("payload_attestation", ("gloas",)),
    "execution_payload_bid": ("execution_payload_bid", ("gloas",)),
    "builder_deposit_request": ("builder_deposit_request", ("gloas",)),
    "builder_exit_request": ("builder_exit_request", ("gloas",)),
}

# The release archives, and the forks whose archived cases this file runs.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}
ARCHIVE_FORKS = ("gloas",)


def runs(fork: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a handler at a fork."""
    return handler in HANDLERS and fork in HANDLERS[handler][1]


def run_case(preset: str, fork: str, handler: str, case: Path) -> None:
    """Run one case: the state after the operation, or a rejection when the case has no post."""
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    operation = snappy.decompress((case / f"{HANDLERS[handler][0]}.ssz_snappy").read_bytes())
    meta = case / "meta.yaml"
    # Setting 2 marks placeholder signatures, which the case must not check.
    setting = YAML(typ="safe").load(meta.read_text()).get("bls_setting", 0) if meta.exists() else 0
    config_file = case / "config.yaml"
    config = (replacements(YAML(typ="safe").load(config_file.read_text()), preset)
              if config_file.exists() else None)
    post = case / "post.ssz_snappy"
    if post.exists():
        got = consensus.process_operation(preset, FORKS[fork], handler, pre, operation,
                                          setting != 2, config)
        assert got == snappy.decompress(post.read_bytes())
    else:
        with pytest.raises(consensus.TransitionError):
            consensus.process_operation(preset, FORKS[fork], handler, pre, operation, setting != 2,
                                        config)


def _cases() -> list:
    """Every vendored case, as its preset, fork, handler and directory."""
    cases = []
    for pre in sorted(FILES.rglob("pre.ssz_snappy")):
        case = pre.parent
        preset, fork, _, handler = case.relative_to(FILES).parts[:4]
        cases.append(pytest.param(preset, fork, handler, case,
                                  id=case.relative_to(FILES).as_posix()))
    return cases


def _archive_cases() -> list:
    """Every case of the archives for a handler that EthLib runs there, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [f"tests/{preset}/{fork}/operations/{handler}"
                 for fork in ARCHIVE_FORKS for handler in HANDLERS if runs(fork, handler)]
        base = archives.unpack(name, *paths) / "tests" / preset
        for path in paths:
            for pre in sorted((base / path.split("/", 2)[2]).rglob("pre.ssz_snappy")):
                case = pre.parent
                fork, _, handler = case.relative_to(base).parts[:3]
                cases.append(pytest.param(preset, fork, handler, case,
                                          id=f"{preset}/{case.relative_to(base).as_posix()}",
                                          marks=pytest.mark.archive(name)))
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no operations case of a handler that EthLib runs")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*") if path.is_file()
                               and path.name not in ("SHA256SUMS", "README.md"))
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, handler, case", _cases())
def test_case(preset, fork, handler, case):
    assert runs(fork, handler)
    run_case(preset, fork, handler, case)


@pytest.mark.parametrize("preset, fork, handler, case", _archive_cases())
def test_archive_case(preset, fork, handler, case):
    run_case(preset, fork, handler, case)


def test_operation_not_yet_specified_at_gloas():
    # At Gloas, an operation whose Gloas rule EthLib does not hold fails before it reads the state.
    with pytest.raises(consensus.TransitionError) as info:
        consensus.process_operation("minimal", "glamsterdam", "block_header", b"", b"")
    assert info.value.code == 0
    assert "not yet specified" in str(info.value)


def test_undecodable_state():
    with pytest.raises(consensus.TransitionError) as info:
        consensus.process_operation("minimal", "phase0", "block_header", b"", b"")
    assert info.value.code == 0
