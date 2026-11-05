"""The steps of the epoch transition of EthLib against the epoch_processing vectors."""

import hashlib
from pathlib import Path

import archives
import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "epoch_processing"

# The forks at which EthLib runs each handler.
HANDLERS = {
    "justification_and_finalization": ("phase0", "altair", "bellatrix", "capella", "deneb",
                                       "electra", "fulu", "gloas"),
    "inactivity_updates": ("altair", "bellatrix", "capella", "deneb", "electra", "fulu",
                           "gloas"),
    "rewards_and_penalties": ("phase0", "altair", "bellatrix", "capella", "deneb", "electra",
                              "fulu", "gloas"),
    "registry_updates": ("phase0", "altair", "bellatrix", "capella"),
    "slashings": ("phase0", "altair", "bellatrix", "capella", "deneb"),
    "eth1_data_reset": ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu",
                        "gloas"),
    "effective_balance_updates": ("phase0", "altair", "bellatrix", "capella", "deneb"),
    "slashings_reset": ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu",
                        "gloas"),
    "randao_mixes_reset": ("phase0", "altair", "bellatrix", "capella", "deneb", "electra",
                           "fulu", "gloas"),
    "historical_roots_update": ("phase0", "altair", "bellatrix"),
    "historical_summaries_update": ("capella", "deneb", "electra", "fulu", "gloas"),
    "participation_record_updates": ("phase0",),
    "participation_flag_updates": ("altair", "bellatrix", "capella", "deneb", "electra", "fulu",
                                   "gloas"),
    "sync_committee_updates": ("altair", "bellatrix", "capella", "deneb", "electra", "fulu",
                               "gloas"),
    "ptc_window": ("gloas",),
    "builder_pending_payments": ("gloas",),
    "proposer_lookahead": ("fulu", "gloas"),
}

# A mainnet sync committee period is 256 epochs, so the release has no mainnet case of its update.
MINIMAL_ONLY = {"sync_committee_updates"}

# The release archives that hold the cases.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}


def runs(fork: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a handler at a fork."""
    return handler in HANDLERS and fork in HANDLERS[handler]


def run_case(preset: str, fork: str, handler: str, case) -> None:
    """Run one case: the state after the step, or a rejection when the case has no post."""
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    config_file = case / "config.yaml"
    config = (replacements(YAML(typ="safe").load(config_file.read_text()), preset)
              if config_file.exists() else None)
    post = case / "post.ssz_snappy"
    if post.exists():
        got = consensus.process_epoch(preset, FORKS[fork], handler, pre, config)
        assert got == snappy.decompress(post.read_bytes())
    else:
        with pytest.raises(consensus.TransitionError):
            consensus.process_epoch(preset, FORKS[fork], handler, pre, config)


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
    """Every case of the archives for a handler that EthLib runs, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [f"tests/{preset}/{fork}/epoch_processing/{handler}"
                 for handler, forks in HANDLERS.items() for fork in forks
                 if preset == "minimal" or handler not in MINIMAL_ONLY]
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
        raise LookupError("the archives hold no epoch_processing case that EthLib runs")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for path in FILES.rglob("*") if path.is_file()
                               and path.name != "SHA256SUMS")
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, handler, case", _cases())
def test_case(preset, fork, handler, case):
    assert runs(fork, handler)
    run_case(preset, fork, handler, case)


@pytest.mark.parametrize("preset, fork, handler, case", _archive_cases())
def test_archive_case(preset, fork, handler, case):
    run_case(preset, fork, handler, case)


def test_step_before_gloas():
    # Before Gloas, the state has no window of payload committees.
    with pytest.raises(consensus.TransitionError) as info:
        consensus.process_epoch("minimal", "fusaka", "ptc_window", b"")
    assert info.value.code == 0


def test_unknown_step():
    with pytest.raises(consensus.TransitionError) as info:
        consensus.process_epoch("minimal", "glamsterdam", "no_such_step", b"")
    assert info.value.code == 0
