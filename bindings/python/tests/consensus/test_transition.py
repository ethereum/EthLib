"""The slots and blocks of EthLib against the sanity, finality, random and transition vectors."""

import hashlib
from pathlib import Path

import archives
import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "transition"

# The forks at which EthLib runs each group, as runner and handler.
GROUPS = {
    "sanity/slots": ("phase0", "altair", "bellatrix", "capella", "deneb"),
    "sanity/blocks": ("phase0", "altair", "bellatrix", "capella", "deneb"),
    "finality/finality": ("phase0", "altair", "bellatrix", "capella", "deneb"),
    "random/random": ("phase0", "altair", "bellatrix", "capella", "deneb"),
    # A transition case lies under the fork after its fork epoch.
    "transition/core": ("altair", "bellatrix", "capella", "deneb"),
}

# The Gloas slot cases that stay inside one epoch.
# EthLib runs only these at Gloas until the epoch transition runs there.
GLOAS_SLOTS = (
    "slots_1",
    "slots_2",
    "execution_payload_availability_reset_from_set",
    "execution_payload_availability_reset_from_unset",
)

# The release archives that hold the cases.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}


def runs(fork: str, group: str) -> bool:
    """Whether EthLib runs the cases of a group at a fork."""
    return group in GROUPS and fork in GROUPS[group]


def _load(path: Path):
    """The content of a YAML file."""
    return YAML(typ="safe").load(path.read_text())


def _fork_epochs(post_fork: str, fork_epoch: int) -> dict:
    """The fork epochs of a transition case: every fork before the post fork at 0."""
    earlier = list(FORKS)[1 : list(FORKS).index(post_fork)]
    return {f"{name.upper()}_FORK_EPOCH": 0 for name in earlier} | {
        f"{post_fork.upper()}_FORK_EPOCH": fork_epoch
    }


def run_case(preset: str, fork: str, group: str, case: Path) -> None:
    """Run one case: the state after its slots or blocks, or a rejection when it has no post."""
    state = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    config_file = case / "config.yaml"
    config = replacements(_load(config_file), preset) if config_file.exists() else None
    meta = _load(case / "meta.yaml") if (case / "meta.yaml").exists() else {}
    # Setting 2 marks placeholder signatures, which the case must not check.
    verify = meta.get("bls_setting", 0) != 2
    post = case / "post.ssz_snappy"

    def advance(state: bytes) -> bytes:
        if group == "sanity/slots":
            return consensus.process_slots(
                preset, FORKS[fork], state, int(_load(case / "slots.yaml")), config
            )
        if group == "transition/core":
            return across(state)
        for index in range(meta["blocks_count"]):
            block = snappy.decompress((case / f"blocks_{index}.ssz_snappy").read_bytes())
            state = consensus.state_transition(preset, FORKS[fork], state, block, verify, config)
        return state

    def across(state: bytes) -> bytes:
        # The state starts at the fork before the post fork, and the blocks up to the index
        # `fork_block` belong to it; with no such index, every block belongs to the post fork.
        pre_fork = list(FORKS)[list(FORKS).index(fork) - 1]
        epochs = replacements(_fork_epochs(fork, meta["fork_epoch"]), preset)
        state_fork = pre_fork
        for index in range(meta["blocks_count"]):
            block = snappy.decompress((case / f"blocks_{index}.ssz_snappy").read_bytes())
            block_fork = pre_fork if index <= meta.get("fork_block", -1) else fork
            state = consensus.state_transition_across(
                preset, FORKS[state_fork], state, FORKS[block_fork], block, verify, epochs
            )
            state_fork = block_fork
        return state

    if post.exists():
        assert advance(state) == snappy.decompress(post.read_bytes())
    else:
        with pytest.raises(consensus.TransitionError):
            advance(state)


def _cases() -> list:
    """Every vendored case, as its preset, fork, group and directory."""
    cases = []
    for pre in sorted(FILES.rglob("pre.ssz_snappy")):
        case = pre.parent
        preset, fork, runner, handler = case.relative_to(FILES).parts[:4]
        cases.append(
            pytest.param(
                preset, fork, f"{runner}/{handler}", case, id=case.relative_to(FILES).as_posix()
            )
        )
    return cases


def _archive_cases() -> list:
    """Every case of the archives for a group that EthLib runs, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [
            f"tests/{preset}/{fork}/{group}" for group, forks in GROUPS.items() for fork in forks
        ]
        base = archives.unpack(name, *paths) / "tests" / preset
        for path in paths:
            for pre in sorted((base / path.split("/", 2)[2]).rglob("pre.ssz_snappy")):
                case = pre.parent
                fork, runner, handler = case.relative_to(base).parts[:3]
                cases.append(
                    pytest.param(
                        preset,
                        fork,
                        f"{runner}/{handler}",
                        case,
                        id=f"{preset}/{case.relative_to(base).as_posix()}",
                        marks=pytest.mark.archive(name),
                    )
                )
        base = archives.unpack(name, f"tests/{preset}/gloas/sanity/slots") / "tests" / preset
        for slot_case in GLOAS_SLOTS:
            case = base / "gloas" / "sanity" / "slots" / "pyspec_tests" / slot_case
            cases.append(
                pytest.param(
                    preset,
                    "gloas",
                    "sanity/slots",
                    case,
                    id=f"{preset}/{case.relative_to(base).as_posix()}",
                    marks=pytest.mark.archive(name),
                )
            )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no sanity, finality or random case")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1 for path in FILES.rglob("*") if path.is_file() and path.name != "SHA256SUMS"
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, group, case", _cases())
def test_case(preset, fork, group, case):
    assert runs(fork, group) or (
        fork == "gloas" and group == "sanity/slots" and case.name in GLOAS_SLOTS
    )
    run_case(preset, fork, group, case)


@pytest.mark.parametrize("preset, fork, group, case", _archive_cases())
def test_archive_case(preset, fork, group, case):
    run_case(preset, fork, group, case)


def test_slots_not_after():
    # The target slot must be after the slot of the state, so zero slots is a rejection.
    case = next((FILES / "minimal" / "phase0").rglob("pre.ssz_snappy"))
    pre = snappy.decompress(case.read_bytes())
    with pytest.raises(consensus.TransitionError) as info:
        consensus.process_slots("minimal", "phase0", pre, 0)
    assert info.value.code == 53
