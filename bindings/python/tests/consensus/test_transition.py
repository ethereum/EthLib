"""The slots and blocks of EthLib against the sanity, finality, random and transition vectors."""

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

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "transition"


def _phase0_pre() -> bytes:
    case = next((FILES / "minimal" / "phase0").rglob("pre.ssz_snappy"))
    return snappy.decompress(case.read_bytes())


# The forks at which EthLib runs each group, as runner and handler.
GROUPS = {
    "sanity/slots": (
        "phase0",
        "altair",
        "bellatrix",
        "capella",
        "deneb",
        "electra",
        "fulu",
        "gloas",
        "heze",
    ),
    "sanity/blocks": (
        "phase0",
        "altair",
        "bellatrix",
        "capella",
        "deneb",
        "electra",
        "fulu",
        "gloas",
        "heze",
    ),
    "finality/finality": (
        "phase0",
        "altair",
        "bellatrix",
        "capella",
        "deneb",
        "electra",
        "fulu",
        "gloas",
        "heze",
    ),
    "random/random": (
        "phase0",
        "altair",
        "bellatrix",
        "capella",
        "deneb",
        "electra",
        "fulu",
        "gloas",
        "heze",
    ),
    # A transition case lies under the fork after its fork epoch.
    "transition/core": (
        "altair",
        "bellatrix",
        "capella",
        "deneb",
        "electra",
        "fulu",
        "gloas",
        "heze",
    ),
}

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
        return consensus.state_transitions(preset, FORKS[fork], state, blocks(), verify, config)

    def blocks() -> list[bytes]:
        return [
            snappy.decompress((case / f"blocks_{index}.ssz_snappy").read_bytes())
            for index in range(meta["blocks_count"])
        ]

    def across(state: bytes) -> bytes:
        # The state starts at the fork before the post fork.
        # The blocks up to the index `fork_block` belong to that fork.
        # With no such index, every block belongs to the post fork.
        pre_fork = list(FORKS)[list(FORKS).index(fork) - 1]
        epochs = replacements(_fork_epochs(fork, meta["fork_epoch"]), preset)
        block_forks = [
            FORKS[pre_fork if index <= meta.get("fork_block", -1) else fork]
            for index in range(meta["blocks_count"])
        ]
        return consensus.state_transitions_across(
            preset, FORKS[pre_fork], state, block_forks, blocks(), verify, epochs
        )

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
    assert runs(fork, group)
    run_case(preset, fork, group, case)


@archives.parametrize("preset, fork, group, case", _archive_cases)
def test_archive_case(preset, fork, group, case):
    run_case(preset, fork, group, case)


def test_slots_not_after():
    # The target slot must be after the slot of the state, so zero slots is a rejection.
    case = next((FILES / "minimal" / "phase0").rglob("pre.ssz_snappy"))
    pre = snappy.decompress(case.read_bytes())
    # A phase0 state starts with genesis_time (8 bytes) and genesis_validators_root (32 bytes).
    # Its slot follows, as a little-endian uint64.
    slot = int.from_bytes(pre[40:48], "little")
    with raises(
        consensus.TransitionError, f"EthLib.Consensus.TransitionError.slotNotAfter {slot} {slot}"
    ) as info:
        consensus.process_slots("minimal", "phase0", pre, 0)
    assert info.value.code == 53


def test_no_blocks():
    # With no block, the state is decoded and encoded again, so it comes back unchanged.
    case = next((FILES / "minimal" / "phase0").rglob("pre.ssz_snappy"))
    pre = snappy.decompress(case.read_bytes())
    assert consensus.state_transitions("minimal", "phase0", pre, []) == pre
    assert consensus.state_transitions_across("minimal", "phase0", pre, [], []) == pre


def test_block_forks_count():
    # Each block names its fork, so a count of forks that differs is a rejection.
    with raises(consensus.TransitionError, "1 block forks for 0 blocks") as info:
        consensus.state_transitions_across("minimal", "phase0", b"", ["phase0"], [])
    assert info.value.code == 0


def test_configuration_replacement_is_read():
    # A replacement crosses as a dict, and a value that does not fit is a rejection.
    field = "EthLib.Consensus.Config.ALTAIR_FORK_EPOCH"
    message = f"configuration: {field}: {2**64} does not fit in 64 bits"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_slots("minimal", "phase0", _phase0_pre(), 1, {"ALTAIR_FORK_EPOCH": 2**64})
    assert info.value.code == 0


def test_slots_out_of_range():
    message = f"expected an int below {2**64}, got {2**64}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_slots("minimal", "phase0", _phase0_pre(), 2**64)
    assert info.value.code == 0


def test_negative_slots():
    with raises(ValueError, "cannot pass a negative int to Lean"):
        consensus.process_slots("minimal", "phase0", _phase0_pre(), -1)


@pytest.mark.parametrize("value, message", [(True, "expected an int"), ("1", "expected an int")])
def test_slots_of_another_type(value, message):
    with raises(consensus.TransitionError, message) as info:
        consensus.process_slots("minimal", "phase0", _phase0_pre(), value)
    assert info.value.code == 0


@pytest.mark.parametrize("verify", [1, None])
def test_verify_must_be_a_bool(verify):
    with raises(consensus.TransitionError, "expected a bool") as info:
        consensus.state_transition("minimal", "phase0", _phase0_pre(), b"", verify)
    assert info.value.code == 0


def test_configuration_must_be_a_dict():
    with raises(consensus.TransitionError, "configuration: expected a dict") as info:
        consensus.process_slots("minimal", "phase0", _phase0_pre(), 1, [1])  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0


def test_genesis_hash_length():
    with raises(consensus.TransitionError, "expected 32 bytes, got 31") as info:
        consensus.initialize_genesis("minimal", "phase0", bytes(31), 0, [])
    assert info.value.code == 0
