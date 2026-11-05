"""The fork choice of EthLib against the fork choice vectors."""

import hashlib
from pathlib import Path

import archives
import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.cryptography.kzg import BYTES_PER_BLOB
from ethlib.networking import snappy

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork_choice"

# The handlers that EthLib runs, and the forks at which it runs them.
HANDLERS = (
    "ex_ante",
    "get_head",
    "get_proposer_head",
    "on_block",
    "on_merge_block",
    "reorg",
    "withholding",
)
SPECIFIED = ("altair", "bellatrix", "capella", "deneb")

# The Fulu cases that judge the columns of a block, which EthLib checks before the state
# transition; that transition does not yet take a Fulu block.
COLUMN_CASES = "on_block_peerdas__"

# The codes of the errors that the data check raises: a bad KZG input, missing columns and
# invalid columns.
_DATA_CODES = (30, 32, 33)

# The code of a rejection by the state transition.
_TRANSITION_CODE = 10

# The release archives that hold the cases.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}

# The step of each file kind of a case, as the export names it.
_FILE_STEPS = ("block", "attestation", "attester_slashing", "pow_block")

_YAML = YAML(typ="safe")


def runs(fork: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a handler at a fork."""
    return fork in SPECIFIED and handler in HANDLERS


def checks_columns(fork: str, case: Path) -> bool:
    """Whether EthLib runs a Fulu case only up to the check of the columns of its block."""
    return fork == "fulu" and fork not in SPECIFIED and case.name.startswith(COLUMN_CASES)


def _load(path: Path):
    """The content of a YAML file."""
    return _YAML.load(path.read_text())


def _read(case: Path, name: str) -> bytes:
    """The bytes of an SSZ file of a case, without the Snappy framing."""
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def _input(case: Path, step: dict) -> tuple:
    """The step that the export runs for a step of a case."""
    if "tick" in step:
        return "tick", step["tick"]
    if "checks" in step:
        return "checks", "get_proposer_head" in step["checks"]
    if "columns" in step:
        return "block", (
            _read(case, step["block"]),
            [_read(case, name) for name in step["columns"]],
        )
    if "blobs" in step:
        # The file holds the blobs one after another.
        data = _read(case, step["blobs"])
        blobs = [data[i : i + BYTES_PER_BLOB] for i in range(0, len(data), BYTES_PER_BLOB)]
        proofs = [_hex(proof) for proof in step.get("proofs", [])]
        return "block", (_read(case, step["block"]), blobs, proofs)
    for kind in _FILE_STEPS:
        if kind in step:
            return kind, _read(case, step[kind])
    raise ValueError(f"no runner for the step {step}")


def _check(read: dict, checks: dict) -> None:
    """Compare a read of the store with each check of a step."""
    for key, want in checks.items():
        match key:
            case "head":
                assert read["head"]["slot"] == want["slot"]
                assert read["head"]["root"] == _hex(want["root"])
            case "time":
                assert read["time_ms"] // 1000 == want
            case "genesis_time":
                assert read["genesis_time_ms"] // 1000 == want
            case "justified_checkpoint" | "finalized_checkpoint":
                assert read[key]["epoch"] == want["epoch"]
                assert read[key]["root"] == _hex(want["root"])
            case "proposer_boost_root":
                assert read["proposer_boost_root"] == _hex(want)
            case "get_proposer_head":
                assert read["proposer_head"] == _hex(want)
            case _:
                raise ValueError(f"no runner for the check {key}")


def run_case(preset: str, fork: str, case: Path) -> None:
    """Run every step of a case on one store, and compare each outcome with the case."""
    steps = _load(case / "steps.yaml")
    config_file = case / "config.yaml"
    config = replacements(_load(config_file), preset) if config_file.exists() else None
    meta = _load(case / "meta.yaml") if (case / "meta.yaml").exists() else {}
    # Setting 2 marks placeholder signatures, which the case must not check.
    verify = (meta or {}).get("bls_setting", 0) != 2
    outcomes = consensus.fork_choice(
        preset,
        FORKS[fork],
        _read(case, "anchor_state"),
        _read(case, "anchor_block"),
        [_input(case, step) for step in steps],
        verify,
        config,
    )
    for index, (step, outcome) in enumerate(zip(steps, outcomes, strict=True)):
        if "checks" in step:
            assert isinstance(outcome, dict), (index, outcome)
            _check(outcome, step["checks"])
        elif not checks_columns(fork, case):
            assert (outcome is None) == step.get("valid", True), (index, step, outcome)
        elif step.get("valid", True):
            # The columns pass, so only the state transition may reject the block.
            assert outcome is None or outcome.code == _TRANSITION_CODE, (index, step, outcome)
            if outcome is not None:
                # Later steps need the block that the transition rejects.
                break
        else:
            assert outcome is not None and outcome.code in _DATA_CODES, (index, step, outcome)


def _cases() -> list:
    """Every vendored case, as its preset, fork and directory."""
    cases = []
    for steps in sorted(FILES.rglob("steps.yaml")):
        case = steps.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


def _archive_cases() -> list:
    """Every case of the archives for a handler that EthLib runs, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [f"tests/{preset}/{fork}/fork_choice" for fork in (*SPECIFIED, "fulu")]
        base = archives.unpack(name, *paths) / "tests" / preset
        for steps in sorted(base.glob("*/fork_choice/*/*/*/steps.yaml")):
            case = steps.parent
            fork, _, handler = case.relative_to(base).parts[:3]
            if runs(fork, handler) or checks_columns(fork, case):
                cases.append(
                    pytest.param(
                        preset,
                        fork,
                        case,
                        id=f"{preset}/{case.relative_to(base).as_posix()}",
                        marks=pytest.mark.archive(name),
                    )
                )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no fork choice case")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1 for path in FILES.rglob("*") if path.is_file() and path.name != "SHA256SUMS"
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, case", _cases())
def test_case(preset, fork, case):
    assert runs(fork, case.parts[-3]) or checks_columns(fork, case)
    run_case(preset, fork, case)


@pytest.mark.parametrize("preset, fork, case", _archive_cases())
def test_archive_case(preset, fork, case):
    run_case(preset, fork, case)


def test_anchor_state_mismatch():
    # The anchor block must commit to the anchor state; its state root sits at bytes 48 to 80.
    case = next((FILES / "minimal" / "altair").rglob("steps.yaml")).parent
    block = bytearray(_read(case, "anchor_block"))
    block[48] ^= 1
    with pytest.raises(consensus.ForkChoiceError) as info:
        consensus.fork_choice("minimal", "altair", _read(case, "anchor_state"), bytes(block), [])
    assert info.value.code == 1
