"""The fork choice of EthLib against the fork choice vectors."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib import consensus
from ethlib.cryptography.kzg import BYTES_PER_BLOB
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork_choice"

# The handlers that EthLib runs, and the forks at which it runs them.
HANDLERS = (
    "deposit_with_reorg",
    "ex_ante",
    "get_head",
    "get_proposer_head",
    "on_block",
    "on_merge_block",
    "optimistic",
    "reorg",
    "withholding",
)
# The handlers whose cases start at Gloas.
GLOAS_HANDLERS = (
    "filter_node_tree_variants",
    "get_parent_payload_status",
    "on_attestation",
    "on_execution_payload_envelope",
    "on_payload_attestation_message",
    "payload_data_availability",
    "payload_timeliness",
    "should_apply_proposer_boost",
)
SPECIFIED = ("altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze")

# The suites of the fast confirmation cases, which EthLib runs at every fork above.
FAST_CONFIRMATION = (
    "basic",
    "current_epoch",
    "empty_slots",
    "ffg",
    "is_one_confirmed",
    "previous_epoch",
    "reconfirmation",
    "restart_gu",
    "revert_finality",
    "variables",
)

# The checks that read the store of the fast confirmation rule.
# A checks step with them follows a run of that rule.
# The case leaves that run implicit at the start of each slot.
FAST_CONFIRMATION_CHECKS = (
    "previous_epoch_observed_justified_checkpoint",
    "current_epoch_observed_justified_checkpoint",
    "previous_epoch_greatest_unrealized_checkpoint",
    "previous_slot_head",
    "current_slot_head",
    "confirmed_root",
    "safe_execution_block_hash",
)

# The release archives that hold the cases.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}

# The step of each file kind of a case, as the export names it.
_FILE_STEPS = (
    "block",
    "attestation",
    "attester_slashing",
    "pow_block",
    "execution_payload",
    "payload_attestation_message",
)

_YAML = YAML(typ="safe")


def runs(fork: str, runner: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a handler at a fork."""
    if runner == "fast_confirmation":
        return fork in SPECIFIED and handler in FAST_CONFIRMATION
    return fork in SPECIFIED and handler in HANDLERS + GLOAS_HANDLERS


def _load(path: Path):
    """The content of a YAML file."""
    return _YAML.load(path.read_text())


def _read(case: Path, name: str) -> bytes:
    """The bytes of an SSZ file of a case, without the Snappy framing."""
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def _inputs(case: Path, step: dict) -> list:
    """The steps that the export runs for a step of a case."""
    if "checks" in step and FAST_CONFIRMATION_CHECKS[0] in step["checks"]:
        return [("fast_confirmation", None), _input(case, step)]
    return [_input(case, step)]


def _input(case: Path, step: dict) -> tuple:
    """The step that the export runs for a step of a case."""
    if "tick" in step:
        return "tick", step["tick"]
    if "checks" in step:
        checks = step["checks"]
        votes = checks.get("payload_timeliness_vote")
        root = votes and _hex(votes["block_root"])
        return "checks", (
            "get_proposer_head" in checks,
            "viable_for_head_roots_and_weights" in checks,
            root,
        )
    if "payload_status" in step:
        status = step["payload_status"]
        latest_valid_hash = status["latest_valid_hash"]
        return "payload", (status["status"], latest_valid_hash and _hex(latest_valid_hash))
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
                if "payload_status" in want:
                    assert read["head"]["payload_status"] == want["payload_status"]
            case "viable_for_head_roots_and_weights":
                # The order of the leaves depends on the walk, so the sets are compared.
                found = [(e["root"], e["weight"], e["payload_status"]) for e in read[key]]
                wanted = [(_hex(e["root"]), e["weight"], e["payload_status"]) for e in want]
                assert sorted(found) == sorted(wanted)
            case "payload_timeliness_vote" | "payload_data_availability_vote":
                # The read asks for the votes on the block of the timeliness check.
                asked = checks["payload_timeliness_vote"]["block_root"]
                assert want["block_root"] == asked
                assert read[key] == want["votes"]
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
            case (
                "previous_epoch_observed_justified_checkpoint"
                | "current_epoch_observed_justified_checkpoint"
                | "previous_epoch_greatest_unrealized_checkpoint"
            ):
                assert read[key]["epoch"] == want["epoch"]
                assert read[key]["root"] == _hex(want["root"])
            case (
                "previous_slot_head"
                | "current_slot_head"
                | "confirmed_root"
                | "safe_execution_block_hash"
            ):
                assert read[key] == _hex(want)
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
    inputs = [_inputs(case, step) for step in steps]
    outcomes = iter(
        consensus.fork_choice(
            preset,
            FORKS[fork],
            _read(case, "anchor_state"),
            _read(case, "anchor_block"),
            [one for step in inputs for one in step],
            verify,
            config,
        )
    )
    for index, step in enumerate(steps):
        # A fast confirmation and the read after it make one checks step.
        reads = [next(outcomes) for _ in inputs[index]]
        outcome = reads[0] if len(reads) == 1 else reads[0] | reads[1]
        if "checks" in step:
            assert all(isinstance(read, dict) for read in reads), (index, reads)
            _check(outcome, step["checks"])
        else:
            assert (outcome is None) == step.get("valid", True), (index, step, outcome)
    assert next(outcomes, None) is None


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
    disagreements = archives.disagreements("consensus-spec-tests")
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [f"tests/{preset}/{fork}/fork_choice" for fork in SPECIFIED]
        # The optimistic sync cases run from Bellatrix to Fulu.
        sync = [fork for fork in SPECIFIED if fork not in ("altair", "gloas", "heze")]
        paths += [f"tests/{preset}/{fork}/sync" for fork in sync]
        # The fast confirmation cases are minimal only.
        if preset == "minimal":
            paths += [f"tests/{preset}/{fork}/fast_confirmation" for fork in SPECIFIED]
        base = archives.unpack(name, *paths) / "tests" / preset
        found = [
            *base.glob("*/fork_choice/*/*/*/steps.yaml"),
            *base.glob("*/sync/*/*/*/steps.yaml"),
            *base.glob("*/fast_confirmation/*/*/*/steps.yaml"),
        ]
        for steps in sorted(found):
            case = steps.parent
            fork, runner, handler = case.relative_to(base).parts[:3]
            if runs(fork, runner, handler):
                path = f"{preset}/{case.relative_to(base).as_posix()}"
                marks = [pytest.mark.archive(name)]
                # A case on which EthLib knowingly disagrees must fail.
                key = f"tests/{path}"
                listed = disagreements.get((key, f"{runner}/{handler}")) or disagreements.get(
                    (key, None)
                )
                if listed is not None:
                    marks.append(
                        pytest.mark.xfail(
                            strict=True, raises=AssertionError, reason=listed["reason"]
                        )
                    )
                cases.append(pytest.param(preset, fork, case, id=path, marks=marks))
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
    assert runs(fork, case.parts[-4], case.parts[-3])
    run_case(preset, fork, case)


@archives.parametrize("preset, fork, case", _archive_cases)
def test_archive_case(preset, fork, case):
    run_case(preset, fork, case)


def test_anchor_state_mismatch():
    # The anchor block must commit to the anchor state; its state root sits at bytes 48 to 80.
    case = next((FILES / "minimal" / "altair").rglob("steps.yaml")).parent
    block = bytearray(_read(case, "anchor_block"))
    block[48] ^= 1
    with raises(
        consensus.ForkChoiceError,
        "fork choice: EthLib.Consensus.ForkChoiceError.anchorStateMismatch",
    ) as info:
        consensus.fork_choice("minimal", "altair", _read(case, "anchor_state"), bytes(block), [])
    assert info.value.code == 1
