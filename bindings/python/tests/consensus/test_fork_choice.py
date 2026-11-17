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
        groups = [next(outcomes) for _ in inputs[index]]
        assert all(groups), (index, groups)
        reads = [group[0] for group in groups]
        if "checks" in step:
            assert all(len(group) == 1 for group in groups), (index, groups)
            found = [read for read in reads if isinstance(read, dict)]
            assert len(found) == len(reads), (index, reads)
            _check(found[0] if len(found) == 1 else found[0] | found[1], step["checks"])
        else:
            assert len(reads) == 1, (index, reads)
            outcome = reads[0]
            assert (outcome is None) == step.get("valid", True), (index, step, outcome)
            # The helper's valid block cases require every carried handler to succeed too.
            if outcome is None:
                assert all(result is None for group in groups for result in group[1:]), (
                    index,
                    groups,
                )
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
    state_root = bytes(block[48:80])
    block[48] ^= 1
    message = (
        f"fork choice: expected the anchor state root 0x{state_root.hex()}, "
        f"got the block's state root 0x{bytes(block[48:80]).hex()}"
    )
    with raises(consensus.ForkChoiceError, message) as info:
        consensus.fork_choice("minimal", "altair", _read(case, "anchor_state"), bytes(block), [])
    assert info.value.code == 1


# A case with blocks at slots 1, 2 and 3, each built on the one before.
_CARRIED_CASE = (
    FILES / "minimal/altair/fast_confirmation/current_epoch/pyspec_tests/fcr_current_epoch_02"
)


def _sealed(signed: dict, state: bytes, admitted: bool) -> bytes:
    """A signed block with its true state root, or with the zero root that the store rejects."""
    message = signed["message"]
    encoded = consensus.api_ssz("minimal", "altair", "BeaconBlock", message)
    root = consensus.compute_new_state_root("minimal", "altair", state, encoded, verify=False)
    message["state_root"] = "0x" + (root if admitted else bytes(32)).hex()
    return consensus.api_ssz("minimal", "altair", "SignedBeaconBlock", signed)


def _carried_replay(voted_admitted: bool, slashed_admitted: bool) -> tuple[list, bytes]:
    """The outcomes of a block that votes for block 1, then of one that slashes those voters."""
    # The pinned slot-2 block moves onto the anchor, so block 1 stays a leaf with its own weight.
    # Its first attestation is the vote of the four validators of the slot-1 committee.
    # A copy with an unknown root follows: the transition accepts it and the fork choice rejects it.
    # The slot-3 block moves onto the slot-2 block and carries a double vote of those four.
    # Proposers in epoch 0 do not depend on the branch, so both blocks keep theirs.
    case = _CARRIED_CASE
    names = [step["block"] for step in _load(case / "steps.yaml") if "block" in step]
    anchor_state, anchor_block = _read(case, "anchor_state"), _read(case, "anchor_block")
    anchor_root = consensus.ssz_static("minimal", "altair", "BeaconBlock", anchor_block)[0]
    first = _read(case, names[0])
    first_root = _hex(names[0].removeprefix("block_"))
    voted = consensus.api_json("minimal", "altair", "SignedBeaconBlock", _read(case, names[1]))
    message = voted["message"]
    assert message["slot"] == "2"
    message["parent_root"] = "0x" + anchor_root.hex()
    good = message["body"]["attestations"][0]
    bad = {**good, "data": {**good["data"], "beacon_block_root": "0x" + "42" * 32}}
    message["body"]["attestations"] = [good, bad]
    committee = consensus.api_committees(
        "minimal", "altair", anchor_state, epoch=0, slot=1, index=0
    )["data"][0]["validators"]
    assert len(committee) == 4
    voted_block = _sealed(voted, anchor_state, True)
    encoded = consensus.api_ssz("minimal", "altair", "BeaconBlock", message)
    voted_root = consensus.ssz_static("minimal", "altair", "BeaconBlock", encoded)[0]
    state = consensus.state_transitions(
        "minimal", "altair", anchor_state, [voted_block], verify=False
    )
    if not voted_admitted:
        voted_block = _sealed(voted, anchor_state, False)
    slashed = consensus.api_json("minimal", "altair", "SignedBeaconBlock", _read(case, names[2]))
    message = slashed["message"]
    assert message["slot"] == "3"
    message["parent_root"] = "0x" + voted_root.hex()
    indexed = {
        "attesting_indices": sorted(committee, key=int),
        "data": good["data"],
        "signature": good["signature"],
    }
    message["body"]["attestations"] = []
    message["body"]["attester_slashings"] = [
        {"attestation_1": indexed, "attestation_2": {**indexed, "data": bad["data"]}}
    ]
    slashed_block = _sealed(slashed, state, slashed_admitted)
    outcomes = consensus.fork_choice(
        "minimal",
        "altair",
        anchor_state,
        anchor_block,
        [
            ("tick", 6),
            ("block", first),
            ("tick", 18),
            ("checks", (False, True, None)),
            ("block", voted_block),
            ("checks", (False, True, None)),
            ("block", slashed_block),
            ("checks", (False, True, None)),
        ],
        verify=False,
        config={"PROPOSER_SCORE_BOOST": 0},
    )
    return outcomes, first_root


def _weight(read: dict, root: bytes) -> int:
    """The weight of a viable leaf of the block tree, from a read of the store."""
    leaves = read["viable_for_head_roots_and_weights"]
    return next(leaf["weight"] for leaf in leaves if leaf["root"] == root)


def _wrong_state_root(outcome: object) -> bool:
    """Whether an outcome is the rejection of a block whose state root is wrong."""
    return isinstance(outcome, consensus.ForkChoiceError) and str(outcome) == (
        "the state transition fails: EthLib.Consensus.TransitionError.wrongStateRoot"
    )


# The four votes for block 1 weigh four effective balances of 32 ETH, in Gwei.
_FOUR_VOTES = 128_000_000_000


def test_rejected_block_runs_no_carried_handlers():
    # Had the carried votes run, block 1 would weigh 128 ETH.
    outcomes, first = _carried_replay(voted_admitted=False, slashed_admitted=True)
    assert outcomes[4] == [outcomes[4][0]]
    assert _wrong_state_root(outcomes[4][0])
    assert _weight(outcomes[5][0], first) == 0
    # Had the carried slashing run, block 1 would weigh nothing.
    outcomes, first = _carried_replay(voted_admitted=True, slashed_admitted=False)
    assert outcomes[4][:2] == [None, None]
    assert _weight(outcomes[5][0], first) == _FOUR_VOTES
    assert outcomes[6] == [outcomes[6][0]]
    assert _wrong_state_root(outcomes[6][0])
    assert _weight(outcomes[7][0], first) == _FOUR_VOTES


def test_carried_handlers_commit_independently():
    outcomes, first = _carried_replay(voted_admitted=True, slashed_admitted=True)
    assert outcomes[3] == [{**outcomes[3][0]}]
    assert _weight(outcomes[3][0], first) == 0
    # The vote for an unknown block fails after the good vote, which keeps its weight.
    assert len(outcomes[4]) == 3
    assert outcomes[4][:2] == [None, None]
    assert isinstance(outcomes[4][2], consensus.ForkChoiceError)
    assert outcomes[4][2].code == 2  # unknownBlock
    assert _weight(outcomes[5][0], first) == _FOUR_VOTES
    # Slashing the four voters removes their weight.
    assert outcomes[6] == [None, None]
    assert _weight(outcomes[7][0], first) == 0


def test_carried_handlers_run_on_each_receipt():
    # Adapt the pinned slot-7 block, which carries two slot-6 votes, and keep its true state root.
    # The transition accepts a vote for an unknown root, and the fork choice rejects it.
    case = _CARRIED_CASE
    name = "block_0x0431ca898066abec9f55aa1bd0e701d14292bd6010a2e747debea04e911ff273"
    steps = _load(case / "steps.yaml")
    index = next(i for i, step in enumerate(steps) if step.get("block") == name)
    anchor_state, anchor_block = _read(case, "anchor_state"), _read(case, "anchor_block")
    signed = consensus.api_json("minimal", "altair", "SignedBeaconBlock", _read(case, name))
    message = signed["message"]
    message["body"]["attestations"][0]["data"]["beacon_block_root"] = "0x" + "42" * 32
    prior = [_read(case, step["block"]) for step in steps[:index] if "block" in step]
    state = consensus.state_transitions("minimal", "altair", anchor_state, prior, verify=False)
    block = _sealed(signed, state, True)
    encoded = consensus.api_ssz("minimal", "altair", "BeaconBlock", message)
    root = consensus.ssz_static("minimal", "altair", "BeaconBlock", encoded)[0]
    inputs = [one for step in steps[:index] for one in _inputs(case, step)]
    good_vote = consensus.api_ssz(
        "minimal", "altair", "Attestation", message["body"]["attestations"][1]
    )
    # A known block is admitted again, and its carried operations run again.
    # At epoch 3 the slot-6 vote is stale on the wire, but a vote from a block skips that check.
    outcomes = consensus.fork_choice(
        "minimal",
        "altair",
        anchor_state,
        anchor_block,
        [
            *inputs,
            ("block", block),
            ("block", block),
            ("checks", False),
            ("tick", 144),
            ("block", block),
            ("attestation", good_vote),
        ],
        verify=False,
    )
    for group in [outcomes[-6], outcomes[-5], outcomes[-2]]:
        assert len(group) == 3
        assert group[0] is None
        assert isinstance(group[1], consensus.ForkChoiceError)
        assert group[1].code == 2  # unknownBlock
        assert group[2] is None
    assert len(outcomes[-1]) == 1
    assert isinstance(outcomes[-1][0], consensus.ForkChoiceError)
    read = outcomes[-4][0]
    assert isinstance(read, dict)
    head = read["head"]
    assert head["slot"] == 7
    assert head["root"] == root


def test_fast_confirmation_discount_bound():
    # The vector has blocks at slots 1 and 2, none at slots 3 to 6, and votes for block 2.
    case = (
        FILES
        / "minimal/altair/fast_confirmation/empty_slots/pyspec_tests"
        / "fcr_slot_head_tracking_during_empty_slots"
    )
    steps = _load(case / "steps.yaml")
    anchor_state = _read(case, "anchor_state")
    anchor_block = _read(case, "anchor_block")
    blocks = [_read(case, step["block"]) for step in steps if "block" in step]
    state = consensus.state_transitions("minimal", "altair", anchor_state, blocks, verify=False)
    # A signed block is the offset of its message, its 96-byte signature, then the message.
    prefix, message = blocks[0][:100], blocks[0][100:]
    parent_root = consensus.ssz_static("minimal", "altair", "BeaconBlock", blocks[-1][100:])[0]
    parent_slot, child_slot = 2, 7
    # A slot of the minimal preset lasts 6 seconds.
    seconds_per_slot = 6
    pre_state = consensus.process_slots("minimal", "altair", state, child_slot - parent_slot)
    # The minimal genesis has 64 validators.
    proposer = next(
        index for index in range(64) if consensus.is_proposer("minimal", "altair", pre_state, index)
    )
    # Add a child at slot 7, reusing the first block's body and skipping signature checks.
    # The message holds its slot, its proposer, its parent root and its state root, then its body.
    child = bytearray(message)
    child[:8] = child_slot.to_bytes(8, "little")
    child[8:16] = proposer.to_bytes(8, "little")
    child[16:48] = parent_root
    child[48:80] = consensus.compute_new_state_root(
        "minimal", "altair", state, bytes(child), verify=False
    )
    child_root = consensus.ssz_static("minimal", "altair", "BeaconBlock", bytes(child))[0]
    # Moved to slot 7, the full votes of slot 6 come from the committees of slot 7, for the child.
    # An attestation holds the offset of its bits, then its slot, its index and its block root.
    attestations: list[consensus.ForkChoiceStep] = []
    for step in steps:
        if "attestation" not in step:
            continue
        vote = bytearray(_read(case, step["attestation"]))
        if int.from_bytes(vote[4:12], "little") == child_slot - 1:
            vote[4:12] = child_slot.to_bytes(8, "little")
            vote[20:52] = child_root
            attestations.append(("attestation", bytes(vote)))
    assert len(attestations) == 2
    # The votes of slot 7 count from slot 8 on, so the clock reaches slot 8 before it moves back.
    inputs: list[consensus.ForkChoiceStep] = [one for step in steps for one in _inputs(case, step)]
    inputs += [("block", prefix + bytes(child)), ("tick", 8 * seconds_per_slot), *attestations]

    def confirm(current_slot: int, boost: int = 0) -> list:
        """The outcomes of the steps, with the clock set back to a slot, then a confirmation."""
        outcomes = consensus.fork_choice(
            "minimal",
            "altair",
            anchor_state,
            anchor_block,
            [*inputs, ("tick", current_slot * seconds_per_slot), ("fast_confirmation", None)],
            verify=False,
            config={"CONFIRMATION_BYZANTINE_THRESHOLD": 0, "PROPOSER_SCORE_BOOST": boost},
        )
        assert len(outcomes) == len(inputs) + 2
        assert all(
            outcome is None or isinstance(outcome, dict)
            for group in outcomes[:-1]
            for outcome in group
        )
        assert len(outcomes[-1]) == 1
        return [group[0] for group in outcomes]

    # With no adversary and no boost, the threshold is half of the maximum minus the discount.
    # A slot holds 8 validators of 32 ETH, so the votes of slots 3 to 6 give a 1024 ETH discount.
    # At slot 7 the maximum is the weight of slots 3 to 6, 1024 ETH: equality is valid.
    confirmation = confirm(7)[-1]
    assert isinstance(confirmation, dict)
    assert confirmation["confirmed_root"] == child_root
    # At slot 6 the child is from the future, and the maximum is the 768 ETH of slots 3 to 5.
    # Only a clock that moves back reaches such a store.
    error = confirm(6)[-1]
    assert isinstance(error, consensus.ForkChoiceError)
    assert error.code == 53
    assert str(error) == (
        f"the support discount of the block 0x{child_root.hex()} "
        "exceeds the committee weight since its parent"
    )
    # A boost of a full committee, 256 ETH, lifts the bound to the discount; the maximum stays.
    boosted = confirm(6, 100)[-1]
    assert isinstance(boosted, consensus.ForkChoiceError)
    assert boosted.code == 53
