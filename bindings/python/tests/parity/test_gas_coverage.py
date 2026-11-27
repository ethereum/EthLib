"""Check the gas report and its classification of pinned branch witnesses."""

import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest

from ethlib.serialization import rlp

from . import catalogue, gas_coverage, runners
from .catalogue import Case

# The fixtures come from the execution release pinned in tests/sources.toml.
SLOAD = (
    "fixtures/state_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/sload_gas"
)
TRANSITION = (
    "fixtures/blockchain_tests/for_bpo2toamsterdamattime15k/amsterdam/"
    "eip8038_state_access_gas_cost_increase/fork_transition/sstore_write_cost_at_transition.json"
)


def test_cli_requires_assertions(tmp_path) -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-O",
            "-m",
            "parity.gas_coverage",
            "--executable",
            str(tmp_path / "missing"),
        ],
        cwd=Path(__file__).resolve().parents[1],
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    assert result.returncode == 2
    assert result.stderr.endswith("error: fixture validation requires Python assertions\n")


def test_report_lists_each_named_branch() -> None:
    inventory = {"gasRules": ["opcode.sload.warm", "opcode.sload.cold", "opcode.memory.expand"]}
    counts = gas_coverage.Counts(
        Counter({"opcode.sload.cold": 3, "opcode.sload.warm": 1}), state_transactions=2
    )
    report = "\n".join(gas_coverage.render_fork("berlin", inventory, counts))
    assert "Observed **2 of 3** instrumented gas rules." in report
    assert "| `opcode.sload.cold` | 3 |" in report
    assert "| `opcode.sload.warm` | 1 |" in report
    assert report.endswith("- `opcode.memory.expand`")


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("stateRoot", "ff", "state root differs"),
        ("logsHash", "ff", "logs hash differs"),
        ("gasUsed", 21_001, "gas used differs"),
        ("succeeded", False, "transaction status differs"),
        ("receipt", "ff", "receipt bytes differ"),
    ],
)
def test_state_output_mismatch_discards_events(monkeypatch, field, value, message) -> None:
    case = Case("execution-spec-tests", "", "Amsterdam", "state_test", "case", "case.json")
    post = {
        "hash": "0x01",
        "logs": "0x02",
        "receipt": {"cumulativeGasUsed": "0x5208", "status": True, "rlp": "0x03"},
    }
    monkeypatch.setattr(
        runners, "state_test_input", lambda *_: (("glamsterdam", 1, b"tx", b"pre", b"env"), post)
    )
    response = {
        "stateRoot": "01",
        "logsHash": "02",
        "gasUsed": 21_000,
        "succeeded": True,
        "receipt": "03",
        "gasRules": {"opcode.sload.warm": 1},
    }
    report = gas_coverage.replay_cases(Path(), [case], lambda _: {**response, field: value})
    assert report.counts == {}
    assert report.failures == [(case, message)]


def test_expected_admission_error_supplies_no_coverage(monkeypatch) -> None:
    case = Case("execution-spec-tests", "", "Amsterdam", "state_test", "case", "case.json")
    post = {"expectException": "TransactionException.NONCE_MISMATCH_TOO_HIGH"}
    monkeypatch.setattr(
        runners, "state_test_input", lambda *_: (("glamsterdam", 1, b"tx", b"pre", b"env"), post)
    )

    def reject(_payload):
        raise gas_coverage.FixtureError("nonceTooHigh")

    report = gas_coverage.replay_cases(Path(), [case], reject)
    assert report.counts == {}
    assert report.failures == []
    assert list(report.outcomes) == [
        (case.suite, case.fork, case.group, "checked without observed events", "")
    ]


def test_later_block_failure_discards_earlier_events(monkeypatch) -> None:
    case = Case(
        "execution-spec-tests",
        "",
        "CancunToPragueAtTime15k",
        "blockchain_test",
        "case",
        "case.json",
    )

    def check_fixture(_root, _case, transition):
        transition({}, b"", [], "dencun", b"block", False)
        pytest.fail("the next block failed its parity check")

    monkeypatch.setattr(runners, "check_blockchain_test", check_fixture)
    response = {"state": "01", "gasRules": {"opcode.sload.cold": 1}}
    report = gas_coverage.replay_cases(Path(), [case], lambda _: response)
    assert report.counts == {}
    assert report.failures == [(case, "the next block failed its parity check")]


@pytest.fixture(scope="module")
def observer():
    if not gas_coverage.EXECUTABLE.is_file():
        pytest.skip("build the fixture runner with lake build gas-coverage")
    with gas_coverage.open_bridge(gas_coverage.EXECUTABLE) as bridge:
        yield bridge.request


@pytest.mark.archive(catalogue.EXECUTION, SLOAD)
def test_pinned_sload_branches(archive, observer) -> None:
    # EIP-2929 makes the slot warm through the access list or a prior access in the same scope.
    # A reverted subcall's access does not warm the caller's slot.
    witnesses = [
        ("sload_gas", "state_test-cold", 1, 0),
        ("sload_gas", "state_test-warm", 0, 1),
        ("sload_warm_after_prior_touch", "state_test", 1, 1),
        ("sload_warmth_reverts_on_subcall_revert", "state_test", 2, 0),
    ]
    for name, variant, cold, warm in witnesses:
        case = Case(
            "execution-spec-tests",
            "",
            "Amsterdam",
            "state_test",
            "tests/amsterdam/eip8038_state_access_gas_cost_increase/test_sload_gas.py"
            f"::test_{name}[fork_Amsterdam-{variant}]",
            f"{SLOAD}/{name}.json",
        )
        counts = gas_coverage.replay_state(archive, case, observer)["glamsterdam"]
        assert counts.state_transactions == 1
        assert counts.gas_rules["opcode.sload.cold"] == cold
        assert counts.gas_rules["opcode.sload.warm"] == warm


def transition_case(archive: Path) -> Case:
    (name,) = json.loads((archive / TRANSITION).read_text())
    return Case(
        "execution-spec-tests", "", "BPO2ToAmsterdamAtTime15k", "blockchain_test", name, TRANSITION
    )


@pytest.mark.archive(catalogue.EXECUTION, TRANSITION)
def test_pinned_sstore_transition(archive, observer) -> None:
    counts = gas_coverage.replay_blockchain(archive, transition_case(archive), observer)
    assert {fork: result.blocks for fork, result in counts.items()} == {"bpo2": 1, "glamsterdam": 1}
    before, after = counts["bpo2"].gas_rules, counts["glamsterdam"].gas_rules
    # Each block fills three empty slots with the timestamp, the parent hash and 1.
    # The beacon roots contract also writes a zero root to an empty slot.
    assert before["opcode.sstore.set-execution-charge"] == 3
    assert before["opcode.sstore.new-slot-state-charge"] == 0
    assert after["opcode.sstore.set-execution-charge"] == 0
    assert after["opcode.sstore.clean-write-execution-charge"] == 3
    assert after["opcode.sstore.new-slot-state-charge"] == 3


@pytest.mark.archive(
    catalogue.LEGACY,
    *(f"{catalogue.LEGACY_ROOT}/{path}" for path in gas_coverage.LEGACY_GAS_CASES),
)
def test_pinned_legacy_gas_branches(archive, observer) -> None:
    root = archive / catalogue.LEGACY_ROOT
    labels = {
        "frontier": "opcode.create.skipped-before-grant",
        "homestead": "opcode.create.skipped-before-grant",
        "tangerineWhistle": "opcode.create.skipped-before-grant",
        "istanbul": "opcode.sstore.clear-refund-debit",
    }
    report = gas_coverage.replay_cases(
        root,
        [
            case
            for case in gas_coverage.source_cases(gas_coverage.LEGACY, catalogue.LEGACY)
            if case.path in gas_coverage.LEGACY_GAS_CASES
        ],
        observer,
    )
    assert report.failures == []
    assert report.counts.keys() == labels.keys()
    for fork, label in labels.items():
        assert report.counts[fork].blocks == 1
        assert report.counts[fork].gas_rules[label] == 1


@pytest.mark.archive(catalogue.EXECUTION, TRANSITION)
@pytest.mark.parametrize(
    ("field", "error"),
    [("stateRoot", "wrongStateRoot"), ("receiptTrie", "wrongReceiptRoot")],
)
def test_corrupt_pinned_block_root_discards_events(archive, observer, field, error) -> None:
    def corrupt_amsterdam(payload):
        if payload["fork"] == "glamsterdam":
            block = rlp.decode(bytes.fromhex(payload["block"]))
            header = block[0]
            index = runners.HEADER_FIELDS.index(field)
            root = header[index]
            header[index] = bytes([root[0] ^ 1]) + root[1:]
            payload = {**payload, "block": rlp.encode(block).hex()}
        return observer(payload)

    case = transition_case(archive)
    report = gas_coverage.replay_cases(archive, [case], corrupt_amsterdam)
    assert report.counts == {}
    ((failed, message),) = report.failures
    assert failed == case
    assert error in message
