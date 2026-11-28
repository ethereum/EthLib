"""Check the gas report and its classification of pinned branch witnesses."""

import json
import os
import shlex
import signal
import subprocess
import sys
from collections import Counter
from copy import deepcopy
from pathlib import Path, PurePosixPath

import pytest

from ethlib.serialization import rlp
from raising import raises

from . import catalogue, gas_coverage, legacy, runners
from .catalogue import Case

# The fixtures come from the execution release pinned in tests/sources.toml.
SLOAD = (
    "fixtures/state_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/sload_gas"
)
SSTORE_RESTORATION = (
    "fixtures/state_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/"
    "state_gas_sstore/sstore_restoration_refund.json"
)
TRANSITION = (
    "fixtures/blockchain_tests/for_bpo2toamsterdamattime15k/amsterdam/"
    "eip8038_state_access_gas_cost_increase/fork_transition/sstore_write_cost_at_transition.json"
)
BERLIN_CALL = (
    "fixtures/state_tests/for_berlin/berlin/eip2929_gas_cost_increases/call/"
    "call_insufficient_balance.json"
)
AMSTERDAM_CALL = (
    "fixtures/state_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/"
    "state_gas_call/call_insufficient_balance_returns_reservoir.json"
)
AMSTERDAM_JUMPDEST = (
    "fixtures/state_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/"
    "eip_vectors/vector_dupn_followed_by_jumpdest.json"
)
DENCUN_TLOAD = (
    "fixtures/state_tests/for_cancun/cancun/eip1153_tstore/basic_tload/basic_tload_gasprice.json"
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


@pytest.mark.parametrize("jobs", [0, gas_coverage.MAX_JOBS + 1])
def test_cli_limits_workers(jobs, monkeypatch, capsys) -> None:
    monkeypatch.setattr(
        sys, "argv", ["gas_coverage", "--executable", sys.executable, "--jobs", str(jobs)]
    )
    with raises(SystemExit, "2"):
        gas_coverage.main()
    assert capsys.readouterr().err.splitlines()[-1] == (
        f"gas_coverage: error: --jobs must be from 1 to {gas_coverage.MAX_JOBS}"
    )


def test_report_lists_each_named_branch() -> None:
    inventory = gas_coverage.InventoryReply(
        0, frozenset({"opcode.sload.warm", "opcode.sload.cold", "opcode.memory.expand"})
    )
    counts = gas_coverage.Counts(
        gas_rules=Counter({"opcode.sload.cold": 3, "opcode.sload.warm": 1}), state_transactions=2
    )
    report = "\n".join(gas_coverage.render_fork("berlin", inventory, counts))
    assert "Observed **2 of 3** instrumented gas rules." in report
    assert "| `opcode.sload.cold` | 3 |" in report
    assert "| `opcode.sload.warm` | 1 |" in report
    assert report.endswith("- `opcode.memory.expand`")


def test_report_orders_forks_and_networks_by_activation() -> None:
    report = gas_coverage.Report()
    report.counts = {
        "berlin": gas_coverage.Counts(),
        "frontier": gas_coverage.Counts(),
        "bpo2": gas_coverage.Counts(),
        "daoFork": gas_coverage.Counts(),
    }
    for network in ("Amsterdam", "Berlin", "Frontier", "NewNetwork", "BPO2"):
        case = Case("execution-spec-tests", "", network, "state_test", "case", "case.json")
        report.outcome(case, "skipped")
    indices = {"frontier": 0, "daoFork": 2, "berlin": 11, "bpo2": 23}

    def inventory(request):
        return {"forkIndex": indices[request["fork"]], "gasRules": ["opcode.fixed-price.0"]}

    lines = gas_coverage.render_report(report, {}, inventory).splitlines()
    headings = [line[3:] for line in lines if line[3:] in indices and line.startswith("## ")]
    networks = [line.split(" | ")[1] for line in lines if line.startswith("| execution-spec-tests")]
    assert headings == ["frontier", "daoFork", "berlin", "bpo2"]
    assert networks == ["Frontier", "Berlin", "BPO2", "Amsterdam", "NewNetwork"]


def test_selection_and_partition_keep_every_variant() -> None:
    def case(network: str, name: str, path: str) -> Case:
        return Case("execution-spec-tests", "", network, "state_test", name, path)

    cold = case("Amsterdam", "cold", "fixtures/group/shared.json")
    warm = case("Amsterdam", "warm", "fixtures/group/shared.json")
    other = case("Amsterdam", "other", "fixtures/group/other.json")
    selected = gas_coverage.select_cases(
        [
            warm,
            case("Berlin", "cold", cold.path),
            case("Amsterdam", "nearby", "fixtures/group_other/shared.json"),
            cold,
            other,
        ],
        {"Amsterdam"},
        {"state_test"},
        PurePosixPath("fixtures/group"),
    )
    assert selected == [other, cold, warm]
    assert gas_coverage.partition_cases(selected, 3) == [[cold, warm], [other]]


def test_skip_reason_follows_parity_plans_and_exclusions(monkeypatch) -> None:
    monkeypatch.setitem(runners.NOT_YET, "planned_test", "the runner that brings it")
    monkeypatch.setitem(catalogue.EXCLUDED_FORMATS, "excluded_test", "outside parity's scope")

    def reason(fork: str, group: str) -> str:
        case = Case("execution-spec-tests", "", fork, group, "case", "case.json")
        return gas_coverage.skip_reason(case, {})

    assert reason("Berlin", "state_test") == ""
    assert reason("Berlin", "planned_test") == "the runner that brings it"
    assert reason("Berlin", "excluded_test") == "outside parity's scope"
    assert reason("Berlin", "blockchain_test_engine") == (
        "the coverage runner does not replay this fixture format"
    )
    assert reason("BPO2ToBPO3AtTime15k", "state_test") == (
        "no parity runner for this fixture at this network"
    )
    assert reason("UnknownNetwork", "blockchain_test") == (
        "fixture network is outside the implemented execution forks"
    )


@pytest.mark.parametrize("group", [None, "state_test"])
def test_skip_reason_uses_listed_disagreements(group) -> None:
    case = Case("execution-spec-tests", "", "Berlin", "state_test", "case", "case.json")
    disagreements = {("case", group): {"reason": "fixture disagrees"}}
    assert gas_coverage.skip_reason(case, disagreements) == "listed parity disagreement"


@pytest.mark.parametrize(
    ("reply", "error"),
    [
        ("!\n", "gas-coverage returned invalid JSON for the inventory request for berlin"),
        (
            "[" * (sys.getrecursionlimit() + 1),
            "gas-coverage returned invalid JSON for the inventory request for berlin",
        ),
        ("[]\n", "gas-coverage returned a non-object reply to the inventory request for berlin"),
        (
            '{"error":0}\n',
            "gas-coverage returned an invalid error for the inventory request for berlin",
        ),
        (
            '{"error":{"code":true,"message":"invalid fork"}}\n',
            "gas-coverage returned an invalid error for the inventory request for berlin",
        ),
        (
            '{"error":{"code":0,"message":"invalid fork"}}\n',
            "gas-coverage rejected the inventory request for berlin: invalid fork",
        ),
    ],
)
def test_bridge_diagnostics(reply, error) -> None:
    with raises(RuntimeError, error):
        gas_coverage.decode_reply(reply.encode(), "inventory", "inventory request for berlin")


def test_bridge_distinguishes_fixture_error_from_invalid_reply() -> None:
    request = "state request for berlin"
    with raises(gas_coverage.FixtureError, "nonceTooHigh"):
        gas_coverage.decode_reply(
            b'{"error":{"code":0,"message":"nonceTooHigh"}}', "state", request
        )
    with raises(RuntimeError, f"gas-coverage returned an invalid error for the {request}"):
        gas_coverage.decode_reply(b'{"error":{"message":"nonceTooHigh"}}', "state", request)


@pytest.fixture
def bridge_child(tmp_path, monkeypatch):
    """Start a test program through the same pipes as the fixture runner."""
    start = subprocess.Popen
    processes = []

    def record(*args, **kwargs):
        process = start(*args, **kwargs)
        processes.append(process)
        return process

    def program(source):
        script = tmp_path / "child.py"
        script.write_text(source)
        executable = tmp_path / "child"
        executable.write_text(f"#!/bin/sh\nexec {shlex.join([sys.executable, str(script)])}\n")
        executable.chmod(0o700)
        return executable, processes

    monkeypatch.setattr(gas_coverage.subprocess, "Popen", record)
    return program


def test_bridge_transfers_multiple_large_messages(bridge_child) -> None:
    executable, processes = bridge_child(
        "import json, sys\n"
        "for line in sys.stdin:\n"
        "    request = json.loads(line)\n"
        "    print(json.dumps({'echo': request['data']}), flush=True)\n"
    )
    with gas_coverage.open_bridge(executable) as bridge:
        for data in ("a" * 250_000, "b" * 130_000):
            assert bridge.request({"kind": "state", "fork": "berlin", "data": data}) == {
                "echo": data
            }
    assert processes[0].returncode == 0


@pytest.mark.parametrize(
    ("source", "payload_size", "action"),
    [
        ("import time\ntime.sleep(30)\n", 1_000_000, "sending"),
        (
            "import sys, time\nsys.stdin.readline()\n"
            "print('{', end='', flush=True)\ntime.sleep(30)\n",
            0,
            "waiting for",
        ),
    ],
    ids=["full input pipe", "partial output line"],
)
def test_bridge_times_out_and_reaps_child(bridge_child, source, payload_size, action) -> None:
    executable, processes = bridge_child(source)
    with (
        raises(RuntimeError, f"gas-coverage timed out while {action} the state request for berlin"),
        gas_coverage.open_bridge(executable, timeout=0.5) as bridge,
    ):
        bridge.request({"kind": "state", "fork": "berlin", "data": "x" * payload_size})
    assert processes[0].returncode == -signal.SIGKILL


def test_bridge_reaps_child_after_early_eof(bridge_child) -> None:
    executable, processes = bridge_child("import sys\nsys.stdin.readline()\n")
    with (
        raises(
            RuntimeError, "gas-coverage stopped before replying to the inventory request for berlin"
        ),
        gas_coverage.open_bridge(executable) as bridge,
    ):
        bridge.request({"kind": "inventory", "fork": "berlin"})
    assert processes[0].returncode is not None


def test_bridge_reaps_a_child_that_ignores_eof(bridge_child) -> None:
    executable, processes = bridge_child("import sys, time\nsys.stdin.read()\ntime.sleep(30)\n")
    with (
        raises(RuntimeError, "gas-coverage did not exit after closing its input"),
        gas_coverage.open_bridge(executable, exit_timeout=0.5),
    ):
        pass
    assert processes[0].returncode == -signal.SIGKILL


def test_bridge_reaps_child_on_replay_failure(bridge_child) -> None:
    executable, processes = bridge_child("import time\ntime.sleep(30)\n")
    with raises(ValueError, "caller failed"), gas_coverage.open_bridge(executable):
        raise ValueError("caller failed")
    assert processes[0].returncode == -signal.SIGKILL


def test_reject_duplicate_inventory_and_invalid_event_counts() -> None:
    with raises(RuntimeError, "duplicate gas rules in the berlin inventory"):
        gas_coverage.parse_inventory_reply({"forkIndex": 0, "gasRules": ["warm", "warm"]}, "berlin")
    for invalid in (["warm"], {"warm": -1}, {"warm": 0}, {"warm": True}, {"": 1}):
        with raises(RuntimeError, "gas-coverage returned invalid gas event counts"):
            gas_coverage.gas_events({"gasRules": invalid})


@pytest.mark.parametrize("response", [{"gasRules": []}, {"forkIndex": True, "gasRules": []}])
def test_inventory_reply_requires_a_valid_index(response) -> None:
    with raises(RuntimeError, "invalid fork index in the berlin inventory"):
        gas_coverage.parse_inventory_reply(response, "berlin")


@pytest.mark.parametrize("rules", [None, "warm", [""], [0]])
def test_inventory_reply_requires_valid_rules(rules) -> None:
    with raises(RuntimeError, "invalid gas rule inventory for berlin"):
        gas_coverage.parse_inventory_reply({"forkIndex": 0, "gasRules": rules}, "berlin")


@pytest.mark.parametrize(
    ("field", "invalid"),
    [
        ("stateRoot", "01"),
        ("logsHash", "z1" * 32),
        ("gasUsed", True),
        ("succeeded", 1),
        ("receipt", "00 01"),
    ],
)
def test_state_reply_rejects_missing_or_malformed_fields(field, invalid) -> None:
    reply = {
        "stateRoot": "01" * 32,
        "logsHash": "02" * 32,
        "gasUsed": 21_000,
        "succeeded": True,
        "receipt": "03",
        "gasRules": {},
    }
    with raises(RuntimeError, f"gas-coverage returned invalid {field}"):
        gas_coverage.parse_state_reply({**reply, field: invalid})
    del reply[field]
    with raises(RuntimeError, f"gas-coverage returned invalid {field}"):
        gas_coverage.parse_state_reply(reply)


@pytest.mark.parametrize(
    ("response", "field"),
    [
        ({"receipts": []}, "state"),
        ({"state": "g0", "receipts": []}, "state"),
        ({"state": "01"}, "receipts"),
        ({"state": "01", "receipts": {"0": "02"}}, "receipts"),
        ({"state": "01", "receipts": ["02", "0"]}, "receipt 1"),
    ],
)
def test_block_reply_rejects_missing_or_malformed_fields(response, field) -> None:
    with raises(RuntimeError, f"gas-coverage returned invalid {field}"):
        gas_coverage.parse_block_reply({**response, "gasRules": {}})


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("stateRoot", "ff" * 32, "state root differs"),
        ("logsHash", "ff" * 32, "logs hash differs"),
        ("gasUsed", 21_001, "gas used differs"),
        ("succeeded", False, "transaction status differs"),
        ("receipt", "ff", "receipt bytes differ"),
    ],
)
def test_state_output_mismatch_discards_events(monkeypatch, field, value, message) -> None:
    case = Case("execution-spec-tests", "", "Amsterdam", "state_test", "case", "case.json")
    post = {
        "hash": "0x" + "01" * 32,
        "logs": "0x" + "02" * 32,
        "receipt": {"cumulativeGasUsed": "0x5208", "status": True, "rlp": "0x03"},
    }
    monkeypatch.setattr(
        runners, "state_test_input", lambda *_: (("glamsterdam", 1, b"tx", b"pre", b"env"), post)
    )
    response = {
        "stateRoot": "01" * 32,
        "logsHash": "02" * 32,
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
    assert report.counts == {"glamsterdam": gas_coverage.Counts()}
    lines = gas_coverage.render_fork(
        "glamsterdam",
        gas_coverage.InventoryReply(0, frozenset({"opcode.sload.warm"})),
        report.counts["glamsterdam"],
    )
    assert "Observed **0 of 1** instrumented gas rules." in lines
    assert "- `opcode.sload.warm`" in lines
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
    response = {"state": "01", "receipts": [], "gasRules": {"opcode.sload.cold": 1}}
    report = gas_coverage.replay_cases(Path(), [case], lambda _: response)
    assert report.counts == {}
    assert report.failures == [(case, "the next block failed its parity check")]


@pytest.mark.parametrize(
    ("network", "fork"),
    [
        ("Amsterdam", "glamsterdam"),
        ("AmsterdamToBPOIncreaseAtTime15k", "glamsterdam"),
        ("BPO2ToAmsterdamAtTime15k", None),
    ],
)
def test_network_with_no_accepted_blocks_has_empty_counts(monkeypatch, network, fork) -> None:
    monkeypatch.setattr(runners, "check_blockchain_test", lambda *_: None)
    case = Case("execution-spec-tests", "", network, "blockchain_test", "case", "case.json")
    expected = {fork: gas_coverage.Counts()} if fork is not None else {}
    assert gas_coverage.replay_blockchain(Path(), case, lambda _: {}) == expected


@pytest.fixture(scope="module")
def coverage_executable() -> Path:
    executable = gas_coverage.EXECUTABLE
    if not executable.is_file():
        message = "build the fixture runner with lake build gas-coverage"
        if os.environ.get("ETHLIB_REQUIRE_GAS_COVERAGE") == "1":
            pytest.fail(message)
        pytest.skip(message)
    return executable


@pytest.fixture(scope="module")
def observer(coverage_executable):
    with gas_coverage.open_bridge(coverage_executable) as bridge:
        yield bridge.request


def test_vendored_dao_transition(observer) -> None:
    cases = [
        case
        for case in catalogue.legacy_cases(gas_coverage.VENDORED_LEGACY)
        if case.fork == gas_coverage.DAO and case.group == gas_coverage.LEGACY_FORMAT
    ]
    report = gas_coverage.replay_cases(gas_coverage.VENDORED_LEGACY, cases, observer)
    # The four pinned sequences contain 20 accepted blocks before block 5 and 25 from block 5 on.
    assert len(cases) == 4
    assert report.failures == []
    assert {name: counts.blocks for name, counts in report.counts.items()} == {
        "homestead": 20,
        "daoFork": 25,
    }
    # Before the fork, four writes set a zero slot. From the fork, five writes pay the reset price.
    assert report.counts["homestead"].gas_rules["opcode.sstore.set-execution-charge"] == 4
    assert report.counts["daoFork"].gas_rules["opcode.sstore.reset-execution-charge"] == 5


def test_cli_reports_legacy_receipt_mismatch(coverage_executable, monkeypatch, capsys) -> None:
    read_fixture = legacy.fixture
    case = next(
        case
        for case in gas_coverage.source_cases(gas_coverage.LEGACY, catalogue.LEGACY)
        if case.fork == gas_coverage.DAO and case.path.endswith("/DaoTransactions.json")
    )

    def fixture_with_receipt(root, selected):
        fixture = read_fixture(root, selected)
        if selected != case:
            return fixture
        fixture = deepcopy(fixture)
        # The legacy fixture pins the receipt root but gives no encoded receipts.
        # Its first block has one transaction, so supply one incorrect receipt to test the check.
        fixture["blocks"][0]["receipts"] = [{"rlp": "0x00"}]
        return fixture

    monkeypatch.setattr(legacy, "fixture", fixture_with_receipt)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "gas_coverage",
            "--suite",
            gas_coverage.LEGACY,
            "--network",
            gas_coverage.DAO,
            "--executable",
            str(coverage_executable),
        ],
    )
    with raises(SystemExit, "1"):
        gas_coverage.main()
    failure = (
        f"| {case.suite} | `{case.id}` | {case.fork} | {case.group} | "
        "block receipt 0 bytes differ |"
    )
    assert failure in capsys.readouterr().out.splitlines()


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


@pytest.mark.archive(catalogue.EXECUTION, SSTORE_RESTORATION)
def test_pinned_sstore_restores_a_new_slot(archive, observer) -> None:
    (name,) = json.loads((archive / SSTORE_RESTORATION).read_text())
    case = Case("execution-spec-tests", "", "Amsterdam", "state_test", name, SSTORE_RESTORATION)
    counts = gas_coverage.replay_state(archive, case, observer)["glamsterdam"]
    # The two writes move the same slot from 0 to 1 and back to 0.
    assert {
        rule: count for rule, count in counts.gas_rules.items() if rule.startswith("opcode.sstore.")
    } == {
        "opcode.sstore.sentry-passed": 2,
        "opcode.sstore.cold": 1,
        "opcode.sstore.warm": 1,
        "opcode.sstore.clean-write-execution-charge": 1,
        "opcode.sstore.dirty-write": 1,
        "opcode.sstore.new-slot-state-charge": 1,
        "opcode.sstore.clear-new-slot-state-refill": 1,
        "opcode.sstore.restore-original-refund": 1,
    }


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
    case = transition_case(archive)
    fixture = json.loads((archive / case.path).read_text())[case.id]
    root = bytes.fromhex(fixture["blocks"][-1]["blockHeader"][field][2:])
    corrupted = bytes([root[0] ^ 1]) + root[1:]

    def corrupt_amsterdam(payload):
        if payload["fork"] == "glamsterdam":
            block = rlp.decode(bytes.fromhex(payload["block"]))
            block[0][runners.HEADER_FIELDS.index(field)] = corrupted
            payload = {**payload, "block": rlp.encode(block).hex()}
        return observer(payload)

    report = gas_coverage.replay_cases(archive, [case], corrupt_amsterdam)
    assert report.counts == {}
    message = f"block invalid: {error} (expected := 0x{corrupted.hex()}) (actual := 0x{root.hex()})"
    assert report.failures == [(case, message)]


def test_complete_inventory_at_each_execution_fork(observer) -> None:
    # The labels name the decisions in the Yellow Paper's fee schedule and the fork EIPs below.
    expected: set[str] = set(
        """
        opcode.fixed-price.0 opcode.fixed-price.1 opcode.fixed-price.2 opcode.fixed-price.3
        opcode.fixed-price.5 opcode.fixed-price.8 opcode.fixed-price.10 opcode.fixed-price.20
        opcode.memory.within-size opcode.memory.expand opcode.copy.zero-length opcode.copy.per-word
        opcode.keccak256.zero-length opcode.keccak256.per-word
        opcode.exp.zero-exponent opcode.exp.per-exponent-byte
        opcode.log.per-topic opcode.log.zero-data opcode.log.per-data-byte
        opcode.sload.fixed-price opcode.sstore.set-execution-charge
        opcode.sstore.reset-execution-charge opcode.sstore.clear-refund-credit
        opcode.call.value-charge opcode.call.new-account-execution-charge opcode.call.value-stipend
        opcode.call.requested-gas-grant opcode.call.grant-returned-without-child
        opcode.create.gas-grant opcode.create.grant-spent-on-collision
        opcode.create.skipped-before-grant opcode.selfdestruct.refund-credit
        transaction.base.fixed transaction.data.zero-byte transaction.data.nonzero-byte
        transaction.refund.none transaction.refund.below-cap transaction.refund.at-cap
    """.split()
    )
    phases = [
        ("frontier", "", ""),
        # EIP-2 adds the base for a transaction that creates a contract.
        ("homestead", "transaction.creation.base", ""),
        ("daoFork", "", ""),
        # EIP-150 reprices BALANCE and EXTCODESIZE, caps grants and prices new accounts.
        (
            "tangerineWhistle",
            "opcode.fixed-price.400 opcode.fixed-price.700 opcode.call.capped-gas-grant "
            "opcode.selfdestruct.new-account-execution-charge",
            "",
        ),
        ("spuriousDragon", "", ""),
        ("byzantium", "", ""),
        # EIP-1014 adds the init-code hash charge.
        ("constantinople", "opcode.create2.init-code-hash-per-word", ""),
        ("petersburg", "", ""),
        # EIP-1884 retires the 400-gas tier, and EIP-2200 adds net SSTORE metering.
        (
            "istanbul",
            "opcode.sstore.sentry-passed opcode.sstore.unchanged opcode.sstore.dirty-write "
            "opcode.sstore.clear-refund-debit opcode.sstore.restore-original-refund",
            "opcode.fixed-price.400",
        ),
        ("muirGlacier", "", ""),
        # EIP-2929 prices warm and cold accesses, and EIP-2930 adds access lists.
        (
            "berlin",
            "opcode.account-read.warm opcode.account-read.cold opcode.sload.warm opcode.sload.cold "
            "opcode.sstore.warm opcode.sstore.cold opcode.call.warm-target opcode.call.cold-target "
            "opcode.selfdestruct.warm-beneficiary opcode.selfdestruct.cold-beneficiary-surcharge "
            "transaction.access-list.address transaction.access-list.storage-key",
            "opcode.fixed-price.700 opcode.sload.fixed-price",
        ),
        # EIP-3529 removes the SELFDESTRUCT refund.
        ("london", "", "opcode.selfdestruct.refund-credit"),
        ("arrowGlacier", "", ""),
        ("grayGlacier", "", ""),
        ("paris", "", ""),
        # EIP-3860 prices init code separately.
        ("shapella", "opcode.create.init-code-per-word transaction.creation.initcode", ""),
        # EIP-1153 prices TLOAD and TSTORE at 100.
        ("dencun", "opcode.fixed-price.100", ""),
        # EIP-7702 adds authorizations and delegation, and EIP-7623 adds the calldata floor.
        (
            "pectra",
            "opcode.call.warm-delegate opcode.call.cold-delegate transaction.authorizations "
            "transaction.calldata-floor.at-floor transaction.calldata-floor.above-floor",
            "",
        ),
        ("fusaka", "", ""),
        ("bpo1", "", ""),
        ("bpo2", "", ""),
        ("bpo3", "", ""),
        ("bpo4", "", ""),
        ("bpo5", "", ""),
        # EIP-2780, EIP-7981, EIP-8037 and EIP-8038 split base, access and state creation charges.
        (
            "glamsterdam",
            "opcode.external-code.read-charge opcode.sstore.clean-write-execution-charge "
            "opcode.sstore.new-slot-state-charge opcode.sstore.clear-new-slot-state-refill "
            "opcode.call.new-account-state-charge opcode.create.new-account-state-charge "
            "opcode.selfdestruct.new-account-state-charge transaction.base.creation "
            "transaction.base.self transaction.base.other-no-value transaction.base.other-value "
            "transaction.access-list.data",
            "opcode.sstore.set-execution-charge opcode.sstore.reset-execution-charge "
            "opcode.call.new-account-execution-charge transaction.base.fixed "
            "transaction.creation.base",
        ),
    ]
    index = -1
    for fork, added, removed in phases:
        expected.difference_update(removed.split())
        expected.update(added.split())
        observed = observer({"kind": "inventory", "fork": fork})
        assert len(observed["gasRules"]) == len(expected), fork
        assert set(observed["gasRules"]) == expected, fork
        assert observed["forkIndex"] > index, fork
        index = observed["forkIndex"]


@pytest.mark.archive(catalogue.EXECUTION, BERLIN_CALL, AMSTERDAM_CALL)
def test_skipped_calls_report_the_paid_grant(archive, observer) -> None:
    # The Berlin caller requests GAS. The Amsterdam caller first requests zero, then 12106.
    for network, fork, path, requested, capped in (
        ("Berlin", "berlin", BERLIN_CALL, 0, 1),
        ("Amsterdam", "glamsterdam", AMSTERDAM_CALL, 2, 0),
    ):
        (name,) = json.loads((archive / path).read_text())
        case = Case("execution-spec-tests", "", network, "state_test", name, path)
        rules = gas_coverage.replay_state(archive, case, observer)[fork].gas_rules
        assert rules["opcode.call.grant-returned-without-child"] == 1
        assert rules["opcode.call.requested-gas-grant"] == requested
        assert rules["opcode.call.capped-gas-grant"] == capped


@pytest.mark.archive(catalogue.EXECUTION, AMSTERDAM_JUMPDEST, DENCUN_TLOAD)
def test_fixed_prices_are_counted_separately(archive, observer) -> None:
    # JUMPDEST costs 1, and TLOAD and TSTORE cost 100 under EIP-1153.
    for network, fork, path, transient_accesses in (
        ("Amsterdam", "glamsterdam", AMSTERDAM_JUMPDEST, 0),
        ("Cancun", "dencun", DENCUN_TLOAD, 3),
    ):
        (name,) = json.loads((archive / path).read_text())
        case = Case("execution-spec-tests", "", network, "state_test", name, path)
        rules = gas_coverage.replay_state(archive, case, observer)[fork].gas_rules
        assert rules["opcode.fixed-price.1"] == 1
        assert rules["opcode.fixed-price.100"] == transient_accesses
        assert rules["opcode.fixed-price.20"] == 0


@pytest.mark.archive(catalogue.EXECUTION, TRANSITION)
def test_corrupt_pinned_receipt_discards_events(archive, observer, monkeypatch) -> None:
    case = transition_case(archive)
    fixtures = json.loads((archive / case.path).read_text())
    fixtures[case.id]["blocks"][-1]["receipts"][0]["rlp"] = "0x00"
    monkeypatch.setattr(runners, "_fixtures", lambda _path: fixtures)
    report = gas_coverage.replay_cases(archive, [case], observer)
    assert report.counts == {}
    assert report.failures == [(case, "block receipt 0 bytes differ")]
