"""Check the gas report and its classification of pinned branch witnesses."""

import json
import subprocess
import sys
from collections import Counter
from io import StringIO
from pathlib import Path, PurePosixPath

import pytest

from ethlib.serialization import rlp
from raising import raises

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


def test_report_lists_each_named_branch() -> None:
    inventory = {"gasRules": ["opcode.sload.warm", "opcode.sload.cold", "opcode.memory.expand"]}
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


@pytest.mark.parametrize(
    ("reply", "error"),
    [
        ("", "gas-coverage stopped before replying to the inventory request for berlin"),
        ("!\n", "gas-coverage returned invalid JSON for the inventory request for berlin"),
        ("[]\n", "gas-coverage returned a non-object reply to the inventory request for berlin"),
        (
            '{"error":0}\n',
            "gas-coverage returned an invalid error for the inventory request for berlin",
        ),
    ],
)
def test_bridge_diagnostics(reply, error) -> None:
    bridge = gas_coverage.Bridge(StringIO(), StringIO(reply))
    with raises(RuntimeError, error):
        bridge.request({"kind": "inventory", "fork": "berlin"})


def test_reject_duplicate_inventory_and_invalid_event_counts() -> None:
    with raises(RuntimeError, "duplicate gas rules in the berlin inventory"):
        gas_coverage.render_fork("berlin", {"gasRules": ["warm", "warm"]}, gas_coverage.Counts())
    for invalid in (["warm"], {"warm": -1}, {"warm": 0}, {"warm": True}):
        with raises(RuntimeError, "gas-coverage returned invalid gas event counts"):
            gas_coverage.gas_events({"gasRules": invalid})


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
    assert report.counts == {"glamsterdam": gas_coverage.Counts()}
    lines = gas_coverage.render_fork(
        "glamsterdam", {"gasRules": ["opcode.sload.warm"]}, report.counts["glamsterdam"]
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
    response = {"state": "01", "gasRules": {"opcode.sload.cold": 1}}
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
def observer():
    if not gas_coverage.EXECUTABLE.is_file():
        pytest.skip("build the fixture runner with lake build gas-coverage")
    with gas_coverage.open_bridge(gas_coverage.EXECUTABLE) as bridge:
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


@pytest.mark.archive(catalogue.EXECUTION, TRANSITION)
@pytest.mark.parametrize(
    ("expected", "accepted"),
    [("RLP_STRUCTURES_ENCODING", True), ("INVALID_WITHDRAWALS_ROOT", False)],
)
def test_malformed_block_requires_its_pinned_error(
    archive, observer, monkeypatch, expected, accepted
):
    case = transition_case(archive)
    fixtures = json.loads((archive / case.path).read_text())
    fixtures[case.id]["blocks"].append(
        {"rlp": "0xc0", "expectException": f"BlockException.{expected}"}
    )
    monkeypatch.setattr(runners, "_fixtures", lambda _path: fixtures)
    report = gas_coverage.replay_cases(archive, [case], observer)
    if accepted:
        assert report.failures == []
        assert {fork: counts.blocks for fork, counts in report.counts.items()} == {
            "bpo2": 1,
            "glamsterdam": 1,
        }
    else:
        assert report.counts == {}
        ((failed, message),) = report.failures
        assert failed == case
        assert expected in message and "block invalid: encoding" in message
