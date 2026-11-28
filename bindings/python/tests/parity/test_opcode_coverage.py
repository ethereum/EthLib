"""The opcode report probes each fork's inventory and the steps, gas and memory of its tests."""

import json
import sys
from collections import defaultdict
from collections.abc import Callable
from pathlib import Path, PurePosixPath
from types import SimpleNamespace
from typing import TypeAlias

import pytest

from ethlib.cryptography.secp256k1 import address
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises
from transactions.test_check_order import KEY, OTHER, _fee_market, _int
from transactions.test_eip3155 import ENV, STATE, TX
from transactions.test_transactions import CHAIN_ID, FORK_OF_NETWORK

from . import opcode_coverage
from .catalogue import Case
from .opcode_coverage import OpcodeStats, opcode_inventory, record_trace, render_fork, select_cases

GROUP = PurePosixPath("fixtures/state_tests/group")

# Five defined opcodes, of which the trace reaches two, with distinct counts everywhere.
OPCODES = {0x55: "SSTORE", 0x00: "STOP", 0x60: "PUSH1", 0x01: "ADD", 0x4B: "SLOTNUM"}

# The bytes defined at Frontier, from Appendix H.2 of the Yellow Paper.
FRONTIER = {
    *range(0x00, 0x0C),
    *range(0x10, 0x1B),
    0x20,
    *range(0x30, 0x3D),
    *range(0x40, 0x46),
    *range(0x50, 0x5C),
    *range(0x60, 0xA5),
    *range(0xF0, 0xF4),
    0xFF,
}

# The bytes that each fork adds, from its EIPs; a fork absent here adds none.
ADDED = {
    "homestead": {0xF4},  # EIP-7
    "byzantium": {0x3D, 0x3E, 0xFA, 0xFD},  # EIP-211, EIP-214, EIP-140
    "petersburg": {0x1B, 0x1C, 0x1D, 0x3F, 0xF5},  # EIP-145, EIP-1052, EIP-1014
    "istanbul": {0x46, 0x47},  # EIP-1344, EIP-1884
    "london": {0x48},  # EIP-3198
    "shapella": {0x5F},  # EIP-3855
    "dencun": {0x49, 0x4A, 0x5C, 0x5D, 0x5E},  # EIP-4844, EIP-7516, EIP-1153, EIP-5656
    "fusaka": {0x1E},  # EIP-7939
    "glamsterdam": {0x4B, 0xE6, 0xE7, 0xE8},  # EIP-7843, EIP-8024
}

# A stub tracer defines these bytes; ADD and SELFDESTRUCT fault on the empty stack.
STUB = {
    0x00: ("STOP", None),
    0x01: ("ADD", "stack underflow"),
    0x5B: ("JUMPDEST", None),
    0xFF: ("SELFDESTRUCT", "stack underflow"),
}

Step: TypeAlias = dict[str, object]
Edit: TypeAlias = Callable[[int, list[Step]], list[Step]]


def _stub_tracer(edit: Edit) -> SimpleNamespace:
    """A tracer of the one-byte probes from the stub table, with an edit of the probe steps."""

    def trace(fork: str, chain_id: int, tx: bytes, state: bytes, env: bytes) -> list[str]:
        (byte,) = rlp.decode(state)[1][3]
        name, error = STUB.get(byte, ("INVALID", "invalid opcode"))
        steps: list[Step] = [{"pc": 0, "op": byte, "depth": 1, "opName": name}]
        if error is not None:
            steps[0]["error"] = error
        if byte == 0x5B:
            steps.append({"pc": 1, "op": 0x00, "depth": 1, "opName": "STOP"})
        summary = '{"output":"0x","pass":true}'
        return [json.dumps(step) for step in edit(byte, steps)] + [summary]

    return SimpleNamespace(trace_eip3155=trace)


def _unchanged(byte: int, steps: list[Step]) -> list[Step]:
    """Keep the probe steps of every byte."""
    return steps


def _no_steps(byte: int, steps: list[Step]) -> list[Step]:
    """Drop every step, leaving only the summary line."""
    return []


def _first(**fields: object) -> Edit:
    """Change fields of the first step of the probe of byte 0x00."""
    return lambda byte, steps: [{**steps[0], **fields}] if byte == 0x00 else steps


def _without(key: str) -> Edit:
    """Remove one field of the first step of the probe of byte 0x00."""
    return lambda byte, steps: (
        [{k: v for k, v in steps[0].items() if k != key}] if byte == 0x00 else steps
    )


def test_record_trace_counts_distinct_costs_and_out_of_gas() -> None:
    """Faulting steps count without a gas cost, and give a memory snapshot to the step before."""
    stats: defaultdict[int, OpcodeStats] = defaultdict(OpcodeStats)
    record_trace(
        stats,
        [
            '{"op":96,"gasCost":"0x3","memSize":0,"depth":1}',
            '{"op":96,"gasCost":"0x3","memSize":0,"depth":1}',
            '{"op":83,"gasCost":"0x6","memSize":0,"depth":1}',
            '{"op":254,"gas":"0x10","gasCost":"0x10","memSize":32,"depth":1,'
            '"error":"invalid opcode"}',
            '{"output":"0x","pass":false}',
        ],
    )
    fault = [
        '{"op":96,"gas":"0x2","gasCost":"0x2","memSize":0,"depth":1,"error":"out of gas"}',
        '{"output":"0x","pass":false}',
    ]
    record_trace(stats, fault)
    record_trace(stats, fault)
    # A fault other than running out of gas adds neither a cost nor an out-of-gas step.
    underflow = (
        '{"op":1,"gas":"0x5","gasCost":"0x5","memSize":0,"depth":1,"error":"stack underflow"}'
    )
    record_trace(stats, [underflow, '{"output":"0x","pass":false}'])
    assert stats == {
        0x60: OpcodeStats(steps=4, gas_costs={3}, memory_growth={0}, out_of_gas=2),
        0x01: OpcodeStats(steps=1),
        0x53: OpcodeStats(steps=1, gas_costs={6}, memory_growth={32}),
        0xFE: OpcodeStats(steps=1),
    }


def test_record_trace_of_a_summary_only() -> None:
    """A trace without steps counts nothing."""
    stats: defaultdict[int, OpcodeStats] = defaultdict(OpcodeStats)
    record_trace(stats, ['{"output":"0x","pass":true}'])
    assert not stats


def test_memory_growth_in_nested_calls() -> None:
    """Each call has its own memory and the caller's growth is visible when it resumes."""
    callee = bytes(19) + b"\x30"
    # Pass 64 input bytes and 256 gas in the first STATICCALL, then 96 bytes and 7 gas.
    caller_code = bytes.fromhex("60006000604060006030610100fa50 600060006060600060306007fa00")
    # Write at offset 64 with MSTORE8 and return one byte at offset 96.
    callee_code = bytes.fromhex("6001604053 60016060f3")
    state = rlp.encode(
        [
            [address(KEY), b"", _int(10**18), b"", []],
            [OTHER, b"", b"", caller_code, []],
            [callee, b"", b"", callee_code, []],
        ]
    )
    trace = transactions.trace_eip3155("pectra", 1, TX, state, ENV)
    assert json.loads(trace[-1])["pass"] is True

    stats: defaultdict[int, OpcodeStats] = defaultdict(OpcodeStats)
    record_trace(stats, trace)
    assert stats == {
        # The caller runs 5 and 6 PUSH1 steps, and the callees 4 and 2.
        0x60: OpcodeStats(steps=17, gas_costs={3}, memory_growth={0}),
        0x61: OpcodeStats(steps=1, gas_costs={3}, memory_growth={0}),
        # Account access costs 2600 and 100 (EIP-2929, Storage read changes).
        # Memory costs 6 and 3 (Yellow Paper H.1), and the calls pass 256 and 7 gas.
        0xFA: OpcodeStats(steps=2, gas_costs={2862, 110}, memory_growth={32, 64}),
        0x50: OpcodeStats(steps=1, gas_costs={2}, memory_growth={0}),
        # The STOP that ends the caller is the last step of its frame.
        0x00: OpcodeStats(steps=1, gas_costs={0}),
        # MSTORE8 costs 3 plus 9 for memory (Yellow Paper H.1).
        # In the second call two PUSH1s leave 1 of the 7 gas, so MSTORE8 runs out of gas.
        0x53: OpcodeStats(steps=2, gas_costs={12}, memory_growth={96}, out_of_gas=1),
        # RETURN pays 3 for the fourth word of memory and ends its frame.
        0xF3: OpcodeStats(steps=1, gas_costs={3}),
    }


def test_report_lists_missed_and_undefined_bytes_separately() -> None:
    """The report sorts each table by byte and gives each undefined byte its own count."""
    stats = {
        0x60: OpcodeStats(steps=3, gas_costs={3, 8}, memory_growth={1, 8}, out_of_gas=1),
        0xFE: OpcodeStats(steps=2),
        0x4B: OpcodeStats(steps=1, gas_costs={2}, memory_growth={0}),
        0x0C: OpcodeStats(steps=5),
    }
    report = render_fork("Amsterdam", OPCODES, stats, traced=3, rejected=1)
    assert report == "\n".join(
        [
            "## Amsterdam",
            "",
            "Observed **2 of 5** defined opcodes.",
            "",
            "| Measure | Count |",
            "| --- | ---: |",
            "| Traced cases | 3 |",
            "| Cases skipped for expected transaction errors | 1 |",
            "| Trace steps | 11 |",
            "",
            "### Observed opcodes (2)",
            "",
            "| Byte | Opcode | Steps | Gas costs | Memory growth (bytes) | Out of gas |",
            "| --- | --- | ---: | ---: | ---: | ---: |",
            "| `0x4b` | `SLOTNUM` | 1 | 2 | 0 | 0 |",
            "| `0x60` | `PUSH1` | 3 | 3, 8 | 1, 8 | 1 |",
            "",
            "### Missed opcodes (3)",
            "",
            "| Byte | Opcode |",
            "| --- | --- |",
            "| `0x00` | `STOP` |",
            "| `0x01` | `ADD` |",
            "| `0x55` | `SSTORE` |",
            "",
            "### Undefined bytes reached",
            "",
            "| Byte | Steps | Gas costs | Memory growth (bytes) | Out of gas |",
            "| --- | ---: | ---: | ---: | ---: |",
            "| `0x0c` | 5 | - | - | 0 |",
            "| `0xfe` | 2 | - | - | 0 |",
        ]
    )


def amsterdam_report(observed: list[str], missed: list[str], undefined: list[str]) -> str:
    """The whole report of one fork of OPCODES with one traced case and one step per row."""
    lines = [
        "## Amsterdam",
        "",
        f"Observed **{len(observed)} of 5** defined opcodes.",
        "",
        "| Measure | Count |",
        "| --- | ---: |",
        "| Traced cases | 1 |",
        "| Cases skipped for expected transaction errors | 0 |",
        f"| Trace steps | {len(observed) + len(undefined)} |",
        "",
        f"### Observed opcodes ({len(observed)})",
        "",
        "| Byte | Opcode | Steps | Gas costs | Memory growth (bytes) | Out of gas |",
        "| --- | --- | ---: | ---: | ---: | ---: |",
        *observed,
        "",
        f"### Missed opcodes ({len(missed)})",
        "",
        "| Byte | Opcode |",
        "| --- | --- |",
        *missed,
    ]
    if undefined:
        lines += [
            "",
            "### Undefined bytes reached",
            "",
            "| Byte | Steps | Gas costs | Memory growth (bytes) | Out of gas |",
            "| --- | ---: | ---: | ---: | ---: |",
            *undefined,
        ]
    return "\n".join(lines)


def test_report_sorts_undefined_bytes_by_byte() -> None:
    """The undefined table follows the byte, not the order in which the trace reached it."""
    stats = {
        0x60: OpcodeStats(steps=1, gas_costs={3}),
        0xFE: OpcodeStats(steps=1),
        0x0C: OpcodeStats(steps=1),
        0x21: OpcodeStats(steps=1),
    }
    report = render_fork("Amsterdam", OPCODES, stats, traced=1, rejected=0)
    assert report == amsterdam_report(
        ["| `0x60` | `PUSH1` | 1 | 3 | - | 0 |"],
        [
            "| `0x00` | `STOP` |",
            "| `0x01` | `ADD` |",
            "| `0x4b` | `SLOTNUM` |",
            "| `0x55` | `SSTORE` |",
        ],
        ["| `0x0c` | 1 | - | - | 0 |", "| `0x21` | 1 | - | - | 0 |", "| `0xfe` | 1 | - | - | 0 |"],
    )


def test_report_without_undefined_bytes_ends_at_the_missed_table() -> None:
    """The undefined section appears only when the trace reaches an undefined byte."""
    stats = {0x60: OpcodeStats(steps=1, gas_costs={3}, memory_growth={0})}
    report = render_fork("Amsterdam", OPCODES, stats, traced=1, rejected=0)
    assert report == amsterdam_report(
        ["| `0x60` | `PUSH1` | 1 | 3 | 0 | 0 |"],
        [
            "| `0x00` | `STOP` |",
            "| `0x01` | `ADD` |",
            "| `0x4b` | `SLOTNUM` |",
            "| `0x55` | `SSTORE` |",
        ],
        [],
    )


@pytest.mark.parametrize(
    ("fork", "name", "slotnum"),
    [
        ("london", "DIFFICULTY", False),
        ("paris", "PREVRANDAO", False),
        ("glamsterdam", "PREVRANDAO", True),
    ],
)
def test_opcode_inventory_matches_trace_across_forks(fork: str, name: str, slotnum: bool) -> None:
    """The inventory and the trace agree on fork-dependent names and opcode activation."""
    accounts = rlp.decode(STATE)
    accounts[1][3] = bytes.fromhex("444bfe")
    trace = transactions.trace_eip3155(fork, 1, TX, rlp.encode(accounts), ENV)
    inventory = opcode_inventory(fork)

    assert inventory[0x44] == name
    assert 0xFE not in inventory
    expected = [(0x44, name)]
    if slotnum:
        assert inventory[0x4B] == "SLOTNUM"
        expected.extend(((0x4B, "SLOTNUM"), (0xFE, "INVALID")))
    else:
        assert 0x4B not in inventory
        expected.append((0x4B, "INVALID"))

    steps = [json.loads(line) for line in trace[:-1]]
    assert [(step["op"], step["opName"]) for step in steps] == expected
    stats: defaultdict[int, OpcodeStats] = defaultdict(OpcodeStats)
    record_trace(stats, trace)
    assert [(byte, opcode.steps) for byte, opcode in stats.items()] == [
        (byte, 1) for byte, _ in expected
    ]


def test_frontier_inventory_includes_opcodes_that_fault() -> None:
    """The legacy probe enters a Frontier block and recognizes ADD despite stack underflow."""
    inventory = opcode_inventory("frontier")

    assert inventory[0x01] == "ADD"
    assert 0x5F not in inventory
    assert 0xFE not in inventory


def test_inventory_bytes_follow_the_eips_fork_by_fork() -> None:
    """Each fork defines exactly the Frontier bytes and those that the EIPs add up to it."""
    defined = set(FRONTIER)
    for fork in FORK_OF_NETWORK.values():
        defined |= ADDED.get(fork, set())
        assert set(opcode_inventory(fork)) == defined, fork


def test_inventory_keeps_faulting_bytes_and_drops_invalid_ones(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Every byte is probed, and only a first step with an invalid opcode leaves the inventory."""
    monkeypatch.setattr(opcode_coverage, "transactions", _stub_tracer(_unchanged))
    assert opcode_inventory("london") == {
        0x00: "STOP",
        0x01: "ADD",
        0x5B: "JUMPDEST",
        0xFF: "SELFDESTRUCT",
    }


@pytest.mark.parametrize(
    ("edit", "message"),
    [
        (_no_steps, "london opcode probe 0x00 has no trace step"),
        (_first(pc=1), "london opcode probe 0x00 has an unexpected first step"),
        (_first(depth=2), "london opcode probe 0x00 has an unexpected first step"),
        (_first(op=0x01), "london opcode probe 0x00 has an unexpected first step"),
        (_without("opName"), "london opcode probe 0x00 has an inconsistent mnemonic"),
        (_first(opName=""), "london opcode probe 0x00 has an inconsistent mnemonic"),
        (_first(opName="INVALID"), "london opcode probe 0x00 has an inconsistent mnemonic"),
        (_first(error="invalid opcode"), "london opcode probe 0x00 has an inconsistent mnemonic"),
    ],
)
def test_inventory_rejects_a_malformed_probe(
    monkeypatch: pytest.MonkeyPatch, edit: Edit, message: str
) -> None:
    """A probe must start at pc 0 and depth 1 on its byte, with a name that matches its error."""
    monkeypatch.setattr(opcode_coverage, "transactions", _stub_tracer(edit))
    with raises(ValueError, message):
        opcode_inventory("london")


def test_select_cases() -> None:
    """State tests follow fork order and an optional directory limits the included files."""

    def case(fork: str, group: str, path: str) -> Case:
        return Case("execution-spec-tests", "", fork, group, "id", path)

    amsterdam = case("Amsterdam", "state_test", f"{GROUP}/sub/test.json")
    osaka = case("Osaka", "state_test", f"{GROUP}/test.json")
    frontier = case("Frontier", "state_test", f"{GROUP}/test.json")
    outside = case("Amsterdam", "state_test", f"{GROUP}_other/test.json")
    cases = [
        amsterdam,
        osaka,
        outside,
        case("Amsterdam", "blockchain_test", f"{GROUP}/test.json"),
        case("Amsterdam", "state_test", str(GROUP)),
        case("Bogota", "state_test", f"{GROUP}/test.json"),
        frontier,
    ]

    selected = select_cases(cases, GROUP)
    assert list(selected) == ["Frontier", "Osaka", "Amsterdam"]
    assert selected == {"Frontier": [frontier], "Osaka": [osaka], "Amsterdam": [amsterdam]}
    assert outside in select_cases(cases, None)["Amsterdam"]
    assert select_cases(cases, PurePosixPath("fixtures/empty")) == {}


def test_select_cases_keeps_every_case_of_a_file() -> None:
    """Two tests of one fixture file both count, and another runner group does not."""

    def case(group: str, name: str) -> Case:
        return Case("execution-spec-tests", "", "Osaka", group, name, f"{GROUP}/test.json")

    first, second = case("state_test", "first"), case("state_test", "second")
    cases = [first, case("state_test_engine", "first"), second]
    assert select_cases(cases, GROUP) == {"Osaka": [first, second]}


# Cancun follows Paris, so fork order differs from the order of the names.
CANCUN = Case("execution-spec-tests", "", "Cancun", "state_test", "ok", f"{GROUP}/test.json")
PARIS = Case("execution-spec-tests", "", "Paris", "state_test", "fault", f"{GROUP}/test.json")
REJECTED = (
    Case("execution-spec-tests", "", "Cancun", "state_test", "reject", f"{GROUP}/test.json"),
    Case("execution-spec-tests", "", "Cancun", "state_test", "refuse", f"{GROUP}/test.json"),
)

# A transfer with no data and no access list has intrinsic gas 21000 (Yellow Paper, Appendix G).
# With two gas left, PUSH1 runs out of gas at Paris before the implicit STOP.
LOW_GAS = _fee_market(CHAIN_ID, 21_002)

# Small inventories keep the whole report short.
INVENTORIES = {
    "paris": {0x00: "STOP", 0x60: "PUSH1", 0x44: "PREVRANDAO"},
    "dencun": {0x00: "STOP", 0x60: "PUSH1", 0x01: "ADD"},
}


def read_case(
    root: Path, case: Case
) -> tuple[tuple[str, int, bytes, bytes, bytes], dict[str, str]]:
    """The transaction of each case, with an expected error for each case of REJECTED."""
    fork = FORK_OF_NETWORK[case.fork]
    # A post entry always holds the hash of the state and the transaction bytes.
    post = {"hash": "0x" + "00" * 32, "txbytes": "0x"}
    if case in REJECTED:
        return (fork, CHAIN_ID, b"", STATE, ENV), {**post, "expectException": "invalid transaction"}
    return (fork, CHAIN_ID, TX if case == CANCUN else LOW_GAS, STATE, ENV), post


@pytest.mark.parametrize("group", [GROUP, None])
def test_main_reports_only_selected_transactions_by_fork(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    tmp_path: Path,
    group: PurePosixPath | None,
) -> None:
    """The report isolates each fork and excludes rejected transactions and inventory probes."""
    unpacked: list[tuple[str, list[Case]]] = []

    def unpack_read(name: str, cases: list[Case]) -> Path:
        unpacked.append((name, cases))
        return tmp_path

    def read_unpacked(
        root: Path, case: Case
    ) -> tuple[tuple[str, int, bytes, bytes, bytes], dict[str, str]]:
        assert root == tmp_path
        return read_case(root, case)

    argv = ["opcode_coverage"] if group is None else ["opcode_coverage", str(group)]
    monkeypatch.setattr(sys, "argv", argv)
    monkeypatch.setattr(opcode_coverage.archives, "CACHE", tmp_path)
    monkeypatch.setattr(
        opcode_coverage.catalogue,
        "execution_cases",
        lambda: [CANCUN, REJECTED[0], PARIS, REJECTED[1]],
    )
    monkeypatch.setattr(opcode_coverage.harness, "unpack_read", unpack_read)
    monkeypatch.setattr(opcode_coverage, "state_test_input", read_unpacked)
    monkeypatch.setattr(opcode_coverage, "opcode_inventory", INVENTORIES.__getitem__)
    opcode_coverage.main()

    execution = opcode_coverage.catalogue.EXECUTION
    assert unpacked == [(execution, [PARIS, CANCUN, *REJECTED])]
    source = (
        f"State tests from `{execution}`."
        if group is None
        else f"Fixture group `{GROUP}` from `{execution}`."
    )
    header = [
        "# EVM opcode coverage",
        source,
        "Each fork's opcode inventory comes from tracing all 256 one-byte programs.",
        "Counts include faulting steps and the implicit `STOP` at the end of code.",
        "Gas costs are the distinct `gasCost` values in decimal of the steps without a fault. "
        "A call or creation that starts a message counts the gas it passes on. "
        "From Amsterdam, `gasCost` counts only execution gas, "
        "without the state gas that the reservoir pays (EIP-8037). "
        "State gas beyond the reservoir comes from execution gas and counts.",
        "Memory growth lists the distinct changes of `memSize` from a step "
        "to the next step of the same call frame, so the last step of a frame has none. "
        "A zero records an observed step with no growth. "
        "A dash means there was no such measurement for that byte.",
        "Out-of-gas counts use the `out of gas` error on a trace step.",
    ]
    cancun = [
        "## Cancun",
        "",
        "Observed **2 of 3** defined opcodes.",
        "",
        "| Measure | Count |",
        "| --- | ---: |",
        "| Traced cases | 1 |",
        "| Cases skipped for expected transaction errors | 2 |",
        "| Trace steps | 2 |",
        "",
        "### Observed opcodes (2)",
        "",
        "| Byte | Opcode | Steps | Gas costs | Memory growth (bytes) | Out of gas |",
        "| --- | --- | ---: | ---: | ---: | ---: |",
        "| `0x00` | `STOP` | 1 | 0 | - | 0 |",
        "| `0x60` | `PUSH1` | 1 | 3 | 0 | 0 |",
        "",
        "### Missed opcodes (1)",
        "",
        "| Byte | Opcode |",
        "| --- | --- |",
        "| `0x01` | `ADD` |",
    ]
    paris = [
        "## Paris",
        "",
        "Observed **1 of 3** defined opcodes.",
        "",
        "| Measure | Count |",
        "| --- | ---: |",
        "| Traced cases | 1 |",
        "| Cases skipped for expected transaction errors | 0 |",
        "| Trace steps | 1 |",
        "",
        "### Observed opcodes (1)",
        "",
        "| Byte | Opcode | Steps | Gas costs | Memory growth (bytes) | Out of gas |",
        "| --- | --- | ---: | ---: | ---: | ---: |",
        "| `0x60` | `PUSH1` | 1 | - | - | 1 |",
        "",
        "### Missed opcodes (2)",
        "",
        "| Byte | Opcode |",
        "| --- | --- |",
        "| `0x00` | `STOP` |",
        "| `0x44` | `PREVRANDAO` |",
    ]
    sections = [*header, "\n".join(paris), "\n".join(cancun)]
    assert capsys.readouterr().out == "\n\n".join(sections) + "\n"


@pytest.mark.parametrize(
    ("argv", "message"),
    [
        ([], "set ETHLIB_ARCHIVES to the fixture archive cache directory"),
        ([], "no state tests"),
        ([str(GROUP)], f"no state tests under {GROUP}"),
    ],
)
def test_main_usage_errors(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    tmp_path: Path,
    argv: list[str],
    message: str,
) -> None:
    """Without an archive cache or a selected state test, the report stops with a usage error."""
    cache = None if message.startswith("set ") else tmp_path
    monkeypatch.setattr(sys, "argv", ["opcode_coverage", *argv])
    monkeypatch.setattr(opcode_coverage.archives, "CACHE", cache)
    monkeypatch.setattr(opcode_coverage.catalogue, "execution_cases", lambda: [])
    # The argparse usage error exits with status 2.
    with raises(SystemExit, "2"):
        opcode_coverage.main()
    assert capsys.readouterr().err == (
        f"usage: opcode_coverage [-h] [group]\nopcode_coverage: error: {message}\n"
    )
