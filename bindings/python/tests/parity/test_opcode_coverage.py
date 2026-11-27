"""The opcode report probes each fork's inventory and counts the steps of its state tests."""

import json
from collections import Counter
from collections.abc import Callable
from pathlib import PurePosixPath
from types import SimpleNamespace
from typing import TypeAlias

import pytest

from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises
from transactions.test_eip3155 import ENV, STATE, TX
from transactions.test_transactions import FORK_OF_NETWORK

from . import opcode_coverage
from .catalogue import Case
from .opcode_coverage import opcode_inventory, render_fork, select_cases, traced_opcodes

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


def test_traced_opcodes() -> None:
    """Every step counts, faulting or not, and the summary line does not."""
    trace = [
        '{"op":96,"opName":"PUSH1"}',
        '{"op":96,"opName":"PUSH1"}',
        '{"op":75,"opName":"SLOTNUM","error":"stack overflow"}',
        '{"op":12,"opName":"INVALID","error":"invalid opcode"}',
        '{"op":254,"opName":"INVALID","error":"invalid opcode"}',
        '{"output":"0x","pass":false}',
    ]
    assert traced_opcodes(trace) == Counter({0x60: 2, 0x4B: 1, 0x0C: 1, 0xFE: 1})


def test_traced_opcodes_of_a_summary_only() -> None:
    """A trace without steps counts nothing."""
    assert traced_opcodes(['{"output":"0x","pass":true}']) == Counter()


def test_report_lists_missed_and_undefined_bytes_separately() -> None:
    """The report sorts each table by byte and gives each undefined byte its own count."""
    counts = Counter({0x60: 3, 0xFE: 2, 0x4B: 1, 0x0C: 5})
    report = render_fork("Amsterdam", OPCODES, counts, traced=3, rejected=1)
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
            "| Byte | Opcode | Steps |",
            "| --- | --- | ---: |",
            "| `0x4b` | `SLOTNUM` | 1 |",
            "| `0x60` | `PUSH1` | 3 |",
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
            "| Byte | Steps |",
            "| --- | ---: |",
            "| `0x0c` | 5 |",
            "| `0xfe` | 2 |",
        ]
    )


def test_report_sorts_undefined_bytes_by_byte() -> None:
    """The undefined table follows the byte, not the step count."""
    counts = Counter({0x60: 3, 0x4B: 1, 0xFE: 5, 0x0C: 2, 0x21: 1})
    report = render_fork("Amsterdam", OPCODES, counts, traced=1, rejected=0)
    assert report.endswith(
        "\n".join(
            [
                "### Undefined bytes reached",
                "",
                "| Byte | Steps |",
                "| --- | ---: |",
                "| `0x0c` | 2 |",
                "| `0x21` | 1 |",
                "| `0xfe` | 5 |",
            ]
        )
    )


def test_report_without_undefined_bytes_ends_at_the_missed_table() -> None:
    """The undefined section appears only when the trace reaches an undefined byte."""
    report = render_fork("Amsterdam", OPCODES, Counter({0x60: 2}), traced=1, rejected=0)
    assert report.endswith("| `0x55` | `SSTORE` |")
    assert "Undefined" not in report


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
    assert traced_opcodes(trace) == Counter(byte for byte, _ in expected)


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
