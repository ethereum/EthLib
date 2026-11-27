"""The opcode report counts trace steps and lists missed opcodes apart from undefined bytes."""

import json
from collections import Counter
from pathlib import PurePosixPath

import pytest

from ethlib.execution import transactions
from ethlib.serialization import rlp
from transactions.test_eip3155 import ENV, STATE, TX

from .catalogue import Case
from .opcode_coverage import opcode_inventory, render_fork, select_cases, traced_opcodes

GROUP = PurePosixPath("fixtures/state_tests/group")

# Five defined opcodes, of which the trace reaches two, with distinct counts everywhere.
OPCODES = {0x55: "SSTORE", 0x00: "STOP", 0x60: "PUSH1", 0x01: "ADD", 0x4B: "SLOTNUM"}


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
