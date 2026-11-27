"""The opcode report counts trace steps and lists missed opcodes apart from undefined bytes."""

from collections import Counter
from pathlib import PurePosixPath

import pytest

from raising import raises

from .catalogue import EXECUTION, Case
from .opcode_coverage import parse_opcodes, render_report, select_cases, traced_opcodes

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
    report = render_report(GROUP, OPCODES, counts, traced=3, rejected=1)
    assert report == "\n".join(
        [
            "# Amsterdam opcode coverage",
            "",
            f"Fixture group `{GROUP}` from `{EXECUTION}`.",
            "Observed **2 of 5** defined opcodes.",
            "",
            "| Measure | Count |",
            "| --- | ---: |",
            "| Traced cases | 3 |",
            "| Cases skipped for expected transaction errors | 1 |",
            "| Trace steps | 11 |",
            "",
            "Counts include faulting steps and the implicit `STOP` at the end of code.",
            "The table lists the opcodes that EthLib defines at Amsterdam, with their trace names.",
            "",
            "## Observed opcodes (2)",
            "",
            "| Byte | Opcode | Steps |",
            "| --- | --- | ---: |",
            "| `0x4b` | `SLOTNUM` | 1 |",
            "| `0x60` | `PUSH1` | 3 |",
            "",
            "## Missed opcodes (3)",
            "",
            "| Byte | Opcode |",
            "| --- | --- |",
            "| `0x00` | `STOP` |",
            "| `0x01` | `ADD` |",
            "| `0x55` | `SSTORE` |",
            "",
            "## Undefined bytes reached",
            "",
            "| Byte | Steps |",
            "| --- | ---: |",
            "| `0x0c` | 5 |",
            "| `0xfe` | 2 |",
        ]
    )


def test_report_without_undefined_bytes_ends_at_the_missed_table() -> None:
    """The undefined section appears only when the trace reaches an undefined byte."""
    report = render_report(GROUP, OPCODES, Counter({0x60: 2}), traced=1, rejected=0)
    assert report.endswith("| `0x55` | `SSTORE` |")
    assert "Undefined" not in report


def test_parse_opcodes() -> None:
    """Each line gives a decimal byte and its mnemonic."""
    assert parse_opcodes("0\tSTOP\n75\tSLOTNUM\n") == {0x00: "STOP", 0x4B: "SLOTNUM"}


@pytest.mark.parametrize(
    "line",
    [
        "warning: declaration uses 'sorry'",
        "0x60\tPUSH1",
        "256\tPUSH1",
        "96\t",
    ],
)
def test_parse_opcodes_rejects_other_lines(line: str) -> None:
    """A diagnostic or a malformed line stops the report instead of corrupting the table."""
    message = f"not an opcode line of scripts/AmsterdamOpcodes.lean: {line!r}"
    with raises(ValueError, message):
        parse_opcodes(f"0\tSTOP\n{line}\n")


def test_select_cases() -> None:
    """Only Amsterdam state tests in a file below the group directory are kept."""

    def case(fork: str, group: str, path: str) -> Case:
        return Case("execution-spec-tests", "", fork, group, "id", path)

    inside = case("Amsterdam", "state_test", f"{GROUP}/sub/test.json")
    cases = [
        inside,
        case("Osaka", "state_test", f"{GROUP}/test.json"),
        case("Amsterdam", "blockchain_test", f"{GROUP}/test.json"),
        case("Amsterdam", "state_test", f"{GROUP}_other/test.json"),
        case("Amsterdam", "state_test", str(GROUP)),
    ]
    assert select_cases(cases, GROUP) == [inside]
