"""The opcode report counts trace steps and distinguishes missing and undefined bytes."""

from collections import Counter
from pathlib import PurePosixPath

from .opcode_coverage import render_report, traced_opcodes


def test_traced_opcodes() -> None:
    trace = [
        '{"op":96,"opName":"PUSH1"}',
        '{"op":96,"opName":"PUSH1"}',
        '{"op":75,"opName":"SLOTNUM","error":"stack overflow"}',
        '{"op":12,"opName":"INVALID","error":"invalid opcode"}',
        '{"op":254,"opName":"INVALID","error":"invalid opcode"}',
        '{"output":"0x","pass":false}',
    ]
    assert traced_opcodes(trace) == Counter({0x60: 2, 0x4B: 1, 0x0C: 1, 0xFE: 1})
    assert traced_opcodes(['{"output":"0x","pass":true}']) == Counter()


def test_report_lists_missed_and_undefined_bytes_separately() -> None:
    report = render_report(
        PurePosixPath("fixtures/state_tests/group"),
        {0x00: "STOP", 0x4B: "SLOTNUM", 0x60: "PUSH1"},
        Counter({0x60: 2, 0x4B: 1, 0xFE: 1}),
        traced=1,
        rejected=1,
    )
    assert "Observed **2 of 3** defined opcodes." in report
    assert "| Traced cases | 1 |" in report
    assert "| Cases skipped for expected transaction errors | 1 |" in report
    assert "| Trace steps | 4 |" in report
    assert "## Observed opcodes (2)" in report
    assert "| `0x4b` | `SLOTNUM` | 1 |\n| `0x60` | `PUSH1` | 2 |" in report
    assert "## Missed opcodes (1)" in report
    assert "| `0x00` | `STOP` |" in report
    assert "## Undefined bytes reached" in report
    assert "| `0xfe` | 1 |" in report
