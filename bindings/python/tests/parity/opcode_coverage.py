"""Report opcode coverage for a group of pinned Amsterdam state tests."""

import argparse
import json
import subprocess
from collections import Counter
from pathlib import PurePosixPath

import archives
from ethlib.execution import transactions

from . import catalogue, harness
from .runners import state_test_input


def _amsterdam_opcodes() -> dict[int, str]:
    """Read the opcode bytes and trace mnemonics from EthLib's Lean definitions."""
    listing = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/AmsterdamOpcodes.lean"],
        cwd=archives.REPO,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    return {int(byte): name for byte, name in (line.split("\t") for line in listing.splitlines())}


def traced_opcodes(trace: list[str]) -> Counter[int]:
    """Count opcode bytes in the trace steps before the transaction summary."""
    return Counter(json.loads(line)["op"] for line in trace[:-1])


def render_report(
    group: PurePosixPath,
    opcodes: dict[int, str],
    counts: Counter[int],
    traced: int,
    rejected: int,
) -> str:
    """Show observed and missed opcodes and any undefined bytes reached by the trace."""
    observed = opcodes.keys() & counts.keys()
    missed = opcodes.keys() - counts.keys()
    lines = [
        "# Amsterdam opcode coverage",
        "",
        f"Fixture group `{group}` from `{catalogue.EXECUTION}`.",
        f"Observed **{len(observed)} of {len(opcodes)}** defined opcodes.",
        "",
        "| Measure | Count |",
        "| --- | ---: |",
        f"| Traced cases | {traced} |",
        f"| Cases skipped for expected transaction errors | {rejected} |",
        f"| Trace steps | {counts.total()} |",
        "",
        "Counts include faulting steps and the implicit `STOP` at the end of code.",
        "The opcode table comes from EthLib's `Op.ofByte` at Amsterdam.",
        "",
        f"## Observed opcodes ({len(observed)})",
        "",
        "| Byte | Opcode | Steps |",
        "| --- | --- | ---: |",
        *(f"| `0x{byte:02x}` | `{opcodes[byte]}` | {counts[byte]} |" for byte in sorted(observed)),
        "",
        f"## Missed opcodes ({len(missed)})",
        "",
        "| Byte | Opcode |",
        "| --- | --- |",
        *(f"| `0x{byte:02x}` | `{opcodes[byte]}` |" for byte in sorted(missed)),
    ]
    if undefined := counts.keys() - opcodes.keys():
        lines.extend(("", "## Undefined bytes reached", "", "| Byte | Steps |", "| --- | ---: |"))
        lines.extend(f"| `0x{byte:02x}` | {counts[byte]} |" for byte in sorted(undefined))
    return "\n".join(lines)


def main() -> None:
    """Trace one group of Amsterdam state tests and print a Markdown report."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("group", type=PurePosixPath, help="directory of state tests in the archive")
    args = parser.parse_args()
    if archives.CACHE is None:
        parser.error("set ETHLIB_ARCHIVES to the fixture archive cache directory")

    group = args.group
    cases = [
        case
        for case in catalogue.execution_cases()
        if case.fork == "Amsterdam"
        and case.group == "state_test"
        and group in PurePosixPath(case.path).parents
    ]
    if not cases:
        parser.error(f"no Amsterdam state tests under {group}")

    opcodes = _amsterdam_opcodes()
    root = harness.unpack_read(catalogue.EXECUTION, cases)
    counts: Counter[int] = Counter()
    rejected = 0
    for case in cases:
        transaction_args, post = state_test_input(root, case)
        if "expectException" in post:
            rejected += 1
            continue
        counts.update(traced_opcodes(transactions.trace_eip3155(*transaction_args)))
    print(render_report(group, opcodes, counts, len(cases) - rejected, rejected))


if __name__ == "__main__":
    main()
