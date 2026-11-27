"""Report opcode coverage for a group of pinned Amsterdam state tests."""

# Run from bindings/python/tests, with the Lean modules built and ETHLIB_ARCHIVES set:
#     python -m parity.opcode_coverage fixtures/state_tests/for_amsterdam/amsterdam/eip7843_slotnum

import argparse
import json
import subprocess
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from pathlib import PurePosixPath

import archives
from ethlib.execution import transactions

from . import catalogue, harness
from .catalogue import Case
from .runners import state_test_input

# The Lean script that lists the opcodes, and the time it may take to load the specification.
OPCODES_SCRIPT = "scripts/AmsterdamOpcodes.lean"
OPCODES_TIMEOUT = 600


def parse_opcodes(listing: str) -> dict[int, str]:
    """Read one decimal byte, a tab and a mnemonic from each line of the Lean listing."""
    opcodes: dict[int, str] = {}
    for line in listing.splitlines():
        byte, tab, name = line.partition("\t")
        if not (tab and byte.isdecimal() and int(byte) < 256 and name):
            raise ValueError(f"not an opcode line of {OPCODES_SCRIPT}: {line!r}")
        opcodes[int(byte)] = name
    return opcodes


def _amsterdam_opcodes() -> dict[int, str]:
    """Read the opcode bytes and trace mnemonics from EthLib's Lean definitions."""
    # Lean writes its diagnostics to standard output, so a failure keeps them for the message.
    try:
        listing = subprocess.run(
            ["lake", "env", "lean", "--run", OPCODES_SCRIPT],
            cwd=archives.REPO,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=OPCODES_TIMEOUT,
        ).stdout
    except subprocess.CalledProcessError as error:
        raise RuntimeError(f"{OPCODES_SCRIPT} failed:\n{error.output}") from error
    return parse_opcodes(listing)


def select_cases(cases: Iterable[Case], group: PurePosixPath) -> list[Case]:
    """Keep the Amsterdam state tests whose fixture file lies under the group directory."""
    return [
        case
        for case in cases
        if case.fork == "Amsterdam"
        and case.group == "state_test"
        and group in PurePosixPath(case.path).parents
    ]


def traced_opcodes(trace: Sequence[str]) -> Counter[int]:
    """Count opcode bytes in the trace steps before the transaction summary."""
    return Counter(json.loads(line)["op"] for line in trace[:-1])


def render_report(
    group: PurePosixPath,
    opcodes: Mapping[int, str],
    counts: Counter[int],
    traced: int,
    rejected: int,
) -> str:
    """Render the Markdown report: counts, observed and missed opcodes, and undefined bytes."""
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
        "The table lists the opcodes that EthLib defines at Amsterdam, with their trace names.",
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
    cases = select_cases(catalogue.execution_cases(), group)
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
