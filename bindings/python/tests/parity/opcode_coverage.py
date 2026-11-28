"""Report opcode coverage, gas costs and memory growth by fork for pinned execution state tests."""

# Run from bindings/python/tests with the Python bindings built and ETHLIB_ARCHIVES set.
#     python -m parity.opcode_coverage [group]

import argparse
import json
from collections import defaultdict
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import PurePosixPath
from typing import NamedTuple, TypedDict

import archives
from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import address, sign
from ethlib.execution import transactions
from ethlib.serialization import rlp
from transactions.test_check_order import KEY, OTHER, _int
from transactions.test_transactions import CHAIN_ID, FORK_OF_NETWORK
from transactions.test_typed import ENV

from . import catalogue, harness
from .catalogue import Case
from .runners import state_test_input


@dataclass(slots=True, kw_only=True)
class OpcodeStats:
    """Observations for one opcode byte at one fork."""

    steps: int = 0
    gas_costs: set[int] = field(default_factory=set)
    memory_growth: set[int] = field(default_factory=set)
    out_of_gas: int = 0


def opcode_inventory(fork: str) -> dict[int, str]:
    """Identify the defined bytes and their mnemonics from one trace per byte."""
    # A legacy transaction with no chain ID can enter the block at any of these forks.
    fields = [b"", _int(10), _int(100_000), OTHER, b"", b""]
    signature = sign(KEY, keccak256(rlp.encode(fields)))
    r, s, parity = signature[:32], signature[32:64], signature[64]
    tx = rlp.encode(fields + [_int(27 + parity), r.lstrip(b"\0"), s.lstrip(b"\0")])
    sender = [address(KEY), b"", _int(10**18), b"", []]

    opcodes: dict[int, str] = {}
    for byte in range(256):
        state = rlp.encode([sender, [OTHER, b"", b"", bytes([byte]), []]])
        trace = transactions.trace_eip3155(fork, CHAIN_ID, tx, state, ENV)
        # A later trace step can be the implicit STOP, so take only the first step.
        if len(trace) < 2:
            raise ValueError(f"{fork} opcode probe {byte:#04x} has no trace step")
        step = json.loads(trace[0])
        if (step.get("pc"), step.get("depth"), step.get("op")) != (0, 1, byte):
            raise ValueError(f"{fork} opcode probe {byte:#04x} has an unexpected first step")
        mnemonic = step.get("opName")
        undefined = step.get("error") == "invalid opcode"
        if not isinstance(mnemonic, str) or not mnemonic or undefined != (mnemonic == "INVALID"):
            raise ValueError(f"{fork} opcode probe {byte:#04x} has an inconsistent mnemonic")
        # A defined byte can fault when the probe supplies no stack operands.
        if not undefined:
            opcodes[byte] = mnemonic
    return opcodes


def select_cases(cases: Iterable[Case], group: PurePosixPath | None) -> dict[str, list[Case]]:
    """Group the traced state tests by fork in fork order, optionally under one directory."""
    by_fork: dict[str, list[Case]] = {
        fork: [] for fork in catalogue.EXECUTION_FORKS if fork in FORK_OF_NETWORK
    }
    for case in cases:
        if (
            case.group == "state_test"
            and case.fork in by_fork
            and (group is None or group in PurePosixPath(case.path).parents)
        ):
            by_fork[case.fork].append(case)
    return {fork: matches for fork, matches in by_fork.items() if matches}


class StepFields(TypedDict):
    """The fields of every EIP-3155 trace step that the report reads."""

    op: int
    depth: int
    memSize: int
    gasCost: str


class TraceStep(StepFields, total=False):
    """A trace step, with the error of a step that faults."""

    error: str


class FrameStep(NamedTuple):
    """The last recorded step of an open call frame."""

    depth: int
    opcode: OpcodeStats
    memory_size: int


def record_trace(stats: defaultdict[int, OpcodeStats], trace: Sequence[str]) -> None:
    """Record the steps before the summary of one EIP-3155 transaction trace."""
    open_frames: list[FrameStep] = []
    for line in trace[:-1]:
        step: TraceStep = json.loads(line)
        depth = step["depth"]
        size = step["memSize"]
        # Discard finished child frames before a later call can reuse their depth.
        while open_frames and open_frames[-1].depth > depth:
            open_frames.pop()
        if open_frames and open_frames[-1].depth == depth:
            previous = open_frames.pop()
            # The snapshot is taken before the step (EIP-3155, Output).
            previous.opcode.memory_growth.add(size - previous.memory_size)

        opcode = stats[step["op"]]
        opcode.steps += 1
        error = step.get("error")
        # A faulting step reports the gas its frame had left, not a price.
        if error is None:
            opcode.gas_costs.add(int(step["gasCost"], 16))
        elif error == "out of gas":
            opcode.out_of_gas += 1
        open_frames.append(FrameStep(depth, opcode, size))


STATS_COLUMNS = "Steps | Gas costs | Memory growth (bytes) | Out of gas |"
STATS_ALIGNMENT = "---: | ---: | ---: | ---: |"


def render_stats(opcode: OpcodeStats) -> str:
    """Render the observations for a byte that the trace reached."""
    gas = ", ".join(map(str, sorted(opcode.gas_costs))) or "-"
    growth = ", ".join(map(str, sorted(opcode.memory_growth))) or "-"
    return f"{opcode.steps} | {gas} | {growth} | {opcode.out_of_gas} |"


def render_fork(
    network: str,
    opcodes: Mapping[int, str],
    stats: Mapping[int, OpcodeStats],
    *,
    traced: int,
    rejected: int,
) -> str:
    """Render the observations and the missed and undefined bytes for one fork."""
    observed = opcodes.keys() & stats.keys()
    missed = opcodes.keys() - stats.keys()
    lines = [
        f"## {network}",
        "",
        f"Observed **{len(observed)} of {len(opcodes)}** defined opcodes.",
        "",
        "| Measure | Count |",
        "| --- | ---: |",
        f"| Traced cases | {traced} |",
        f"| Cases skipped for expected transaction errors | {rejected} |",
        f"| Trace steps | {sum(opcode.steps for opcode in stats.values())} |",
        "",
        f"### Observed opcodes ({len(observed)})",
        "",
        f"| Byte | Opcode | {STATS_COLUMNS}",
        f"| --- | --- | {STATS_ALIGNMENT}",
        *(
            f"| `0x{byte:02x}` | `{opcodes[byte]}` | {render_stats(stats[byte])}"
            for byte in sorted(observed)
        ),
        "",
        f"### Missed opcodes ({len(missed)})",
        "",
        "| Byte | Opcode |",
        "| --- | --- |",
        *(f"| `0x{byte:02x}` | `{opcodes[byte]}` |" for byte in sorted(missed)),
    ]
    if undefined := stats.keys() - opcodes.keys():
        lines.extend(
            (
                "",
                "### Undefined bytes reached",
                "",
                f"| Byte | {STATS_COLUMNS}",
                f"| --- | {STATS_ALIGNMENT}",
            )
        )
        lines.extend(
            f"| `0x{byte:02x}` | {render_stats(stats[byte])}" for byte in sorted(undefined)
        )
    return "\n".join(lines)


def main() -> None:
    """Trace the pinned state tests and print one coverage section for each selected fork."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("group", nargs="?", type=PurePosixPath, help="directory in the archive")
    args = parser.parse_args()
    if archives.CACHE is None:
        parser.error("set ETHLIB_ARCHIVES to the fixture archive cache directory")

    group: PurePosixPath | None = args.group
    by_fork = select_cases(catalogue.execution_cases(), group)
    if not by_fork:
        parser.error(f"no state tests under {group}" if group is not None else "no state tests")
    root = harness.unpack_read(
        catalogue.EXECUTION, [case for cases in by_fork.values() for case in cases]
    )
    source = (
        f"Fixture group `{group}` from `{catalogue.EXECUTION}`."
        if group is not None
        else f"State tests from `{catalogue.EXECUTION}`."
    )
    sections = [
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
    for network, cases in by_fork.items():
        opcodes = opcode_inventory(FORK_OF_NETWORK[network])
        stats: defaultdict[int, OpcodeStats] = defaultdict(OpcodeStats)
        rejected = 0
        for case in cases:
            transaction_args, post = state_test_input(root, case)
            if "expectException" in post:
                rejected += 1
                continue
            record_trace(stats, transactions.trace_eip3155(*transaction_args))
        sections.append(
            render_fork(network, opcodes, stats, traced=len(cases) - rejected, rejected=rejected)
        )
    print("\n\n".join(sections))


if __name__ == "__main__":
    main()
